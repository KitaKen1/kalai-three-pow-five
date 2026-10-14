#!/usr/bin/env python3
"""Archive one successful CI attempt, original artifact ZIPs, logs and metadata."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import urllib.request
import urllib.error
import zipfile


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def extract(source, destination):
    with zipfile.ZipFile(source) as archive:
        require(archive.testzip() is None, 'Invalid artifact ZIP checksum')
        for entry in archive.infolist():
            require((destination / entry.filename).resolve().is_relative_to(destination.resolve()),
                    'Unsafe ZIP path')
            require((entry.external_attr >> 16) & 0o170000 != 0o120000, 'ZIP contains a symlink')
        archive.extractall(destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True)
    parser.add_argument('--run', required=True, type=int)
    parser.add_argument('--attempt', required=True, type=int)
    parser.add_argument('--expected-commit', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--public-success-only', action='store_true')
    args = parser.parse_args()
    require(re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', args.repo), 'Invalid repository')
    require(re.fullmatch(r'[0-9a-f]{40}', args.expected_commit), 'Expected commit must be a full SHA')
    require(not args.output.exists(), 'Choose a new archive directory')
    token = os.environ.get('GH_TOKEN')
    if not token:
        credential = subprocess.run(['git', 'credential', 'fill'],
            input='protocol=https\nhost=github.com\npath=' + args.repo + '.git\n\n',
            text=True, capture_output=True, check=True)
        values = dict(line.split('=', 1) for line in credential.stdout.splitlines() if '=' in line)
        token = values['password']
    headers = {'Authorization': 'Bearer ' + token, 'Accept': 'application/vnd.github+json',
               'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'Kalai-CI-Archive'}

    class NoRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, *args, **kwargs):
            return None

    def get(endpoint):
        request = urllib.request.Request('https://api.github.com/repos/' + args.repo + endpoint, headers=headers)
        try:
            with urllib.request.build_opener(NoRedirect).open(request, timeout=45) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            if error.code != 302:
                raise
            # Do not forward the GitHub credential to the signed storage URL.
            request = urllib.request.Request(error.headers['Location'], headers={'User-Agent': headers['User-Agent']})
            with urllib.request.urlopen(request, timeout=45) as response:
                return response.read()

    attempt_path = f'/actions/runs/{args.run}/attempts/{args.attempt}'
    run_raw = get(attempt_path)
    run = json.loads(run_raw)
    require(run['status'] == 'completed' and run['conclusion'] == 'success', 'CI attempt did not succeed')
    require(run['head_sha'] == args.expected_commit, 'CI tested commit differs')
    repository_raw = get('')
    repository = json.loads(repository_raw)
    if args.public_success_only:
        require(not repository['private'] and run['head_branch'] == 'main', 'Require successful public main CI')
    jobs_raw = get(attempt_path + '/jobs?per_page=100')
    artifacts_raw = get(f'/actions/runs/{args.run}/artifacts?per_page=100')
    jobs = json.loads(jobs_raw)
    artifacts = json.loads(artifacts_raw)
    require(jobs['total_count'] <= 100 and artifacts['total_count'] <= 100, 'Pagination required; refusing partial archive')
    for name in ['build', 'comparator', 'replay', 'arithmetic', 'verification_status']:
        matching = [job for job in jobs['jobs'] if job['name'] == name]
        require(len(matching) == 1 and matching[0]['conclusion'] == 'success', 'Missing successful job: ' + name)
    expected_names = {f'{name}-{args.run}-{args.attempt}' for name in ['build', 'comparator', 'replay', 'arithmetic']}
    chosen = [a for a in artifacts['artifacts'] if a['name'] in expected_names]
    require({a['name'] for a in chosen} == expected_names and len(chosen) == 4, 'Missing attempt-specific artifacts')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix='.kalai-archive-', dir=args.output.parent))

    def save(name, content):
        target = temporary / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)

    try:
        save('github/attempt.json', run_raw)
        save('github/repository.json', repository_raw)
        save('github/jobs.json', jobs_raw)
        save('github/artifacts.json', artifacts_raw)
        records = []
        for artifact in chosen:
            require(not artifact['expired'], 'Artifact expired: ' + artifact['name'])
            data = get(f'/actions/artifacts/{artifact["id"]}/zip')
            digest = hashlib.sha256(data).hexdigest()
            require(artifact.get('digest') == 'sha256:' + digest, 'GitHub artifact digest differs or is absent')
            name = f'artifacts/{artifact["id"]}-{artifact["name"]}.zip'
            save(name, data)
            extract(temporary / name, temporary / 'receipt' / artifact['name'])
            records.append({'id': artifact['id'], 'name': artifact['name'], 'file': name,
                            'sha256': digest, 'github_digest': artifact['digest'], 'digest_matches': True})
        save('github/workflow-logs.zip', get(attempt_path + '/logs'))
        extract(temporary / 'github/workflow-logs.zip', temporary / 'github/logs')
        for job in jobs['jobs']:
            save(f'github/job-{job["id"]}.log', get(f'/actions/jobs/{job["id"]}/logs'))

        receipts = {name: temporary / 'receipt' / f'{name}-{args.run}-{args.attempt}'
                    for name in ['build', 'comparator', 'replay', 'arithmetic']}
        for name, receipt in receipts.items():
            require((receipt / 'status.txt').read_text() == 'PASS\n', 'Receipt not PASS: ' + name)
        inputs = json.loads((receipts['comparator'] / 'input-check.json').read_text())
        require(inputs['tested_commit'] == args.expected_commit and inputs['input_check'] == 'passed', 'Input receipt differs')
        pins = inputs['pins']
        require(pins['targets'] == ['Kalai.three_pow_five'], 'Wrong comparison target')
        require(pins['lean_toolchain'] == 'leanprover/lean4:v4.33.1', 'Wrong FC proof toolchain')
        require(pins['mathlib_commit'] == '0df444a360eaa60ab8c11dca51a86af692955474', 'Wrong FC Mathlib')
        require(re.fullmatch(r'[0-9a-f]{64}', pins['proof_source_map_sha256']), 'Missing proof source hash')
        for name, receipt in receipts.items():
            if name != 'replay':
                other = json.loads((receipt / 'input-check.json').read_text())
                require(other['tested_commit'] == args.expected_commit and
                        other['publication_manifest_sha256'] == inputs['publication_manifest_sha256'] and
                        other['pins'] == pins, 'Receipt inputs differ: ' + name)
        environment = json.loads((receipts['comparator'] / 'checker-environment.json').read_text())
        require(environment['status'] == 'PASS' and environment['required_version'] == '4.33.1', 'Wrong checker environment')
        require(environment['source_changes'] == {'comparator': ['lean-toolchain'],
                'lean4export': ['lean-toolchain'], 'landrun': []}, 'Unexpected checker source changes')
        require(set(environment['compiler_versions']) == {'proof', 'comparator', 'lean4export'}, 'Missing compiler records')
        require(all('version 4.33.1,' in v for v in environment['compiler_versions'].values()), 'Compiler versions differ')
        log = (receipts['comparator'] / 'comparator.log').read_text()
        for message in ['Lean default kernel accepts the solution', 'Your solution is okay!']:
            require(message in log, 'Missing Comparator acceptance')
        audit = json.loads((receipts['comparator'] / 'axioms.json').read_text())
        require(audit['status'] == 'PASS' and not audit['sorryAx'] and not audit['new_axioms'], 'Invalid axiom receipt')
        require(set(audit['targets']) == {'Kalai.three_pow_five', 'Kalai5.kalai_three_pow_five'}, 'Missing theorem audit')
        require(all(set(v) == {'propext', 'Classical.choice', 'Quot.sound'} for v in audit['targets'].values()), 'Unexpected axioms')
        progress = json.loads((receipts['build'] / 'source-build.json').read_text())
        require(progress['status'] == 'PASS' and progress['complete_target_build'] and
                progress['target'] == 'FCSolution' and progress['lean_toolchain'] == pins['lean_toolchain'] and
                progress['proof_source_map_sha256'] == pins['proof_source_map_sha256'],
                'Incomplete FC target build')
        require(progress.get('method') == 'explicit proof declarations, ordinary kernel replay'
                and progress.get('native_decide') is False
                and progress.get('archive_sha256') == pins['fast_archive_sha256']
                and progress.get('archive_declarations') == pins['fast_archive_declarations'],
                'Wrong FC archive build receipt')
        archive_replay = json.loads((receipts['build'] / 'archive-replay.json').read_text())
        require(archive_replay['status'] == 'PASS' and archive_replay['archive_completed']
                and archive_replay['archive_sha256'] == pins['fast_archive_sha256']
                and archive_replay['declarations'] == pins['fast_archive_declarations']
                and archive_replay['native_decide'] is False
                and set(archive_replay['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'},
                'Incomplete or mismatched complete archive replay')
        require('Exit status: 0' in (receipts['replay'] / 'time.log').read_text(), 'Fresh kernel replay did not succeed')
        finite = json.loads((receipts['arithmetic'] / 'finite-checks.json').read_text())
        require(finite['status'] == 'passed' and finite['exact_cost_certificates'] == 742 and len(finite['steps']) == 17,
                'Incomplete finite arithmetic checks')
        provenance = {'repository': args.repo, 'run_id': args.run, 'run_attempt': args.attempt,
                      'tested_commit': args.expected_commit, 'run_url': run['html_url'],
                      'conclusion': run['conclusion'], 'proof_source_map_sha256': pins['proof_source_map_sha256'],
                      'publication_manifest_sha256': inputs['publication_manifest_sha256'],
                      'artifacts': records, 'retrieved_at_utc': datetime.now(timezone.utc).isoformat(),
                      'note': 'Original ZIPs, GitHub digests, metadata and logs retained. Local hashes are not a signed GitHub attestation.'}
        save('provenance.json', (json.dumps(provenance, indent=2) + '\n').encode())
        paths = sorted(p for p in temporary.rglob('*') if p.is_file())
        save('SHA256SUMS', ''.join(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(temporary).as_posix() + '\n'
                                 for p in paths).encode())
        temporary.rename(args.output)
        print('Archived successful CI attempt to ' + str(args.output))
    finally:
        if temporary.exists():
            shutil.rmtree(temporary)


if __name__ == '__main__':
    main()
