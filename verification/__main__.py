#!/usr/bin/env python3
"""Recompute the manuscript's finite arithmetic with Python's standard library.

Run from the repository root: python3 -m verification
Reports are written to evidence/. This is not a verification of the whole
geometric theorem. Do not run with -O: some existing checkers use assertions.
"""
from datetime import datetime, timezone
from hashlib import sha256
import gzip
import json
from pathlib import Path
import subprocess
import sys
import time

from .paths import ROOT, CERTIFICATES, EVIDENCE
CHECKS = Path(__file__).resolve().parent
COSTS = (
    ('mathematical-certificate-data.json', 'printed-cost-certificates.json'),
    ('extended-certificate-data.json', 'extended-cost-checks.json'),
    ('quad-certificate-data.json', 'quad-cost-checks.json'),
    ('weighted20-certificate-data.json', 'weighted20-cost-checks.json'),
    ('low18-certificate-data.json', 'low18-cost-checks.json'),
    ('positive-certificate-data.json', 'positive-cost-checks.json'),
)
PROGRAMS = (
    ('verify_mathematics.py', 'mathematics-check.json'),
    ('check_coverage.py', 'endpoint-coverage.json'),
    ('check_extended_coverage.py', 'extended-coverage.json'),
    ('check_ridge_counts.py', 'ridge-count-checks.json'),
    ('check_one_pair.py', 'one-pair-checks.json'),
    ('check_two_pair_zero.py', 'two-pair-zero-checks.json'),
    ('check_positive_profiles.py', 'positive-profile-checks.json'),
    ('check_positive_geometry.py', 'positive-geometry-checks.json'),
    ('check_signed_carriers.py', 'signed-carrier-checks.json'),
    ('check_interval_sections.py', 'interval-section-checks.json'),
)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def save(name, data):
    target = EVIDENCE / name
    temporary = target.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(target)


def require_passed(data):
    if data.get('status') == 'passed':
        return
    # Coverage programs report a status for each endpoint group.
    if not data or any(not isinstance(v, dict) or v.get('status') != 'passed'
                       for v in data.values()):
        raise ValueError('Check did not report success')


def main():
    if not __debug__:
        raise RuntimeError('Run Python without -O or PYTHONOPTIMIZE')
    EVIDENCE.mkdir(exist_ok=True)
    inputs = sorted({CERTIFICATES / f for f, _ in COSTS} |
                    set(CERTIFICATES.glob('cube-*-certificates.json.gz')) |
                    set(CHECKS.glob('*.py')))
    hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in inputs}
    steps = []
    started = time.monotonic()

    from .certificate_checks import verify_leaf
    count = 0
    for source, report in COSTS:
        print('Checking ' + source, flush=True)
        tick = time.monotonic()
        leaves = json.loads((CERTIFICATES / source).read_text())['leaves']
        proofs = [verify_leaf(leaf) for leaf in leaves]
        save(report, {'status': 'passed', 'whole_theorem_verified': False,
                      'scope': 'Local row costs and global linear contradictions',
                      'certificates': proofs})
        count += len(proofs)
        steps.append({'check': 'certificates/' + source, 'report': report,
                      'certificates': len(proofs),
                      'seconds': round(time.monotonic() - tick, 3)})
        print('Passed: ' + str(len(proofs)) + ' exact cost certificates', flush=True)

    print('Checking all cube-lift integer identities and sign trees', flush=True)
    tick = time.monotonic()
    from .check_cube_certificates import sign_cube, reduction, family_check
    cubes = {'status': 'passed', 'whole_theorem_verified': False,
             'five_full_normals': sign_cube()}
    for m in (7, 8):
        data = json.loads(gzip.decompress(
            (CERTIFICATES / f'cube-{2*m}-certificates.json.gz').read_bytes()))
        cubes[f'{2*m}_vertices'] = {
            'reduction': reduction(data),
            'families': [family_check(f['F'], m) for f in data['families']]}
        print(f'Passed: {2*m}-vertex cube-lift certificates', flush=True)
    save('cube-lift-checks.json', cubes)
    steps.append({'check': 'cube-lift integer certificates',
                  'report': 'cube-lift-checks.json',
                  'seconds': round(time.monotonic() - tick, 3)})

    # Ordering regenerates the profile reports before their dependent searches.
    for program, report in PROGRAMS:
        print('Checking ' + program, flush=True)
        tick = time.monotonic()
        result = subprocess.run([sys.executable, '-B', '-m',
                                 'verification.' + Path(program).stem],
                                cwd=ROOT, capture_output=True, text=True)
        if result.returncode:
            raise RuntimeError(program + ' failed:\n' + result.stderr)
        data = json.loads(result.stdout)
        require_passed(data)
        save(report, data)
        steps.append({'check': 'verification/' + program, 'report': report,
                      'seconds': round(time.monotonic() - tick, 3)})
        print('Passed: ' + program, flush=True)

    if hashes != {p.relative_to(ROOT).as_posix(): digest(p) for p in inputs}:
        raise RuntimeError('Inputs changed during the checks')
    save('finite-checks.json', {
        'status': 'passed', 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'whole_theorem_verified': False, 'exact_cost_certificates': count,
        'seconds': round(time.monotonic() - started, 3), 'steps': steps,
        'input_sha256': hashes,
        'report_sha256': {s['report']: digest(EVIDENCE / s['report']) for s in steps},
        'limits': [
            'Geometric lemmas and rigidity are mathematical inputs, not checked here.',
            'Continuous cube-lift coverage uses the manuscript normalization and sign-tree proof.',
            'Balanced-section checks test rational cell representatives; the cell boundaries are proved in the manuscript.',
            'This result is not an independent mathematical audit of the whole manuscript.',
        ],
    })
    print(f'All finite checks passed ({count} exact cost certificates). '
          'Whole geometric theorem: not verified by this program.', flush=True)


if __name__ == '__main__':
    main()
