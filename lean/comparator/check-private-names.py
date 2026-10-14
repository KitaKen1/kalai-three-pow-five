#!/usr/bin/env python3
"""Exercise the actual archive decoder on two colliding source-private names.

The fixture defines the two constants with distinct values (1 and 2), then
kernel-checks a theorem referring to both. No full Kalai replay is run here.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', required=True, type=Path)
    parser.add_argument('--lean', help='Optional compiler path; default: lake env lean')
    args = parser.parse_args()
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    archive = (ROOT / 'lean/KalaiFast.lean').read_text()
    header, separator, _ = archive.partition('kalai_replay_group% {\n')
    if not separator:
        raise RuntimeError('Missing archive group')
    # This fixture only uses Lean's core Nat, Eq and And, so Mathlib imports
    # are unnecessary. All decoding and kernel-checking code is unchanged.
    header = re.sub(r'^import .+\n', '', header, flags=re.M)
    fixtures = ROOT / 'lean/comparator/fixtures'
    source = ('import Lean\n' + header + 'kalai_replay_group% {\n'
              + (fixtures / 'private-names.block').read_text() + '}\n'
              + '#print axioms KalaiPrivateFixture.target\n'
              + (fixtures / 'private-names-checks.lean').read_text())
    with tempfile.TemporaryDirectory(prefix='kalai-private-names-') as directory:
        path = Path(directory) / 'PrivateNames.lean'
        path.write_text(source)
        command = [args.lean] if args.lean else ['lake', 'env', 'lean']
        result = subprocess.run(command + ['-Ddebug.skipKernelTC=false', '-DElab.async=false', str(path)],
                                cwd=ROOT / 'lean', capture_output=True, text=True, timeout=120)
    log = result.stdout + result.stderr
    (args.receipt_dir / 'private-names.log').write_text(log)
    if (result.returncode != 0 or re.search(r'\berror:|\bPANIC\b|sorryAx|ofReduceBool', log)
            or log.count('PRIVATE_NAME_FIXTURE_PASS') != 1
            or "'KalaiPrivateFixture.target' does not depend on any axioms" not in log):
        raise RuntimeError('Private-name regression failed; inspect private-names.log')
    receipt = {'status': 'PASS', 'declarations': 3, 'axioms': [],
               'archive_sha256': hashlib.sha256(archive.encode()).hexdigest(),
               'fixture_sha256': hashlib.sha256(source.encode()).hexdigest(),
               'checks': ['distinct source modules retain distinct names and values',
                          'references resolve to both renamed declarations',
                          'imported private names unchanged'],
               'full_archive_replayed': False}
    (args.receipt_dir / 'private-names.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('PASS: three-declaration private-name regression; no full archive replay')


if __name__ == '__main__':
    main()
