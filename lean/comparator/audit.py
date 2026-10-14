#!/usr/bin/env python3
"""Require actual final theorem axiom reports and reject incomplete proofs."""
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def axioms(text, targets):
    if re.search(r'\berror:|\bPANIC\b|sorryAx|declaration uses [\x27`]?sorry', text):
        raise RuntimeError('Error or unfinished proof in verification output')
    records = {}
    for target in targets:
        found = re.findall("'" + re.escape(target) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
        if len(found) != 1:
            raise RuntimeError('Missing or duplicated axiom report: ' + target)
        names = [s.strip() for s in found[0].split(',') if s.strip()]
        if len(names) != len(set(names)) or set(names) != ALLOWED:
            raise RuntimeError('Unexpected final axioms: ' + target + ': ' + str(names))
        records[target] = sorted(names)
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['axioms'])
    parser.add_argument('log', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    text = args.log.read_text()
    result = {'status': 'PASS', 'targets': axioms(text, ['Kalai.three_pow_five',
                                                        'Kalai5.kalai_three_pow_five']),
              'sorryAx': False, 'new_axioms': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
