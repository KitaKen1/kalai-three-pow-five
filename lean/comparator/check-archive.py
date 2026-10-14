#!/usr/bin/env python3
"""Check FC archive packaging, or audit an actual complete kernel replay."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BLOCK = re.compile(r'^kalai_deflated_block% (\d+) (\d+): "([A-Za-z0-9+/=]*)"$', re.M)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def signature(text):
    start = text.index('theorem three_pow_five\n')
    return text[start:text.index(' := by', start)]


def source():
    path = ROOT / 'lean/KalaiFast.lean'
    text = path.read_text()
    meta = json.loads((ROOT / 'lean/fast-manifest.json').read_text())
    pins = json.loads((ROOT / 'lean/comparator/pins.json').read_text())
    require(digest(path) == meta['sha256'] and path.stat().st_size == meta['bytes'],
            'Archive differs from its manifest')
    require(meta['lean'] == pins['lean_toolchain'] == 'leanprover/lean4:v4.33.1'
            and meta['mathlib'] == pins['mathlib_commit'] ==
            '0df444a360eaa60ab8c11dca51a86af692955474', 'Wrong FC environment')
    require(meta['target'] == 'Kalai.three_pow_five' and meta['FC_port'] is True,
            'Wrong archive target or port')
    require(meta['native_decide'] is False and meta['kernel_checking'] ==
            'forced on for each declaration', 'Wrong verification policy')
    require(meta['visible_public_theorem'] is True and meta['public_bridge_declarations'] == 1
            and meta['omitted_encoded_public_bridge'] is True, 'Missing public bridge')
    require(signature(text) == signature((ROOT / 'lean/Kalai5/FormalConjectures.lean').read_text()),
            'Public theorem signature differs')
    require(text.count('\nnamespace Kalai\n') == 1 and
            text.rstrip().endswith('#print axioms Kalai.three_pow_five'),
            'Missing final named theorem or axiom audit')
    require(re.findall(r'^import (\S+)$', text, re.M) == pins['mathlib_imports'],
            'Archive must import only pinned Mathlib modules')
    require(not re.search(r'\bnative_decide\b|^\s*(?:axiom|sorry|admit)\b|skipKernelTC[^\n]*\btrue\b',
                          text, re.M), 'Hole, native reduction or skipped kernel check')
    require('Lean.Elab.async.set (debug.skipKernelTC.set opts false) false' in text,
            'Missing forced kernel checking')
    blocks = list(BLOCK.finditer(text))
    require(len(blocks) == len(meta['blocks']) and len(blocks) > 0, 'Wrong archive block count')
    total = 0
    for match, expected in zip(blocks, meta['blocks']):
        require(int(match[1]) == expected['count'] and int(match[2]) == expected['raw_bytes'],
                'Block declaration count or decoded length differs')
        total += int(match[1])
        require(total == expected['cumulative'], 'Invalid cumulative declaration count')
    require(total == meta['declarations'], 'Incomplete archive')
    require(hashlib.sha256(text[:blocks[0].start()].encode()).hexdigest() ==
            meta['embedded_support_sha256'], 'Decoder or archive header differs')
    require(meta['source_proof_objects_unchanged'] is True and
            meta['input_pool_boundaries_preserved'] is True and
            meta['encoded_proof_blocks_identical'] is True, 'Missing transport round-trip checks')
    require([int(n) for n in re.findall(r'#eval IO.eprintln "KALAI_REPLAY_DONE (\d+)"', text)] ==
            [b['cumulative'] for b in meta['blocks']], 'Source completion markers differ')
    require((ROOT / 'lean4web/Kalai.lean').read_bytes() == path.read_bytes(),
            'Browser file differs from CI proof')
    return meta


def audit_log(meta, text):
    require(not re.search(r'\berror:|\bPANIC\b|sorryAx|ofReduceBool|declaration uses [\x27`]?sorry', text),
            'Error or unfinished/native proof in replay log')
    # Lake may prefix an informational message with the source location.
    markers = re.findall(r'\bKALAI_REPLAY_DONE (\d+)\b', text)
    require(markers == [str(b['cumulative']) for b in meta['blocks']],
            'Missing, duplicated or out-of-order replay completion markers')
    target = 'Kalai.three_pow_five'
    reports = re.findall("'" + re.escape(target) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
    require(len(reports) == 1, 'Missing or duplicated final theorem axiom report')
    names = [s.strip() for s in reports[0].split(',') if s.strip()]
    require(len(names) == len(set(names)) and set(names) == ALLOWED,
            'Unexpected final theorem axioms: ' + str(names))
    return {'status': 'PASS', 'target': target, 'archive_completed': True,
            'declarations': meta['declarations'], 'archive_sha256': meta['sha256'],
            'lean_toolchain': meta['lean'], 'mathlib_commit': meta['mathlib'],
            'axioms': sorted(names), 'native_decide': False, 'kernel_checking': 'forced on'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['source', 'audit'])
    parser.add_argument('log', nargs='?', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    meta = source()
    if args.mode == 'audit':
        if args.log is None:
            parser.error('audit requires an actual Lean replay log')
        result = audit_log(meta, args.log.read_text())
    else:
        result = {'source_check': 'PASS', 'archive_sha256': meta['sha256'],
                  'declarations': meta['declarations'], 'proof_checked_by_this_command': False}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
