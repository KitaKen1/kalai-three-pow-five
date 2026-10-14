#!/usr/bin/env python3
"""Validate the publication sources and pins; this does not check a Lean proof."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
IGNORED_DIRS = {'.git', '.lake', '__pycache__', 'local-tools', 'build-receipt',
                'comparator-receipt', 'replay-receipt', 'math-receipt'}
GENERATED = {'PUBLICATION-MANIFEST.json', 'verification/local-package-check.json'}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def signature(text):
    start = text.index('theorem three_pow_five\n')
    return text[start:text.index(' := by', start)]


def tracked_inputs():
    result = set()
    for path in ROOT.rglob('*'):
        relative = path.relative_to(ROOT)
        if any(part in IGNORED_DIRS for part in relative.parts):
            continue
        if path.name == '.DS_Store' or path.suffix in {'.pyc', '.pyo'}:
            continue
        if path.name.endswith('.json.tmp'):
            continue
        require(not path.is_symlink(), 'Unexpected symlink: ' + str(relative))
        if path.is_file() and relative.as_posix() not in GENERATED:
            result.add(relative.as_posix())
    return result


def check():
    pins = json.loads((ROOT / 'lean/comparator/pins.json').read_text())
    manifest = json.loads((ROOT / 'PUBLICATION-MANIFEST.json').read_text())
    hashes = manifest['files_sha256']
    require(set(hashes) == tracked_inputs(), 'Publication file inventory differs')
    for name, expected in hashes.items():
        path = Path(name)
        require(not path.is_absolute() and '..' not in path.parts, 'Unsafe manifest path')
        require(digest(ROOT / path) == expected, 'Publication file changed: ' + name)
    for name, expected in pins['files_sha256'].items():
        require(digest(ROOT / name) == expected, 'Pinned checker input changed: ' + name)

    require(pins['lean_toolchain'] == pins['fc_upstream_toolchain'] ==
            'leanprover/lean4:v4.33.1', 'Unexpected FC Lean pin')
    require(pins['mathlib_commit'] == '0df444a360eaa60ab8c11dca51a86af692955474',
            'Unexpected FC Mathlib pin')
    for folder in ['lean', 'leanWithoutComparator', 'lean4web', 'FClikelean']:
        require((ROOT / folder / 'lean-toolchain').read_text().strip() == pins['lean_toolchain'],
                'Toolchain differs: ' + folder)
        deps = json.loads((ROOT / folder / 'lake-manifest.json').read_text())['packages']
        require(next(p['rev'] for p in deps if p['name'] == 'mathlib') == pins['mathlib_commit'],
                'Mathlib differs: ' + folder)
    for folder in ['lean', 'leanWithoutComparator']:
        lakefile = (ROOT / folder / 'lakefile.toml').read_text()
        for option in ['debug.skipKernelTC', 'Elab.async']:
            require(re.search(r'^' + re.escape(option) + r'\s*=\s*false\s*$', lakefile, re.M),
                    'Use an unquoted dotted Lake option set to false: ' + folder + ': ' + option)
    for name in ['comparator', 'lean4export']:
        require(pins['toolchain_patches'][name] == {
            'upstream': 'leanprover/lean4:v4.33.0', 'build': pins['lean_toolchain'],
            'changed_files': ['lean-toolchain']}, 'Unexpected checker patch: ' + name)
    config = json.loads((ROOT / 'lean/comparator.json').read_text())
    require(config['challenge_module'] == 'Challenge' and config['solution_module'] == 'FCSolution',
            'Wrong Comparator modules')
    require(config['theorem_names'] == pins['targets'] == ['Kalai.three_pow_five'], 'Wrong targets')
    require(set(config['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'},
            'Wrong permitted axioms')
    require(config['enable_nanoda'] is False, 'Unexpected external-kernel configuration')

    original = ROOT / 'leanWithoutComparator'
    source_manifest = json.loads((original / 'verification/source-manifest.json').read_text())
    require(len(source_manifest['files']) == source_manifest['original_modules'] == 976,
            'Original module count differs')
    source_map_path = ROOT / 'lean/comparator/proof-source-map.json'
    require(digest(source_map_path) == pins['proof_source_map_sha256'], 'Proof source map differs')
    source_map = json.loads(source_map_path.read_text())
    require(source_map['original_modules'] == 976 and len(source_map['files']) == 976,
            'Proof source map count differs')
    baseline = {item['path']: item['sha256'] for item in source_manifest['files']}
    require(set(baseline) == {item['path'] for item in source_map['files']}, 'Source inventory differs')
    for item in source_map['files']:
        name = item['path']
        require(item['original_sha256'] == baseline[name], 'Baseline hash differs: ' + name)
        for folder in [ROOT / 'lean', original]:
            require(digest(folder / name) == item['sha256'], 'Proof module changed: ' + name)
        text = (ROOT / 'lean' / name).read_text()
        body = re.sub(r'^import .*\n', '', text, flags=re.M).strip()
        require(hashlib.sha256(body.encode()).hexdigest() == item['body_sha256'],
                'Proof body differs: ' + name)
        require(not re.search(r'^\s*import Challenge\b|^\s*(?:sorry|admit|axiom)\b|\bnative_decide\b',
                              body, re.M), 'Hole or native dependency: ' + name)
    require(sum(item['imports_changed'] for item in source_map['files']) == 5,
            'Unexpected import migration')
    require(sorted(item['path'] for item in source_map['files'] if item['body_changed']) ==
            pins['body_compatibility_edits'] == ['Kalai5/Cube3/AlignedSupportBonus.lean', 'Kalai5/Cube3/AlignedTriangle.lean', 'Kalai5/Cube3/AllSharedTriangle.lean', 'Kalai5/Cube3/CentralVertices.lean', 'Kalai5/Cube3/EqualTriangleWidths.lean', 'Kalai5/Cube3/NoFive.lean', 'Kalai5/Cube3/NoTriangles.lean', 'Kalai5/Cube3/OpposedTriangle.lean', 'Kalai5/Cube3/PolarGeometry.lean', 'Kalai5/Cube3/PolygonSegmentSlice.lean', 'Kalai5/Cube3/RayVertices.lean', 'Kalai5/Cube3/SharedTriangleCount.lean', 'Kalai5/Cube3/SingletonCount.lean', 'Kalai5/Cube3/SliceEdges.lean', 'Kalai5/Cube3/ThirdTriangleSupport.lean', 'Kalai5/Cube3/TranslatedOffNormal.lean', 'Kalai5/Cube3/TranslatedTriangleFrame.lean', 'Kalai5/Cube3/TriangleCount.lean', 'Kalai5/Cube3/TriangleInterpolation.lean', 'Kalai5/Cube3/TriangleNormals.lean', 'Kalai5/Cube3/TriangleReferenceBonus.lean', 'Kalai5/Cube3/TriangleSegmentSlice.lean', 'Kalai5/Cube3/TriangleSegments.lean', 'Kalai5/Cube3/TriangleSegmentsBonus.lean', 'Kalai5/Cube3/TriangleSliceVertices.lean', 'Kalai5/Cube3/TriangleSupportIntervals.lean', 'Kalai5/Cube3/TriangleVertices.lean', 'Kalai5/Cube3/TwoWidthConstruction.lean', 'Kalai5/Cube3/UnequalSupportBonus.lean', 'Kalai5/Cube3/UniqueSharedTriangle.lean', 'Kalai5/Endpoints/CContextSupport.lean', 'Kalai5/Endpoints/NegativeGapCapacity.lean', 'Kalai5/Endpoints/OnePairClosure.lean', 'Kalai5/Endpoints/PairBudgetParity.lean', 'Kalai5/Endpoints/PrismBudget.lean', 'Kalai5/Endpoints/QFourPairBudget.lean', 'Kalai5/Endpoints/SinglePairBudget.lean', 'Kalai5/Endpoints/SinglePairSupport.lean', 'Kalai5/Endpoints/TwoPairZeroClosure.lean', 'Kalai5/Gale/ProfileCount.lean', 'Kalai5/LemmaB/Assemble.lean', 'Kalai5/LemmaB/Classes.lean', 'Kalai5/Small/CubeFaces.lean'],
            'Unexpected body compatibility edits')
    web_map = json.loads((ROOT / 'lean4web/source-map.json').read_text())
    require(digest(ROOT / 'lean4web/Kalai.lean') == web_map['sha256'], 'Single-file source differs')
    require(web_map['lean'] == pins['lean_toolchain'] and web_map['mathlib'] == pins['mathlib_commit'],
            'Single-file environment differs')
    require((ROOT / 'lean/Kalai5/FormalConjectures.lean').read_bytes() ==
            (original / 'Kalai5/FormalConjectures.lean').read_bytes(), 'Public bridge differs')
    expected = signature((original / 'Kalai5/FormalConjectures.lean').read_text())
    for name in ['lean/Kalai5/FormalConjectures.lean', 'lean/Challenge.lean',
                 'FClikelean/Kalai.lean', 'lean4web/Kalai.lean']:
        require(signature((ROOT / name).read_text()) == expected, 'Public signature differs: ' + name)
    challenge = (ROOT / 'lean/Challenge.lean').read_text()
    require(re.findall(r'^import (\S+)$', challenge, re.M) == pins['challenge_imports'],
            'Challenge must depend only on pinned Mathlib')
    require(len(re.findall(r'^theorem ', challenge, re.M)) == 1 and challenge.count('  sorry\n') == 1,
            'Unexpected reference placeholders')
    for name in ['lean/FCSolution.lean', 'lean/Kalai5/FormalConjectures.lean']:
        source = (ROOT / name).read_text()
        require(not re.search(r'^\s*import Challenge\b', source, re.M), 'Solution imports reference')
        require(not re.search(r'^\s*(?:sorry|admit|axiom)\b', source, re.M), 'Hole in solution: ' + name)
    require(re.findall(r'^import (\S+)$', (ROOT / 'lean/FCSolution.lean').read_text(), re.M) == ['KalaiFast'],
            'Solution bridge differs')
    import importlib.util
    spec = importlib.util.spec_from_file_location('kalai_archive', ROOT / 'lean/comparator/check-archive.py')
    archive_module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(archive_module)
    archive = archive_module.source()
    require(archive['sha256'] == pins['fast_archive_sha256'], 'Fast archive pin differs')
    fc = (ROOT / 'FClikelean/Kalai.lean').read_text()
    require(len(re.findall(r'^theorem ', fc, re.M)) == 4 and fc.count('  sorry\n') == 4,
            'Unexpected FC draft statements')
    require(pins['prior_verified_commit'] in fc and 'formal_proof using lean4 at' in fc,
            'Missing fixed prior proof link')

    proc = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True)
    commit = proc.stdout.strip() if proc.returncode == 0 else None
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        require(commit == os.environ.get('GITHUB_SHA'), 'Checked commit differs from GitHub event')
    return {'input_check': 'passed', 'tested_commit': commit, 'pins': pins, 'config': config,
            'publication_manifest_sha256': digest(ROOT / 'PUBLICATION-MANIFEST.json'),
            'publication_files': len(hashes), 'original_modules': 976,
            'proof_source_map_sha256': digest(source_map_path), 'fc_version': '4.33.1',
            'exact_public_statement': True, 'whole_lean_proof_checked_by_this_command': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt-dir', type=Path)
    args = parser.parse_args()
    result = check()
    if args.receipt_dir:
        args.receipt_dir.mkdir(parents=True, exist_ok=True)
        (args.receipt_dir / 'input-check.json').write_text(json.dumps(result, indent=2) + '\n')
        for name in ['Challenge.lean', 'FCSolution.lean', 'FCAudit.lean', 'comparator.json']:
            (args.receipt_dir / name).write_bytes((ROOT / 'lean' / name).read_bytes())
    print(f"PASS: {result['publication_files']} publication files, 976 original modules, exact public statement.")


if __name__ == '__main__':
    main()
