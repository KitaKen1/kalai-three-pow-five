#!/usr/bin/env python3
"""Check pinned sources, the sole permitted toolchain patch and FC Lean version."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
pins = json.loads((root / 'lean/comparator/pins.json').read_text())
tools = Path(sys.argv[1]).resolve()
output = Path(sys.argv[2])
changes = {}
for tool, key in [('comparator', 'comparator_commit'), ('lean4export', 'lean4export_commit'),
                  ('landrun', 'landrun_commit')]:
    actual = subprocess.check_output(['git', '-C', str(tools / tool), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != pins[key]:
        raise SystemExit('Checker commit differs: ' + tool)
    directory = tools / tool
    expected = pins['toolchain_patches'].get(tool, {}).get('changed_files', [])
    actual_changes = subprocess.check_output(
        ['git', '-C', str(directory), 'diff', 'HEAD', '--name-only'], text=True).splitlines()
    if actual_changes != expected:
        raise SystemExit('Unexpected checker source changes: ' + tool)
    if expected:
        upstream = subprocess.check_output(['git', '-C', str(directory), 'show',
                                           'HEAD:lean-toolchain'], text=True).strip()
        if upstream != pins['toolchain_patches'][tool]['upstream']:
            raise SystemExit('Upstream toolchain differs: ' + tool)
    changes[tool] = actual_changes
versions = {}
for name, directory in [('proof', root / 'lean'), ('comparator', tools / 'comparator'),
                         ('lean4export', tools / 'lean4export')]:
    if (directory / 'lean-toolchain').read_text().strip() != pins['lean_toolchain']:
        raise SystemExit('Toolchain differs: ' + name)
    version = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=directory, text=True).strip()
    if 'version 4.33.1,' not in version:
        raise SystemExit('Compiler differs: ' + name)
    versions[name] = version
binaries = {name: hashlib.sha256((tools / name / '.lake/build/bin' / name).read_bytes()).hexdigest()
            for name in ['comparator', 'lean4export']}
output.parent.mkdir(parents=True, exist_ok=True)
output.write_text(json.dumps({'status': 'PASS', 'required_version': '4.33.1',
                             'compiler_versions': versions, 'binary_sha256': binaries,
                             'source_changes': changes}, indent=2) + '\n')
