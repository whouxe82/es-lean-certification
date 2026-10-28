#!/usr/bin/env python3
"""Verify that checked-out, tracked dependency sources match the lockfile."""
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'lean' / 'lake-manifest.json').read_text())
records = []
for package in manifest['packages']:
    path = root / 'lean' / '.lake' / 'packages' / package['name']
    actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True).splitlines()
    records.append({'name': package['name'], 'expected': package['rev'], 'actual': actual,
                    'match': package['rev'] == actual, 'tracked_source_changes': dirty})
print(json.dumps(records, indent=2))
sys.exit(0 if all(r['match'] and not r['tracked_source_changes'] for r in records) else 1)
