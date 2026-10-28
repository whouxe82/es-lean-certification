#!/usr/bin/env python3
"""Run real project verification and record exits, source hashes, and axiom counts."""
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
paths = sorted((root / 'lean' / 'ES').rglob('*.lean'))
paths += [root / 'lean' / p for p in ['ES.lean', 'Audit.lean', 'lakefile.toml', 'lean-toolchain', 'lake-manifest.json']]
paths += [root / 'scripts' / p for p in ['verify.sh', 'audit_sources.py', 'check_dependencies.py', 'generate_aggregate.py', 'record_verification.py']]

def hashes():
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}

before = hashes()
started = datetime.now(timezone.utc).isoformat()
t0 = time.monotonic()
run = subprocess.run(['bash', str(root / 'scripts' / 'verify.sh')], cwd=root, text=True, capture_output=True)
(root / 'logs' / 'verification-driver.log').write_text(run.stdout + run.stderr)
after = hashes()
axiom_path = root / 'logs' / 'axioms-all.log'
axioms = axiom_path.read_text() if axiom_path.exists() else ''
observed_modules = set(re.findall(r'^AUDIT_MODULE\|(.+)$', axioms, re.M))
expected_modules = {'ES'} | {'ES.' + '.'.join(p.relative_to(root / 'lean' / 'ES').with_suffix('').parts) for p in paths if root / 'lean' / 'ES' in p.parents}
missing_modules = sorted(expected_modules - observed_modules)
counts = Counter()
for line in axioms.splitlines():
    if line.startswith('AUDIT|'):
        counts[line.split('|')[1]] += 1
m = re.search(r'^AUDIT_TOTAL\|(\d+)\s*$', axioms, re.M)
safe_total = re.search(r'^AUDIT_SAFE_TOTAL\|(\d+)\s*$', axioms, re.M)
stub_total = re.search(r'^AUDIT_COMPILER_STUB_TOTAL\|(\d+)\s*$', axioms, re.M)
receipt = {
    'command': 'bash scripts/verify.sh',
    'started_utc': started,
    'completed_utc': datetime.now(timezone.utc).isoformat(),
    'elapsed_seconds': round(time.monotonic() - t0, 3),
    'exit_code': run.returncode,
    'source_files_stable_during_verification': before == after,
    'compiled_input_sha256': before,
    'final_input_sha256': after,
    'theorem_constants_audited_including_generated_helpers': int(m.group(1)) if m else None,
    'other_safe_declarations_audited': int(safe_total.group(1)) if safe_total else None,
    'unsafe_compiler_stubs_inventoried': int(stub_total.group(1)) if stub_total else None,
    'theorem_constants_by_module': dict(sorted(counts.items())),
    'audited_modules': sorted(observed_modules),
    'missing_modules': missing_modules,
    'allowed_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'provenance_limit': 'Execution and content receipt only; not cryptographic model, labor, or independent-review attestation.',
}
(root / 'logs' / 'verification-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps({k: v for k, v in receipt.items() if k not in ['compiled_input_sha256', 'final_input_sha256']}, indent=2))
sys.exit(run.returncode if run.returncode else (0 if before == after and m and not missing_modules else 1))
