#!/usr/bin/env python3
"""Source hygiene audit; kernel axiom dependencies are checked separately by Audit.lean."""
import hashlib
import json
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]

def strip_comments_and_strings(text):
    out = []
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(' ')
        else:
            out.append(text[i])
            i += 1
    return ''.join(out)

files = []
violations = []
for path in sorted((root / 'lean' / 'ES').rglob('*.lean')):
    data = path.read_bytes()
    clean = strip_comments_and_strings(data.decode())
    bad = sorted(set(re.findall(r'(?<![\w.])(sorry|admit|axiom|native_decide|debug\.skipKernelTC)(?!\w)', clean)))
    record = {
        'file': str(path.relative_to(root)),
        'sha256': hashlib.sha256(data).hexdigest(),
        'authored_theorem_or_lemma_commands': len(re.findall(r'\b(?:theorem|lemma)\s+', clean)),
        'forbidden_tokens': bad,
    }
    files.append(record)
    if bad:
        violations.append(record['file'])
result = {
    'audit_kind': 'source_hygiene_not_a_kernel_proof',
    'files': files,
    'authored_theorem_or_lemma_commands_total': sum(f['authored_theorem_or_lemma_commands'] for f in files),
    'violations': violations,
    'passed': not violations,
}
print(json.dumps(result, indent=2))
sys.exit(bool(violations))
