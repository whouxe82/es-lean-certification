#!/usr/bin/env python3
"""Explicitly import every delivered project module; run before freezing proofs."""
from pathlib import Path
root = Path(__file__).resolve().parents[1]
lean = root / 'lean'
modules = sorted('ES.' + '.'.join(p.relative_to(lean / 'ES').with_suffix('').parts)
                 for p in (lean / 'ES').rglob('*.lean'))
body = ''.join(f'import {name}\n' for name in modules)
body += '''
/- The open propositions ES.HD, ES.HN, and ES.ErdosStraus are definitions.
   This aggregate imports supporting results; it does not prove those open propositions. -/
'''
(lean / 'ES.lean').write_text(body)
print('\n'.join(modules))
