# ES formal certification — 28 October 2026

Start with output/ES_Formal_Certification_Review_2026-10-28.pdf and the companion proof map.
The pinned Lean project proves supporting theorems, including full integral matching and
B4 descent. It does not prove H_D, H_N, or the universal Erdős–Straus conjecture.

For the whouxe82 rerun, follow lean/README.md. No run on that machine occurred here.
Keep lean/, scripts/, and logs/ as sibling directories. Install the pinned Lean toolchain,
enter lean/, run `lake exe cache get`, then `python3 ../scripts/record_verification.py`.
This rebuilds all delivered ES modules and runs the theorem-dependency and source audits.

Authoritative receipts are logs/verification-receipt.json, logs/clean-build.log,
logs/axioms-all.log, logs/source-audit.json, and logs/dependency-manifest-audit.json.
Other logs retain development history and may contain earlier errors; they are not the
final certification result. The audit report explains the generated compiler stubs.

The full Lean installation and Mathlib caches are omitted. The container compatibility
shim source is retained for transparency; ordinary installations should not need it.
The source manifest detects byte changes, but is not a digital signature or author/model
attestation. Agent provenance, originality, and informal interpretation are separate claims.

The partial port in ES/PriorOffsetCore.lean retains its upstream Apache-2.0 notice;
the full license is in prior_art/offset/LICENSE. Other upstream repositories are linked
and pinned in reports/literature_formal.md; their complete repositories are not included.

To regenerate figures/reports separately, install Python matplotlib and reportlab and
provide DejaVu Sans fonts at the paths in make_report.py. This is not needed for Lean replay.
