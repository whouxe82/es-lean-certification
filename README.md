# ES formal certification — 28 October 2026  

**Jointly validated computations (Claude, GPT, director replications), 29–30 Oct 2026 — including the refutation of Conjecture Q — are in [`es-xyz-validated/`](es-xyz-validated/README.md).**

Start with output/ES_Formal_Certification_Review_2026-10-28.pdf and the companion proof map.
The pinned Lean project proves supporting theorems, including full integral matching and
B4 descent. It does not prove H_D, H_N, or the universal Erdős–Straus conjecture.

For another rerun, follow lean/README.md. The user-controlled second verification is now complete; see the record below.
Keep lean/, scripts/, and logs/ as sibling directories. Install the pinned Lean toolchain,
enter lean/, run `lake exe cache get`, then `python3 ../scripts/record_verification.py`.
This rebuilds all delivered ES modules and runs the theorem-dependency and source audits.

Original-run authoritative receipts are logs/verification-receipt.json, logs/clean-build.log,
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


## User-controlled second verification completed

On **28 October 2026**, `whouxe82` completed [GitHub Actions run #1](https://github.com/whouxe82/es-lean-certification/actions/runs/40788446292), attempt 1, at commit `a92f65600f74847311746acf484d7af7746cde6b`. The public workflow is `.github/workflows/verify-es-lean.yml`.

| Item | Confirmed result |
|---|---|
| Environment | GitHub-hosted Ubuntu 24.04 runner (OS 24.04.5 LTS), controlled through the user's repository |
| Run started | 28 October 2026, 7:35:42 p.m. EDT (23:35:42 UTC) |
| Toolchain | Lean 4.19.0, release commit `6caaee842e94` |
| Mathlib | v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; pinned cache fetched |
| Clean rebuild plus audits | 117.077 seconds; exit 0; sources stable during verification |
| Job duration shown by GitHub | 3 minutes 16 seconds, including setup and cache retrieval |
| Axiom inventory | 310 theorem constants including generated helpers; 75 other safe declarations; 18 separately inventoried unsafe compiler stubs |
| Four pass conditions | Clean build, axiom audit, source audit, and compiled-input hash comparison all passed |
| Source identity | All 22 compiled-input SHA-256 entries exactly matched the original receipt |

The independent execution requirement previously left outstanding is satisfied. This is a second execution of the same proofs under user control on a separate hosted runner. It is not a claim of a local Windows, macOS, or WSL run or of independently authored proofs. The certified scope remains the supporting theorems, including full integral matching, B4 restrictions, and finite forcing; `H_D`, `H_N`, and universal ES remain open. Mathlib was imported from its pinned cache, not rebuilt from source.

The review checked the supplied screenshot PDFs, live GitHub run/job and artifact records, pinned workflow, full decoded job log, and original package. The workflow's successful assertion compares the two complete `compiled_input_sha256` dictionaries. A separate comparison of the run's Git tree with the original package confirmed the same 22 inputs.

- [Machine-readable second-verification record](verification/run-1/second-verification.json).
- [Full decoded job log](verification/run-1/job-123167382081.log).
- [Run-generated receipts artifact](https://github.com/whouxe82/es-lean-certification/actions/runs/40788446292/artifacts/12861010630): `es-lean-receipts`, 109,806 bytes, artifact ID `12861010630`.
- Artifact ZIP SHA-256 reported by GitHub: `199dd16acbcf689f7d5055189f317a6b1d31deb367e4ee441e0638d70a0af105`.

The artifact contains the rerun's `logs/` and copied `logs_gpt_original/`. Its reported expiry is **26 January 2027**. The ZIP bytes were not downloaded in this evidence review; its identity and digest were confirmed from GitHub metadata and the upload log. Preserve the ZIP before expiry. The retained job log and extracted record document the completed verification but do not replace its full per-file receipts.

The original reports retain their historical status at issuance; this entry supersedes their statement that a second run had not occurred. Original proof sources and `logs/verification-receipt.json` retain their certified contents. `MANIFEST_SHA256.json` covers the updated repository files; the original delivery manifest is preserved at [verification/run-1/original-package-MANIFEST_SHA256.json](verification/run-1/original-package-MANIFEST_SHA256.json).
