# Prover infrastructure receipt

This report records actual commands and outputs, not a mathematical proof of the Erdős–Straus conjecture.

## Pinned installation

- Lean 4.19.0, release commit `6caaee842e94`, Linux x86_64.
- Lake 5.0.0-6caaee8 (Lean 4.19.0).
- Mathlib tag `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Project: `round_z5/lean`; toolchain: `round_z5/toolchain/lean-4.19.0-linux`.
- All 6,641 Mathlib cache files downloaded and unpacked successfully; actual receipt: `round_z5/logs/mathlib-cache.log`. Full `import Mathlib`, an integer `ring` proof, and the pinned Dirichlet theorem name compiled successfully; receipt: `round_z5/logs/mathlib-smoke.log`.
- Dependency lockfile: `round_z5/lean/lake-manifest.json`. All nine checked-out dependency HEADs exactly match it; receipt: `round_z5/logs/dependency-manifest-audit.json`.
- Actual version and SHA-256 receipt: `round_z5/logs/toolchain-manifest.txt`.
- Archive extraction succeeded using `tar --no-same-owner --use-compress-program=unzstd`.

## Container compatibility

The stock Lean executable initially reported `failed to locate application`. Lean 4.19's runtime uses `readlink("/proc/<getpid()>/exe", ...)`; this container's PID namespace returns PID 2 although `/proc/2/exe` is unavailable. `/proc/self/exe` works. The minimal source `round_z5/toolchain/proc_self_compat.c`, compiled with GCC as `proc_self_compat.so`, redirects exactly that own-process executable-path lookup to `/proc/self/exe`. No Lean kernel or theorem routines are altered. Stock archive extraction and leantar installation also needed `TAR_OPTIONS=--no-same-owner` because foreign archive ownership IDs are unavailable; this affects file metadata only. `round_z5/lean/env.sh` sets the binary path and this compatibility library.

The actual standalone Lean smoke check `round_z5/toolchain/Smoke.lean` successfully proved `kernelSmoke (n : Nat) : n + 0 = n`. Its `#print axioms` output is `'kernelSmoke' does not depend on any axioms`, saved in `round_z5/logs/toolchain-smoke.log`.

## Reproduction in this container

```sh
cd /workspace/scratch/15f1326ae9dc/round_z5/lean
source env.sh
lake env lean ES/Basic.lean
lake build ES
lake env lean Audit.lean
```

The complete reproducible project verification command is `bash round_z5/scripts/verify.sh`. It cleans only the root package (`lake clean es_certification`), rebuilds all project modules, audits transitive axiom dependencies, and scans source hygiene. It preserves the imported dependency caches.

For Linux, macOS, or WSL replay outside this container, follow `lean/README.md`: install Elan, select the pinned Lean toolchain, fetch the locked cache, and run `python3 ../scripts/record_verification.py`. Do not source the container-only environment file on an ordinary machine. No replay on `whouxe82`, macOS, or WSL was performed or observed in this session.

## Final mathematical build and axiom audit

**Final status: PASS, actual exit 0.** `scripts/record_verification.py` ran the complete clean verification in 161.010 seconds. It removed only the root package's generated build artifacts, then rebuilt the complete `ES` library from source. Every one of the 12 delivered mathematical modules is imported by `ES.lean`, rebuilt, and present in the audited environment. There are zero omitted modules. All proof/instrumentation input hashes were identical before and after the run. All nine dependency HEADs match the lockfile and their tracked sources are clean.

Canonical final receipts:

- `logs/verification-receipt.json`: actual command, exit, timing, before/after SHA-256 hashes, module coverage, and counts.
- `logs/clean-build.log`: final successful clean build, including per-module printed axiom receipts.
- `logs/axioms-all.log`: full final environment audit.
- `logs/source-audit.json`: source hygiene result and per-file SHA-256 hashes.
- `logs/dependency-manifest-audit.json`: pinned and clean dependency checks.

The final audit checks **310 theorem constants**, including generated helper proofs, and **75 other safe declarations**. Every transitive axiom closure is contained in exactly the allowed set `{propext, Classical.choice, Quot.sound}`; no other mathematical axiom is permitted. It also rejects any safe project axiom declaration. The source audit found **191 authored theorem/lemma commands**, zero authored `axiom`, `sorry`, `admit`, `native_decide`, or `debug.skipKernelTC` tokens outside comments/strings. Source scanning supplements the actual kernel build; it is not a proof by itself.

| Module | Authored theorem/lemma commands | Audited theorem constants, including helpers |
|---|---:|---:|
| `ES.Basic` | 9 | 16 |
| `ES.Bridges` | 34 | 48 |
| `ES.Descent` | 27 | 53 |
| `ES.EdgeClassification` | 6 | 9 |
| `ES.Families` | 26 | 41 |
| `ES.Forcing` | 27 | 55 |
| `ES.Literature` | 6 | 6 |
| `ES.Matching` | 13 | 17 |
| `ES.MatchingGraph` | 24 | 40 |
| `ES.Normalization` | 4 | 4 |
| `ES.Pivot` | 5 | 5 |
| `ES.PriorOffsetCore` | 10 | 16 |

### Initial audit rejection and exact correction

The first full clean build succeeded, but an additional blanket check rejecting every project `axiomInfo` entry rejected an unsafe compiler specialization of `Option.decEqOption` in `ES.Forcing.avoidanceProfiles`. That was an overbroad instrumentation rule. Its failed receipt and output are preserved in `logs/verification-initial-failed.json`, `logs/axioms-all-initial-failed.log`, and `logs/clean-build-initial.log`.

Inspection found **18 unsafe computational compiler stubs**, with explicit `isUnsafe = true`, whose types include specialized equality decisions and `Finset`, `Multiset`, and `List` computations. Their complete names, types, and safety flags are retained in `logs/generated-axioms-inspection.log` and the final audit log. Separate same-session review independently checked all 310 theorem closures and all 75 other safe declaration closures (`logs/forcing-stub-review.log`). A further inspection verified that each of the 18 stubs has actual `Lean.IR.findEnvDecl` compiler code, with no safe axiom entries (`logs/forcing-stub-provenance.log`).

The corrected audit rejects all safe project axiom declarations, inventories unsafe compiler entries separately, and retains the unchanged strict dependency whitelist for **every theorem and every other safe declaration**. It grants no stub permission to appear in those dependency closures. The separate source ban still rejects all authored axiom commands. No mathematical proof source was changed to resolve the audit issue. The final clean replay then passed. Historical failed-development logs are not the final certification receipt.

## Provenance and limits of this receipt

The requested agent configuration is observable in this session's orchestration/task records. Source files, logs, and dependency hashes document the artifacts and executions recorded here. They are not cryptographic attestations of model identity, reasoning effort, agent labor, or human-independent review. Replaying Lean checks the formal statements against Lean's kernel and imported dependencies; it does not verify how much work an agent performed or establish originality. The allowed standard axioms are stated explicitly. This report does not claim an independent implementation of the kernel or an independently administered verification run.
