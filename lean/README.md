# Replaying the ES supporting-results certificate

This project proves the statements in the included Lean modules. `ES.HD`, `ES.HN`, and `ES.ErdosStraus` remain open propositions; their definitions and conditional implications are not proofs of those propositions.

The first recorded build was performed in the supplied Linux container. **The user-controlled second verification is complete:** on 28 October 2026, `whouxe82` ran [GitHub Actions run #1](https://github.com/whouxe82/es-lean-certification/actions/runs/40788446292) on a separate Ubuntu 24.04 hosted runner. The clean rebuild and audits passed in 117.077 seconds, and all 22 compiled-input hashes matched the original receipt. See the [verification record](../verification/run-1/second-verification.json) and [root README](../README.md#user-controlled-second-verification-completed). This hosted rerun is distinct from a local macOS or WSL run. The following instructions remain available for further replays.

## Pinned versions

- Lean: `leanprover/lean4:v4.19.0` (release commit `6caaee842e94`).
- Mathlib: `v4.19.0`, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Exact transitive revisions: `lake-manifest.json`.

Keep the delivered directory layout: `lean/`, `scripts/`, and `logs/` are siblings inside the extracted round directory. The full toolchain binaries and downloaded dependency caches need not be shipped.

## Linux, macOS, or Windows through WSL

Use Bash with Git, curl, and Python 3 installed. On WSL, run these commands inside the Linux distribution. On macOS, install the Xcode Command Line Tools if Git is unavailable. The Elan installation command below follows the [official Lean installation guide](https://lean-lang.org/install/manual/); Elan's [upstream documentation](https://github.com/leanprover/elan) explains project toolchain selection.

If Elan is not already installed:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

From the delivered `lean` directory:

```bash
elan toolchain install leanprover/lean4:v4.19.0
lean --version
lake --version
lake exe cache get
lake build ES
lake env lean Audit.lean
python3 ../scripts/audit_sources.py
```

`lean --version` must report 4.19.0. The checked-in `lean-toolchain` selects that version when using Elan. `lake exe cache get` retrieves the pinned dependency artifacts; it does not prove this project's source. `lake build ES` elaborates and kernel-checks this project's proofs against those imported dependencies.

For a clean rebuild of all delivered project proofs, followed by the axiom and source audits with a machine-readable receipt:

```bash
python3 ../scripts/record_verification.py
```

This cleans only the root package `es_certification`, preserving dependency caches. Success requires an exit status of zero, `Build completed successfully.` in `../logs/clean-build.log`, a final `AUDIT_TOTAL` entry in `../logs/axioms-all.log`, and `passed: true` in `../logs/source-audit.json`. `../logs/verification-receipt.json` records the actual exit, source hashes before and after the run, and theorem-constant counts. These counts include compiler-generated helper proofs.

## Trust and scope

`Audit.lean` rejects safe project axiom declarations and all theorem/safe-declaration dependencies outside `propext`, `Classical.choice`, and `Quot.sound`. Unsafe computational compiler stubs are inventoried separately, including their type and safety flag; they receive no exemption from the dependency whitelist. The source audit rejects all authored axiom commands, proof placeholders, `native_decide`, and kernel-check skipping. Finite example proofs, conditional theorems, and imported classical results retain the scope stated in their source and reports. Replaying a theorem checks its formal statement; it does not prove unstated mathematical claims, novelty, agent identity, or amount of work performed.

The original container required a documented executable-path compatibility shim because its numeric `/proc/<pid>/exe` path was unavailable. The shim changes only that path lookup to `/proc/self/exe`; it does not alter the kernel. On a normal machine, **do not source the container-specific `env.sh` or preload its shim**. Use Elan and the pinned toolchain above. If the delivered bundle omits the complete container toolchain, the replay scripts automatically use the tools already on the user's PATH.

