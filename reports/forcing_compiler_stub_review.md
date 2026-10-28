# Independent review of compiler-stub audit correction

**Conclusion:** The initial audit rejection concerned an unsafe compiler specialization, not a logical assumption of a certified theorem. The correction keeps the logical axiom whitelist unchanged. `ES/Forcing.lean` was not changed.

The first rejected declaration was

```
_private.Init.Data.Option.Basic.0.Option.decEqOption.«_@».Init.Data.Option.Basic._hyg.4._at.ES.Forcing.avoidanceProfiles._spec_1
```

Environment inspection identifies it as `axiomInfo`, **`isUnsafe = true`**, with the computational type

```
(n : Nat) → (a b : Option (Fin n)) → Decidable (a = b)
```

The exact printed type and all other entries are in `logs/forcing-stub-review.log`. There are eighteen such entries, all in `ES.Forcing`, representing equality decisions, finite sums, filters, finite products, and images.

## Independent executed checks

1. `toolchain/ForcingStubReview.lean` imported the final project and inspected every project theorem and every other safe non-axiom declaration. **Exit 0:** all **310 theorem constants** and **75 other safe declarations** have transitive axiom dependencies contained in exactly `{propext, Classical.choice, Quot.sound}`. No specialization name was added to the allowed list. The exact `REVIEW_TOTAL` receipt is in `logs/forcing-stub-review.log`.
2. `toolchain/ForcingStubProvenance.lean` independently required every project axiom-info entry to be unsafe and to possess an actual compiler IR declaration returned by `Lean.IR.findEnvDecl`. **Exit 0:** all **18** entries satisfy both requirements. `logs/forcing-stub-provenance.log` records each name. This identifies computational code provenance rather than relying on an `_spec` naming convention.
3. Inspected the actual Lean 4.19.0 `Lean/Util/CollectAxioms.lean`: it follows the checked kernel environment recursively through declaration types and values. Also inspected `ConstantInfo.isUnsafe` in `Lean/Declaration.lean` and the compiler-safety explanation in `Init/Prelude.lean`.

## Review of the corrected main audit

The reviewed `lean/Audit.lean` correction rejects every **safe project axiom**, separately inventories unsafe axiom-info entries, and checks every theorem and other safe declaration against the same original three-name whitelist. Thus an unexpected axiom in a theorem's dependency closure still fails, regardless of its name or unsafe status. The separate source audit also bans authored `axiom` commands. The supplementary IR-provenance check above is additional evidence; it does not exempt any logical dependency.

This is a correction to the declaration inventory's classification, **not an expansion of the permitted logical assumptions**. The original assertion “every axiom-info entry is a mathematical axiom introduced by the project” was too broad for executable Lean definitions, whose compiler can create unsafe computational specializations.

## Trust boundary

The evidence relies on the installed Lean 4.19.0 kernel, its environment/dependency inspection functions, and the pinned imported library. It is not an independent kernel implementation or cryptographic provenance attestation. The mathematical proofs do not depend on the eighteen compiler stubs. In particular, the finite certificates use kernel-checked `decide`/arithmetic proof terms, not `native_decide`; correctness of executing the compiled optimizer is not being substituted for a proof. Ordinary standard logical axioms remain explicitly allowed as recorded above.
