# Arbitrary Type II normalization

**Status: kernel-checked, complete for the stated normalization.** `lean/ES/Normalization.lean` proves the normal form from arbitrary positive prime-input ES triples. It does not assume canonical parameters in its input.

## Main API

`ESNormalization.normalize_typeII_denominators` takes natural numbers `p,x,y,z` and exactly these hypotheses:

- `p.Prime`;
- `ES.IsSolution p x y z`, which includes positivity and the polynomial ES equation;
- `¬p ∣ x`, `p ∣ y`, `p ∣ z`;
- `y ≤ z`.

It produces positive natural parameters `δ,r,s,t` with

`ES.NormalizedII p δ r s t`,

`x = δ*r*s`, `y = p*δ*r*t`, `z = p*r*s*t`.

Thus `δ.Coprime s`, `δ≤s`, and `4δrst=pt+δ+s` are conclusions. The theorem assumes neither source normalization nor the desired classification. No restriction `p=1 mod4` is needed for normalization.

`ESNormalization.normalize_typeII_bridge` has the same inputs and coordinate conclusions, and returns `ESBridge.TypeII` directly through the checked natural-to-integer interface.

`ESNormalization.normalize_typeII` is the core API when the two divisible denominators are already written as `p*a,p*b`, with `0<a≤b`.

## Actual proof

1. Cancel `p²` from the ES equation to obtain `4*x*a*b = p*a*b+x*(a+b)` (`typeII_reduced_equation`).
2. Use the existing natural gcd decomposition to write `a=δ*g`, `b=s*g`, with `g>0` and coprime `δ,s`. Positivity and ordering are derived.
3. Cancel `g`. Coprimality of `δ*s` with `δ+s` then proves `δ*s ∣ x`; write `x=δ*s*r` and derive `r>0`.
4. The reduced equation proves `r ∣ p*g`. Since `r ∣ x`, primality of `p` and `p∤x` give `r.Coprime p`. Consequently `r∣g`; write `g=r*t` and derive `t>0`.
5. Cancel the positive `r` to obtain the normalized Type II equation and all coordinate identities.

The proof stays in natural arithmetic and uses no truncated subtraction. All cancellation steps explicitly use positive factors.

## Receipt

Actual final command in `round_z5/lean`, after sourcing `env.sh`:

```text
set -o pipefail
lake build ES.Normalization 2>&1 | tee ../logs/normalization-final-build.log
```

**Exit status: 0.** The receipt ends with `Built ES.Normalization` and `Build completed successfully.` The module itself has no warnings. Dependency linter warnings are unrelated stylistic warnings in `ES.Bridges`.

The four `#print axioms` outputs are:

- `typeII_reduced_equation`: `[propext]`.
- `normalize_typeII`: `[propext, Classical.choice, Quot.sound]`.
- `normalize_typeII_denominators`: `[propext, Classical.choice, Quot.sound]`.
- `normalize_typeII_bridge`: `[propext, Classical.choice, Quot.sound]`.

There are no target axioms, `sorry`, `admit`, `native_decide`, or finite checks in this proof. An earlier failed build log is retained as development history; only the successful final receipt certifies the final source.

## Scope

This closes the arbitrary-Type-II-to-normalized-source gap needed to apply the bridge lane's exact gates and opposite-pivot obstruction globally. It does not by itself assert the permutation-quotient graph matching theorem: graph/orientation assembly belongs to `ES/Matching.lean`. It also does not prove that a Type II source exists for an arbitrary prescribed prime, nor resolve `H_D`, `H_N`, or universal ES.

`ES/Descent.lean` was left frozen throughout this extension.
