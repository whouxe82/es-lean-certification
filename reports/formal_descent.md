# Formal descent and dyadic scope restriction

**Status: all requested descent, recurrence/parity, and dyadic no-rescue claims in this lane are kernel-checked.** The final module is `lean/ES/Descent.lean`, compiled with Lean 4.19.0 and Mathlib v4.19.0. The source-level conclusions derive their norm equation from the actual B4 gate; they do not assume `t=1`, odd delta, or a recurrence classification.

## Final source-level theorems

All names below are in namespace `ESDescent`. Let the integer source satisfy `ESBridge.TypeII p δ r s t`: positive parameters, `IsCoprime δ s`, `δ ≤ s`, and

`4*δ*r*s*t = p*t + δ + s`.

Assume `p = 4*k+1` and the precise B4 gate

`4*δ*s ∣ (4*δ*r*s-p)^2-1`.

| Kernel-checked theorem | Additional input | Conclusion |
|---|---|---|
| `b4_source_restriction` | None | `t = 1 ∧ δ % 2 = 1` |
| `b4_dyadic_no_rescue` | `∃ j : ℕ, δ = 2^j` | `δ = 1 ∧ t = 1 ∧ δ*t ∣ k` |
| `normalizedII_b4_dyadic_no_rescue` | Shared `ES.NormalizedII` and `ES.Dyadic` definitions | Same conclusion over natural parameters; the gate remains in integers to avoid truncated subtraction |
| `b4_dyadic_endpoints_equal` | Dyadic source; `p+d=4δrs`; `4C=pd+1` | Exact equality of the full rational B4 triple `(tC/s,tC/δ,pC)` and B1 triple `(k+δrt,(k+δrt)s/t,p(k+δrt)s/δ)` |

No primality hypothesis is needed for these restrictions. The existence of a normalized source is an explicit premise, not a conclusion. The B4 gate is identified with actual integral return by the separately checked `ESBridge.b4_rational_integral_iff` and `ESBridge.b4_integer_return_iff`.

## Descent actually proved

`companion m t a b = (4*m*t^2-2)*a-b` is an integer expression; there is no quotient or truncated subtraction. The checked helper lemmas establish:

- `companion_product`: `b*companion = a^2-t^2`.
- `companion_norm`: the same norm equation holds at `(companion,a)`.
- `companion_coprime`: coprimality survives, using an explicit Bezout witness.
- `companion_sum_dvd`: `t ∣ a+b` survives, with an explicit divisor witness.
- `norm_large_coordinate`: every positive ordered norm shape with positive `m` satisfies `a*t^2 < b`.
- `companion_bounds`: if `t<a`, then `0<companion<a`.
- `terminal_t_one`: at `a≤t`, divisibility and the strict bound give `a=t`, and coprimality then gives `t=1`.

`norm_t_one_aux` uses strong induction on the natural measure `a.toNat`; the recursive step carries all hypotheses to the strictly smaller companion. `norm_t_one` and `norm_t_one_gcd` expose the final theorem with `IsCoprime` and integer-gcd interfaces, respectively.

The source integration uses `ESBridge.b4_parameters` to derive positive `d`, `d*t=a+b`, and the equations for `d,C`; `ESBridge.b4_gate_norm` constructs a positive integer `m` from the B4 divisor witness. Thus the norm premise in the auxiliary theorem is fully discharged for `b4_source_restriction`.

## Recurrence and parity actually proved

The checked recurrence is

`shapePair m 0 = (1,4*m-2)`

`shapePair m (n+1) = (b,(4*m-2)*b-a)` when `shapePair m n = (a,b)`.

| Theorem | Certified statement |
|---|---|
| `shapePair_valid` | For positive `m`, every recurrence pair is positive, strictly ordered, and satisfies `(a+b)^2 = 4*m*a*b+1`. |
| `norm_recurrence_complete` | Every positive ordered solution of that equation occurs in the recurrence; proved by strong Vieta descent. |
| `shapePair_mod_four` | Exact residues: the two coordinates are `n+1` and `n+2` modulo 4. |
| `shapePair_allowed_iff_even` | The sum is 3 modulo 4 exactly when the recurrence index is even. |
| `norm_difference_mod_four` | An independent second descent proves `(b-a)%4=1`. |
| `norm_delta_odd` | With `t=1` derived and sum 3 modulo 4, the smaller coordinate is odd. |
| `norm_shape_restriction` | The parity input is given on the original `d`, via `d*t=a+b` and `d%4=3`. |

The recurrence proof here is direct and does not import Mathlib's Pell classification. The literature lane separately identifies the existing Pell framework and proves the algebraic dictionary; no historical novelty is asserted.

## Build and axiom receipt

Final command, run in `round_z5/lean` after sourcing `env.sh`:

```text
set -o pipefail
lake build ES.Descent 2>&1 | tee ../logs/descent-final-build.log
```

**Actual exit status: 0.** The log ends with `Built ES.Descent` and `Build completed successfully.` The final descent module has no warnings; dependency warnings in `ES.Bridges` are stylistic linter warnings.

The module contains `#print axioms` for 17 main/helper theorems. Every listed theorem depends only on:

`propext`, `Classical.choice`, `Quot.sound`.

`shapePair_mod_four` uses only `propext`, `Quot.sound`. No target axioms, `sorry`, `admit`, `native_decide`, or finite enumeration support the descent or scope conclusions. The complete receipt is in `logs/descent-final-build.log`; earlier direct-elaboration receipts include `logs/descent-integrated.log` and `logs/descent-endpoints.log`.

## Review and limits

This lane independently reviewed the bridge algebra and hypotheses: the cancellation assumptions in B1 are derived from `TypeII`, the B4 gate algebra has the correct signs, and positive `m` is obtained from the gate with `d≥3`. The forcing lane independently reviewed the descent logic, including the need to discharge `t∣a+b`; the integrated source theorem discharges it from `d*t=a+b`.

These results classify this exact four-step construction. They prove zero new dyadic endpoint edges for it. The auxiliary descent is not an ES normalization algorithm at fixed `p`. No source existence for an arbitrary input is established. `H_D`, `H_N`, and the universal Erdős–Straus conjecture remain open. Other rational paths are outside this theorem. A separate uniqueness-of-recurrence-index theorem and the full nondyadic B1/B4 overlap characterization were not needed and are not claimed here.
