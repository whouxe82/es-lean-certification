"""Q-attack — exhaustive energy-route test (Colab-ready; standard library; exact integers).
For every prime p ≡ 1 (mod 24) up to N it decides Conjecture Q exactly (all admissible x, all eligible cells, E_C < M_C
with M_C from the closed formula of Theorem E3), then repeats with the non-residue restriction on x removed ("Q-extended").
Prefilter: a cell can force only if its target is occupied, i.e. only at x where a channel fires; non-firing x are skipped
(their actual histogram already avoids the target, so M <= E there).  Outputs a JSON record of every Q-failure with the
list of eligible cells at firing x (d, x, channel, T, E, M) — the data of a Proposition E10 refutation certificate.
Implementation reproduces the 29-prime pilot record exactly (10,884 eligible cells; 40 infinite; 161 witnesses).
Set N below. 120,000 runs in ~2 s; 1,000,000 in a few minutes; memory ~ N/4 ints."""
import sys, math, time, json
from collections import Counter

N = 1_000_000
if len(sys.argv) > 1 and sys.argv[1].isdigit(): N = int(sys.argv[1])
t0 = time.time()
M_ = N + 2
spf = list(range(M_))
for i in range(2, int(M_ ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, M_, i):
            if spf[j] == j: spf[j] = i

def factor(n):
    f = {}
    while n > 1:
        q = spf[n]; e = 0
        while n % q == 0: n //= q; e += 1
        f[q] = e
    return f
def is_prime(n): return n > 1 and spf[n] == n
def jacobi(a, n):
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0
def subgroup(gens, d):
    H = {1 % d}; frontier = [1 % d]
    while frontier:
        new = []
        for h in frontier:
            for g in gens:
                v = h * g % d
                if v not in H: H.add(v); new.append(v)
        frontier = new
    return H
def M_formula(b, f, c, T):
    if T < c or (T - c) % 2: return math.inf
    U = (T - c) // 2; D = 2 * b + f + c
    if D == 0: return 0 if T == 0 else math.inf
    q, r = divmod(U, D); r1 = min(r, b); r2 = min(max(r - b, 0), f); r3 = max(r - b - f, 0)
    return c + 4 * D * q * q + 4 * c * q + (8 * q + 2) * r1 + (8 * q + 4) * r2 + (8 * q + 6) * r3

def histogram(fac, d):
    hist = Counter({1 % d: 1})
    for q, e in fac.items():
        qm = q % d; pw = [1 % d]
        for _ in range(2 * e): pw.append(pw[-1] * qm % d)
        new = Counter()
        for r, cnt in hist.items():
            for v in pw: new[r * v % d] += cnt
        hist = new
    return hist

def cells(p, x, fac, hist):
    d = 4 * x - p
    H = subgroup([q % d for q in fac], d); K = {h * h % d for h in H}
    iota = lambda r: x * x * pow(r, -1, d) % d
    xd = x % d; out = []
    for ch, t in (("I", (-p * x) % d), ("II", (-x) % d)):
        if t not in H: continue
        C = {t * k % d for k in K}
        T = sum(hist.get(r, 0) for r in C); E = sum(hist.get(r, 0) ** 2 for r in C)
        orbit = {t, iota(t)}
        if xd in orbit: M = math.inf; mech = "central"
        else:
            rest = C - orbit
            b = sum(1 for r in rest if iota(r) != r) // 2
            f = sum(1 for r in rest if iota(r) == r and r != xd)
            c = 1 if xd in rest else 0
            M = M_formula(b, f, c, T); mech = "infinite" if M == math.inf else "finite"
        out.append(dict(d=d, x=x, ch=ch, T=T, E=E, M=(M if M != math.inf else "inf"), mech=mech, forces=E < M))
    return out

def test_prime(p, nonresidue_only=True, keep_cells=False):
    """returns (holds, first_witness, cell_list_at_firing_x)"""
    recs = []; first = None
    for x in range((p + 3) // 4, (3 * (p - 1)) // 4 + 1):
        if nonresidue_only and jacobi(x, p) != -1: continue
        d = 4 * x - p; fac = factor(x); hist = histogram(fac, d)
        if hist.get((-x) % d, 0) == 0 and hist.get((-p * x) % d, 0) == 0: continue   # no channel fires
        cs = cells(p, x, fac, hist)
        if keep_cells: recs.extend(cs)
        for c in cs:
            if c["forces"] and first is None:
                first = dict(c, jacobi_x=jacobi(x, p))
                if not keep_cells: return True, first, recs
    return first is not None, first, recs

primes = [p for p in range(25, N + 1, 24) if is_prime(p)]
def in_R(p): return p % 840 in (1, 121, 169, 289, 361, 529) and all(q % 4 == 1 for q in factor(p + 1) if q != 2)
R_count = sum(1 for p in primes if in_R(p))
print(f"{len(primes):,} primes ≡ 1 (mod 24) up to {N:,}; {R_count:,} of them in R (six classes, p+1 free of primes ≡ 3 mod 4); sieve ready at {time.time()-t0:.0f} s", flush=True)
fails = []; ext_fails = []; first_is_residue = 0; first_dQ = Counter()
for i, p in enumerate(primes, 1):
    if i % 1000 == 0: print(f"  ... {i:,} primes done, p = {p:,}, Q-failures so far {len(fails)}, {time.time()-t0:.0f} s", flush=True)
    holds, first, _ = test_prime(p, True)
    if not holds:
        _, _, recs = test_prime(p, True, keep_cells=True)
        inR = p % 840 in (1, 121, 169, 289, 361, 529) and all(q % 4 == 1 for q in factor(p + 1) if q != 2)
        fails.append(dict(p=p, mod840=p % 840, in_R=inR, firing_cells=recs))
        print(f"Q FAILS at p = {p:,} (p mod 840 = {p % 840}, in R = {inR}); eligible cells at firing x: {len(recs)}, all with E >= M", flush=True)
    else:
        first_dQ[first["d"]] += 1
    holds2, first2, _ = test_prime(p, False)
    if not holds2: ext_fails.append(p); print(f"Q-EXTENDED FAILS at p = {p:,}", flush=True)
    elif first2["jacobi_x"] == 1: first_is_residue += 1

print(f"\n{len(primes)} primes p ≡ 1 (mod 24) up to {N:,} tested exhaustively in {time.time()-t0:.1f} s")
print(f"Conjecture Q (ES-QP-TEST v1.0 admissibility, non-residue x): {len(fails)} failures: {[f['p'] for f in fails]}")
print(f"Q-failures as a share of R-primes: {len(fails)}/{R_count} = {100*len(fails)/max(1,R_count):.2f}%;  failures by band (×10⁵): {Counter(f['p']//100000 for f in fails)}")
print(f"Q-extended (any x in (p/4, 3p/4)): {len(ext_fails)} failures: {ext_fails}")
print(f"Primes whose first forcing x is a quadratic residue (excluded by the spec): {first_is_residue} of {len(primes)}")
print("Distribution of the first Q witness shift d_Q (spec admissibility):", sorted(first_dQ.items())[:12], "... max", max(first_dQ) if first_dQ else None)
json.dump(dict(N=N, primes=len(primes), R_primes=R_count, Q_failures=fails, Q_extended_failures=ext_fails, first_is_residue=first_is_residue,
               elapsed_s=round(time.time()-t0, 1)), open("q_attack_results.json", "w"), indent=1)
