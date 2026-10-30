"""Q' Stage 1 — exploratory (NOT a census record; the sealed ES-QP-TEST implementations remain the record instruments).
Targets the hardest primes first: members of R (six square classes mod 840, every odd prime factor of p+1 ≡ 1 mod 4)
with the largest channel depth D(p) below N, plus the Ionascu–Wilson record primes.  For each, scans admissible x in
increasing order (nonresidue x only, as in ES-QP-TEST), builds H, K, cells, the divisor histogram, T, E and the exact
avoidance minimum M (Theorem E3), and reports the first energy witness: its mechanism, margin and "Q-depth" d_Q = 4x - p.
Also records, over the scanned window, how many firing channels are energy-forcing (the key ratio for the Monte Carlo stage).
Standard library only; exact integers. Set N and WINDOW below. Colab-safe (ignores stray argv)."""
import sys, math, time, json
from collections import Counter

N = 20_000_000          # census bound for selecting deep primes (20M: ~1 min, ~700 MB; 60M needs ~2 GB)
TOP = 150               # how many deepest R-primes to test
WINDOW = 4000           # keep scanning for a first witness up to d <= WINDOW
STATS = 400             # firing/forcing statistics are collected over d <= STATS only
EXTRA = [73, 1129, 1201, 21169, 118801, 8803369]   # Ionascu–Wilson record primes (tested regardless of R-membership)
if len(sys.argv) > 1 and sys.argv[1].isdigit(): N = int(sys.argv[1])
t0 = time.time()

M_ = (N + WINDOW) // 4 + 2
spf = list(range(M_))
for i in range(2, int(M_ ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, M_, i):
            if spf[j] == j: spf[j] = i

def factor(n):
    f = {}
    if n < M_:
        while n > 1:
            q = spf[n]; e = 0
            while n % q == 0: n //= q; e += 1
            f[q] = e
        return f
    q = 2
    while q * q <= n:
        while n % q == 0: f[q] = f.get(q, 0) + 1; n //= q
        q += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def is_prime(n):
    if n < M_: return n > 1 and spf[n] == n
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a % n == 0: continue
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True

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

def divisor_residues(fac, d):
    res = {1 % d}
    for q, e in fac.items():
        qm = q % d; pw = [1 % d]
        for _ in range(2 * e): pw.append(pw[-1] * qm % d)
        res = {r * w % d for r in res for w in pw}
    return res

def channel_depth(p):
    d = 3
    while d <= WINDOW and d < 2 * p:
        x = (p + d) // 4; R = divisor_residues(factor(x), d)
        if (-x) % d in R or (-p * x) % d in R: return d
        d += 4
    return None

def in_R(p):
    if p % 840 not in (1, 121, 169, 289, 361, 529): return False
    return all(q % 4 == 1 for q in factor(p + 1) if q != 2)

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

def q_cells(p, x):
    """all eligible cells at admissible x: list of dicts with channel, T, E, M, mechanism"""
    d = 4 * x - p; fac = factor(x)
    H = subgroup([q % d for q in fac], d); K = {h * h % d for h in H}
    # divisor histogram from exponents
    hist = Counter({1 % d: 1})
    for q, e in fac.items():
        qm = q % d; pw = [1 % d]
        for _ in range(2 * e): pw.append(pw[-1] * qm % d)
        new = Counter()
        for r, cnt in hist.items():
            for v in pw: new[r * v % d] += cnt
        hist = new
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
            M = M_formula(b, f, c, T); mech = "infinite-noncentral" if M == math.inf else "finite"
        out.append(dict(ch=ch, d=d, T=T, E=E, M=M, mech=mech, fires=hist.get(t, 0) > 0, K=len(K)))
    return out

def q_scan(p):
    """first energy witness over admissible x with d <= WINDOW; also firing/forcing counts over the window"""
    fires = forces = 0; first = None; admissible = 0
    d = 3
    while d <= WINDOW and d < 2 * p:
        x = (p + d) // 4
        if d > STATS and first is not None: break
        if jacobi(x, p) == -1:
            admissible += 1
            for c in q_cells(p, x):
                if d <= STATS and c["fires"]: fires += 1
                if c["E"] < c["M"]:
                    if d <= STATS: forces += 1
                    if first is None: first = dict(dQ=d, x=x, **{k: c[k] for k in ("ch", "T", "E", "M", "mech", "K")})
        d += 4
    return first, admissible, fires, forces

# ---- select targets: deepest R-primes below N ----
cand = []
for p in range(25, N + 1, 24):
    if not is_prime(p) or not in_R(p): continue
    cand.append((channel_depth(p) or 10 ** 9, p))
cand.sort(reverse=True)
targets = [p for _, p in cand[:TOP]]
print(f"R-primes below {N:,}: {len(cand):,}; deepest {TOP} selected (depth range {cand[min(TOP,len(cand))-1][0]}..{cand[0][0]}); setup {time.time()-t0:.1f}s")
print("R share of six-class primes below N:", round(len(cand) / max(1, sum(1 for p in range(25, N + 1, 24) if is_prime(p) and p % 840 in (1,121,169,289,361,529))), 4))

rows = []
for p in sorted(set(targets + [q for q in EXTRA if is_prime(q)])):
    D = channel_depth(p); first, adm, fires, forces = q_scan(p)
    rows.append(dict(p=p, inR=in_R(p), D=D, admissible_in_window=adm, firing_cells=fires, forcing_cells=forces, first_witness=first))
    fw = first and f"d_Q={first['dQ']} ch={first['ch']} {first['mech']} T={first['T']} E={first['E']} M={first['M']}"
    print(f"p={p:>10,} R={str(in_R(p)):5} D={D:>4} adm={adm:>4} fire={fires:>4} force={forces:>4} | {fw if first else 'NO WITNESS IN WINDOW'}")

noW = [r["p"] for r in rows if r["first_witness"] is None]
ratio = sum(r["forcing_cells"] for r in rows) / max(1, sum(r["firing_cells"] for r in rows))
print(f"\nprimes tested: {len(rows)}; no energy witness within d<={WINDOW}: {len(noW)} {noW}")
print(f"forcing/firing ratio over all tested windows: {ratio:.3f}; max d_Q among witnesses: {max((r['first_witness']['dQ'] for r in rows if r['first_witness']), default=None)}")
print(f"elapsed {time.time()-t0:.1f}s")
json.dump(rows, open("qprime_stage1.json", "w"), indent=1, default=str)
