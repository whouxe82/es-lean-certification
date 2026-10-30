"""Exact recomputations for the ES draft paper. Standard library only."""
import sys, json, math, time
from collections import Counter

# Set the census bound here. 5_000_000 runs in ~2 s; 60_000_000 (the paper's figure) in ~25 s and ~1 GB RAM.
N = 60_000_000
# When run from a terminal, an integer on the command line overrides N; Colab's own flags (e.g. "-f") are ignored.
if len(sys.argv) > 1 and sys.argv[1].isdigit():
    N = int(sys.argv[1])
t0 = time.time()

# smallest-prime-factor sieve to M = (N + 4000)//4 + 1 (x_d = (p+d)/4, d < 4000 cap)
DCAP = 4000
M = (N + DCAP) // 4 + 2
spf = list(range(M))
for i in range(2, int(M ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, M, i):
            if spf[j] == j:
                spf[j] = i

def factor(n):
    f = {}
    while n > 1:
        q = spf[n]
        e = 0
        while n % q == 0:
            n //= q; e += 1
        f[q] = e
    return f

def is_prime(n):
    if n < 2: return False
    if n < M: return spf[n] == n
    for q in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

def divisor_residues(fac, d):
    """set of residues mod d of all divisors of x^2, from exponents of x"""
    res = {1 % d}
    for q, e in fac.items():
        qm = q % d
        pw = [1 % d]
        for _ in range(2 * e):
            pw.append(pw[-1] * qm % d)
        res = {r * w % d for r in res for w in pw}
    return res

def depth(p):
    """least d (Type II, Type I, either) at which a channel fires; None if none below DCAP"""
    dII = dI = None
    d = 3
    while d < DCAP and d < 2 * p:
        x = (p + d) // 4
        fac = factor(x)
        R = divisor_residues(fac, d)
        tII = (-x) % d
        tI = (-p * x) % d
        if dII is None and tII in R: dII = d
        if dI is None and tI in R: dI = d
        if dII is not None and dI is not None: break
        d += 4
    D = min(v for v in (dII, dI) if v is not None) if (dII or dI) else None
    return D, dII, dI

# census over p ≡ 1 (mod 24)
hist = Counter(); histII = Counter(); histI = Counter()
count = 0; fail3 = 0; record = (0, 0)
for p in range(25, N + 1, 24):
    if not is_prime(p): continue
    count += 1
    D, dII, dI = depth(p)
    hist[D] += 1; histII[dII] += 1; histI[dI] += 1
    if D != 3: fail3 += 1
    if D is not None and D > record[0]: record = (D, p)

cum = 0; cumtab = []
for d in sorted(k for k in hist if k is not None):
    cum += hist[d]
    cumtab.append((d, hist[d], cum, cum / count))

# Mordell six classes = squares mod 840 coprime to 840 that are ≡ 1 mod 24? just list squares of units mod 840
units = [a for a in range(840) if math.gcd(a, 840) == 1]
sq = sorted({a * a % 840 for a in units})

# witnesses mentioned in the record, re-verified by the two-channel criterion
def channel_check(p, d):
    x = (p + d) // 4
    fac = factor(x) if x < M else None
    R = divisor_residues(fac, d)
    return {"x": x, "fac": fac, "ChI": ((-p * x) % d) in R, "ChII": ((-x) % d) in R}

def es_from_II(p, d):
    x = (p + d) // 4
    for a in range(1, x * x + 1):
        if x * x % a == 0 and a % d == (-x) % d:
            b = x * x // a
            Y = (a + x) // d; Z = (b + x) // d
            y, z = p * Y, p * Z
            assert 4 * x * y * z == p * (x * y + x * z + y * z)
            return (x, y, z)
    return None

wit = {}
for (p, d) in [(421, 27), (29, 3), (3049, 19), (3361, 39), (577, 39), (149, 7)]:
    wit[f"{p},{d}"] = channel_check(p, d)
# 577 example from the certification package: 4/577 = 1/154 + 1/2308 + 1/177716
assert 4 * 154 * 2308 * 177716 == 577 * (154 * 2308 + 154 * 177716 + 2308 * 177716)
# 528n+505 family: n=0 -> 505 composite; check the first prime members
fam = [528 * n + 505 for n in range(60) if is_prime(528 * n + 505)][:8]

out = {
    "N": N, "primes_1_mod_24": count, "fail_d3": fail3, "fail_d3_frac": fail3 / count,
    "record_depth": record, "cumulative": cumtab[:40],
    "histII": {str(k): v for k, v in sorted(histII.items(), key=lambda kv: (kv[0] is None, kv[0]))},
    "histI_small": {str(k): histI[k] for k in sorted(k for k in histI if k is not None)[:15]},
    "squares_mod_840": sq, "witnesses": wit, "family_primes": fam,
    "elapsed_s": round(time.time() - t0, 1),
}
json.dump(out, open("census.json", "w"), indent=1, default=str)
print(json.dumps({k: out[k] for k in ("N", "primes_1_mod_24", "fail_d3", "fail_d3_frac", "record_depth", "squares_mod_840", "family_primes", "elapsed_s")}, indent=1))
print("cum:", cumtab[:12])
print("witnesses:", json.dumps(wit, default=str))
