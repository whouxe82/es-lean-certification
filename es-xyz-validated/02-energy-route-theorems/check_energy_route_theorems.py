"""Independent checks of the new theorems in GPT's energy-route draft (29 Oct 2026).
Standard library only; exact integers. Written from the statements, without sight of GPT's code."""
import itertools, math, json
from functools import lru_cache

def is_prime(n):
    if n < 2: return False
    for q in range(2, int(n**0.5)+1):
        if n % q == 0: return False
    return True

def jacobi(a, n):
    assert n > 0 and n % 2 == 1
    a %= n; r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: r = -r
        a %= n
    return r if n == 1 else 0

def legendre(a, p): return jacobi(a, p)

def factor(n):
    f = {}; q = 2
    while q * q <= n:
        while n % q == 0: f[q] = f.get(q, 0) + 1; n //= q
        q += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def divisors(n):
    f = factor(n); ds = [1]
    for q, e in f.items():
        ds = [d * q**k for d in ds for k in range(e + 1)]
    return sorted(ds)

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

# ---------- Theorem 5: formula (9) vs brute force over orbit structure ----------
def M_formula(b, f, c, T):
    if (T - c) % 2 or T < c: return math.inf
    U = (T - c) // 2
    D = 2*b + f + c
    if D == 0: return 0 if T == 0 else math.inf
    q, r = divmod(U, D)
    r1 = min(r, b); r2 = min(max(r - b, 0), f); r3 = max(r - b - f, 0)
    return c + 4*D*q*q + 4*c*q + (8*q+2)*r1 + (8*q+4)*r2 + (8*q+6)*r3

def M_brute(b, f, c, T):
    # orbits: b pairs (k,k) energy 2k^2 mass 2k; f fixed bins mass 2m energy 4m^2; central mass 2n+1 energy (2n+1)^2 (n>=0, compulsory)
    @lru_cache(None)
    def best(i, mass):
        # i indexes orbits: first b pairs, then f fixed, then central
        if i == b + f + c:
            return 0 if mass == 0 else math.inf
        res = math.inf
        if i < b:
            for k in range(mass // 2 + 1): res = min(res, 2*k*k + best(i+1, mass - 2*k))
        elif i < b + f:
            for m in range(mass // 2 + 1): res = min(res, 4*m*m + best(i+1, mass - 2*m))
        else:
            for n in range((mass - 1) // 2 + 1):
                if 2*n + 1 <= mass: res = min(res, (2*n+1)**2 + best(i+1, mass - 2*n - 1))
        return res
    return best(0, T)

mism = 0; cases = 0
for b in range(5):
    for f in range(5):
        for c in (0, 1):
            for T in range(41):
                cases += 1
                if M_formula(b, f, c, T) != M_brute(b, f, c, T): mism += 1
print("Theorem 5 formula vs brute force:", cases, "cases,", mism, "mismatches")

# bounds (10) and collision threshold (11)
viol = 0
for b in range(5):
    for f in range(5):
        for c in (0,1):
            for T in range(41):
                M = M_formula(b,f,c,T); D = 2*b+f+c
                if M == math.inf or D == 0: continue
                if not (T*T/D <= M <= T*T/D + D - c): viol += 1
                U=(T-c)//2; q,r=divmod(U,D); r1=min(r,b); r2=min(max(r-b,0),f); r3=max(r-b-f,0)
                L = D*q*(2*q-1) + 2*c*q + 4*q*r + r2 + 2*r3
                if 2*L != M - T: viol += 1
                if (M == T) != (U <= b): viol += 1
print("bounds (10), threshold (11), Corollary 6 equality: violations =", viol)

# ---------- cell machinery for an actual prime ----------
def cells_for(p, x):
    d = 4*x - p
    fac = factor(x)
    H = subgroup([q % d for q in fac], d)
    K = subgroup([h*h % d for h in H], d)
    w = {}
    for a in divisors(x*x): w[a % d] = w.get(a % d, 0) + 1
    assert all(r in H for r in w)
    xinv = pow(x, -1, d)
    iota = lambda r: x*x*pow(r, -1, d) % d
    tI = (-p*x) % d; tII = (-x) % d
    cosets = []; seen = set()
    for h in H:
        if h in seen: continue
        C = {h*k % d for k in K}; seen |= C; cosets.append(C)
    out = []
    for C in cosets:
        for ch, t in (("I", tI), ("II", tII)):
            if t not in C: continue
            T = sum(w.get(r, 0) for r in C); E = sum(w.get(r, 0)**2 for r in C)
            orbit = {t, iota(t)}
            if x % d in orbit:
                M = math.inf
            else:
                rest = C - orbit
                b = sum(1 for r in rest if iota(r) != r) // 2
                f = sum(1 for r in rest if iota(r) == r and r != x % d)
                c = 1 if x % d in rest else 0
                M = M_formula(b, f, c, T)
            out.append(dict(channel=ch, d=d, cell=sorted(C), T=T, E=E, M=M, target=t, K=len(K), H=len(H)))
    return out

# 577 certificate
res577 = [c for c in cells_for(577, 154) if c["channel"] == "II" and c["target"] == 2]
print("p=577, x=154, d=39 channel II cell:", res577)
# brute force M directly for that cell by enumeration
# p = 433 example
x = 113; p = 433; d = 19
print("p=433: (113|433) =", legendre(113, 433), " H =", subgroup([q % d for q in factor(x)], d), " cells:", cells_for(433, 113))

# ---------- Theorem 10: p ≡ 1 mod 24, p mod 7 in {3,5}: d = 7, finite margin >= 6; p mod 7 == 6: M = inf ----------
bad = 0; n10 = 0
for p in range(25, 20000, 24):
    if not is_prime(p) or p % 7 not in (3, 5, 6): continue
    x = (p + 7) // 4
    assert legendre(x, p) == -1
    cs = [c for c in cells_for(p, x) if c["channel"] == "I"]
    assert len(cs) == 1; c = cs[0]; n10 += 1
    if p % 7 == 6:
        if c["M"] != math.inf: bad += 1
    else:
        if not (c["M"] != math.inf and c["M"] - c["E"] >= 6): bad += 1
print("Theorem 10 checked on", n10, "primes < 20000; violations:", bad)

# ---------- Theorem 11: p mod 5 in {2,3}: d = 15, channel I, M = inf ----------
bad = 0; n11 = 0
for p in range(25, 20000, 24):
    if not is_prime(p) or p % 5 not in (2, 3): continue
    x = (p + 15) // 4
    assert legendre(x, p) == -1 and x % 15 in (7, 13)
    cs = [c for c in cells_for(p, x) if c["channel"] == "I"]
    n11 += 1
    if len(cs) != 1 or cs[0]["M"] != math.inf or cs[0]["T"] == 0: bad += 1
print("Theorem 11 checked on", n11, "primes < 20000; violations:", bad)

# ---------- Theorem 9: d | p+1, d ≡ 3 mod 4 ⇒ channel I target central, M = inf; converse ----------
bad = 0; n9 = 0
for p in range(25, 2000, 24):
    if not is_prime(p): continue
    for x in range((p+3)//4, 3*(p-1)//4 + 1):
        if legendre(x, p) != -1: continue
        d = 4*x - p
        central = ((-p*x) % d == x % d)
        if central != ((p+1) % d == 0): bad += 1
        if central:
            n9 += 1
            cs = [c for c in cells_for(p, x) if c["channel"] == "I"]
            if len(cs) != 1 or cs[0]["M"] != math.inf: bad += 1
print("Theorem 9 central-target characterisation on p < 2000:", n9, "central cases; violations:", bad)

# ---------- Theorem 13: classify every infinite threshold for p < 3000 ----------
bad = 0; counts = {"I-central": 0, "I-15": 0, "II-K1": 0}
for p in range(25, 1500, 24):
    if not is_prime(p): continue
    for x in range((p+3)//4, 3*(p-1)//4 + 1):
        if legendre(x, p) != -1: continue
        d = 4*x - p
        for c in cells_for(p, x):
            inf = c["M"] == math.inf
            mech = None
            if c["channel"] == "I" and (p+1) % d == 0: mech = "I-central"
            elif c["channel"] == "I" and d == 15 and p % 5 in (2,3): mech = "I-15"
            elif c["channel"] == "II" and c["K"] == 1: mech = "II-K1"
            if inf != (mech is not None): bad += 1
            if inf and mech: counts[mech] += 1
print("Theorem 13 classification on p < 1500:", counts, "violations:", bad)

# ---------- Theorem 4 reduction cases ----------
def check(p, x, y, z): return 4*x*y*z == p*(x*y + x*z + y*z)
bad = 0
for p in range(3, 5000):
    if not is_prime(p): continue
    if p == 2: continue
    if p % 3 == 2: k = (p+1)//3; ok = check(p, p, k, p*k)
    elif p % 4 == 3: t = (p+1)//4; ok = check(p, t, 2*p*t, 2*p*t)
    elif p % 24 == 13:
        x = (p+3)//4; a = 2; b = x*x//2; ok = check(p, x, p*(x+a)//3, p*(x+b)//3) and (x+a) % 3 == 0 and (x+b) % 3 == 0
    else: ok = (p % 24 == 1)
    if not ok: bad += 1
print("Theorem 4 case split, odd primes < 5000: violations", bad)

# ---------- family (17) ----------
bad = 0
for n in range(0, 200):
    p = 528*n + 505; r = n + 1; h = 23*n + 22
    if not check(p, 132*r, 11*p*r, 12*p*r) or not check(p, 11*h, 12*h, 132*p*h): bad += 1
    if not (p/4 < 11*h < p/2 < 12*h < 3*p/4): bad += 1
print("family (17) identities and interval, n < 200: violations", bad)
print("4·11·12 =", 4*11*12, " 23^2-1 =", 23**2 - 1)

# ---------- Theorem 14 sanity: p ≡ 1 mod lcm(24, d's) ⇒ (x|p)=+1 ----------
D0 = [3, 7, 11, 15, 19]; B0 = math.lcm(24, *D0); bad = 0; n14 = 0
for p in range(1 + B0, 40*B0, B0):
    if not is_prime(p): continue
    n14 += 1
    for d in D0:
        if legendre((p+d)//4, p) != 1: bad += 1
print("Theorem 14 on", n14, "primes p ≡ 1 mod", B0, ": violations", bad)
