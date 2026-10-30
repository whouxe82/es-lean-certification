"""Calibration of the q_attack implementation against the sealed ES-QP-TEST v1.0 pilot record (29 Oct 2026):
the 29 primes p ≡ 1 (mod 24) up to 1873 must give 10,884 eligible cells, 40 infinite thresholds, 161 witness cells,
Q holding at all 29. The sealed pilot implementations (qp_claude.py; GPT-DP-1.0.0) live under qp-test/ in this repository."""
import sys, math, os
sys.argv=['x','2000']
HERE=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE,'..','03-q-refutation','claude','q_attack.py')).read().split('primes = [p for p')[0])
ps=[p for p in range(25,1874,24) if is_prime(p)]
ok=0; ncells=0; inf=0; wit=0
for p in ps:
    found=False
    for x in range((p+3)//4,(3*(p-1))//4+1):
        if jacobi(x,p)!=-1: continue
        d=4*x-p; fac=factor(x); hist=histogram(fac,d)
        for c in cells(p,x,fac,hist):
            ncells+=1; inf+= c['M']=='inf'
            if c['forces']: wit+=1; found=True
    ok+=found
print(f"{len(ps)} primes; Q holds at {ok}; eligible cells {ncells}; infinite {inf}; witness cells {wit}  (expected 29 / 10884 / 40 / 161)")
