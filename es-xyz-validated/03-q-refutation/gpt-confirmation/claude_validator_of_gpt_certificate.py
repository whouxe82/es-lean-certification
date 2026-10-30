"""Claude's independent validator of GPT's ES-Q-REF-1 refutation certificate at p = 66,361.
Re-derives the admissible and firing sets and checks all 54 explicit avoiding allocations (cell membership, mass, pair symmetry,
parities, zero at target, energy = M <= E, H/H^2 orders). Written independently of GPT's independent_validate.py.
Usage: unzip the evidence zip into ./ev, then python3 -I claude_validator_of_gpt_certificate.py"""
import json, sys, math
from collections import Counter
sys.argv=['x','70000']
import os
HERE=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE,'..','claude','q_attack.py')).read().split('primes = [p for p')[0])
# unzip ES_Q_REF_1_Evidence_2026-10-30.zip into ./ev first
c=json.load(open(os.path.join(HERE,'ev','verification_work','run_001','refutation_certificate.json')))
p=c['p']
# 1. admissible set and firing set
adm=[x for x in range((p+3)//4,(3*(p-1))//4+1) if jacobi(x,p)==-1]
assert adm==sorted(c['admissible_x']), "admissible set differs"
fire=[]
for x in adm:
    d=4*x-p; h=histogram(factor(x),d)
    if h.get((-x)%d,0) or h.get((-p*x)%d,0): fire.append(x)
assert fire==sorted(c['firing_x']), "firing set differs"
# 2. each explicit profile: in cell, mass, pair symmetry, parities, zero at target, energy <= E; and E,T,M vs mine
mine={}
for x in fire:
    d=4*x-p; fac=factor(x); h=histogram(fac,d)
    for cc in cells(p,x,fac,h): mine[(x,cc['ch'])]=cc
bad=0; checked=0
for cell in c['cells']:
    x=cell['x']; d=cell['d']; ch=cell['channel']; C=set(cell['residues']); t=cell['target']
    v=Counter({r:k for r,k in cell['allocation']})
    iota=lambda r: x*x*pow(r,-1,d)%d
    ok = set(v)<=C and all(k>=0 and isinstance(k,int) for k in v.values())
    ok &= sum(v.values())==cell['T']
    ok &= all(v[r]==v[iota(r)] for r in C)
    xd=x%d
    ok &= (v[xd]%2==1 and v[xd]>0) if xd in C else True
    ok &= all(v[r]%2==0 for r in C if iota(r)==r and r!=xd)
    ok &= v[t]==0
    en=sum(k*k for k in v.values()); ok &= en<=cell['E']
    m=mine[(x,ch)]
    ok &= (m['T'],m['E'],m['M'])==(cell['T'],cell['E'],cell['M']) and en==cell['M'] and m['M']<=m['E']
    # cell membership = coset of K in H containing the target
    fac=factor(x); H=subgroup([q%d for q in fac],d); K={h*h%d for h in H}
    ok &= C=={t*k%d for k in K} and len(H)==cell['H_order'] and len(K)==cell['H_squared_order']
    checked+=1; bad+= (not ok)
print("admissible",len(adm),"firing",len(fire),"cells checked",checked,"invalid",bad)
print("every non-firing x: both target bins empty by construction of the firing set -> actual profile avoids; M<=E.")
