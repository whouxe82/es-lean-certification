"""Claude's cross-check of all 1,224 draws (1,979 eligible cells) in GPT's ES-MC-1.0.0 results: mass, energy, minimum,
force verdict and |H|, |H^2| recomputed independently. Result on 29 Oct 2026: 0 mismatches.
Usage: unzip the results zip into this folder, then python3 -I claude_crosscheck_of_gpt_draws.py"""
import json, sys, math
sys.argv=['x','50000']
import os
HERE=os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(HERE,'..','03-q-refutation','claude','q_attack.py')).read().split('primes = [p for p')[0])
# unzip ES_MC_results_2026-10-29.zip here first
draws=[json.loads(l) for l in open(os.path.join(HERE,'draws.jsonl'))]
mism=0; cells_checked=0; forces_gpt=0; forces_mine=0; Hmis=0
for dr in draws:
    p=dr['p']; x=dr['x']; d=4*x-p; fac=factor(x); hist=histogram(fac,d)
    mine={c['ch']:c for c in cells(p,x,fac,hist)}
    H=subgroup([q%d for q in fac],d); K={h*h%d for h in H}
    if len(H)!=dr['result']['H_order'] or len(K)!=dr['result']['H_squared_order']: Hmis+=1
    for c in dr['result']['cells']:
        cells_checked+=1
        m=mine.get(c['channel'])
        gM = math.inf if c['minimum'] in (None,'inf','Infinity') or c['threshold_kind']!='finite' else c['minimum']
        if m is None or m['T']!=c['mass'] or m['E']!=c['energy'] or (m['M']!=('inf' if gM==math.inf else gM)) or bool(m['forces'])!=bool(c['force']):
            mism+=1
            if mism<=5: print("MISMATCH",p,x,c['channel'],c['mass'],c['energy'],c['minimum'],c['force'],"| mine",m)
        forces_gpt+=bool(c['force'])
    if len(mine)!=len(dr['result']['cells']): mism+=1; print("cell-count mismatch",p,x,len(mine),len(dr['result']['cells']))
print("draws",len(draws),"cells checked",cells_checked,"mismatches",mism,"H/K order mismatches",Hmis,"forcing cells (GPT)",forces_gpt)
