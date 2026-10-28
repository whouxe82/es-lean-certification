from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

BASE=Path(__file__).resolve().parent
OUT=BASE/'output'
OUT.mkdir(exist_ok=True)
status_path=BASE/'proof_status.json'
status=json.loads(status_path.read_text()) if status_path.exists() else {}
plt.rcParams.update({'font.family':'DejaVu Sans','pdf.fonttype':42,'svg.fonttype':'none'})
COL={'ink':'#182B3A','muted':'#5F7280','line':'#99ABB4','paper':'#FAFBFC',
     'checked':'#E3F3EC','checked_edge':'#2E7861','open':'#FFF1D5','open_edge':'#B47718',
     'partial':'#EAF0F7','partial_edge':'#526F96','imported':'#EEE9F8','imported_edge':'#74639B',
     'stop':'#F8E8E5','stop_edge':'#A45B4F'}
fig,ax=plt.subplots(figsize=(15,11.6))
fig.patch.set_facecolor(COL['paper'])
ax.set_xlim(0,15); ax.set_ylim(0,11.6); ax.axis('off')

def card(x,y,w,h,title,body,kind='partial',badge=None,title_size=12.5,body_size=10.5):
    edge=COL[kind+'_edge']; face=COL[kind]
    p=FancyBboxPatch((x-w/2,y-h/2),w,h,boxstyle='round,pad=0.02,rounding_size=0.09',
                    facecolor=face,edgecolor=edge,linewidth=1.35,
                    linestyle=(0,(4,3)) if kind=='open' else 'solid',zorder=3)
    ax.add_patch(p)
    top=y+h/2
    if badge:ax.text(x-w/2+.17,top-.16,badge.upper(),ha='left',va='top',fontsize=8.1,
                    fontweight='bold',color=edge,zorder=4)
    ty=top-(.43 if badge else .22)
    ax.text(x,ty,title,ha='center',va='top',fontsize=title_size,fontweight='bold',color=COL['ink'],zorder=4)
    ax.text(x,ty-.39,body,ha='center',va='top',fontsize=body_size,color=COL['ink'],
            linespacing=1.43,zorder=4)
    return (x,y,w,h)

def arrow(a,b,label=None,dashed=False,color=None,rad=0):
    color=color or COL['line']
    ax.add_patch(FancyArrowPatch(a,b,arrowstyle='-|>',mutation_scale=12,
                 linewidth=1.45,color=color,linestyle=(0,(4,3)) if dashed else 'solid',
                 connectionstyle=f'arc3,rad={rad}',zorder=1))
    if label:
        ax.text((a[0]+b[0])/2,(a[1]+b[1])/2,label,ha='center',va='center',fontsize=8.8,
                color=COL['muted'],bbox={'facecolor':COL['paper'],'edgecolor':'none','pad':2},zorder=2)

ax.text(.45,11.20,'ERDŐS–STRAUS',fontsize=22,fontweight='bold',color=COL['ink'],ha='left')
ax.text(.45,10.86,'A proof dependency map — certified restrictions and the remaining existence gap',
        fontsize=12.1,color=COL['muted'],ha='left')
ax.text(14.55,11.18,'28 OCTOBER 2026',fontsize=9.2,color=COL['muted'],ha='right')
ax.text(14.55,10.89,status.get('toolchain','Lean certification in progress'),fontsize=9.0,
        color=COL['muted'],ha='right')

card(7.5,9.90,6.8,1.20,'ES CONJECTURE — OPEN',
     r'For every integer $n\geq2$, positive integers $x,y,z$ satisfy'
     '\n'+r'$4/n=1/x+1/y+1/z$.','open',title_size=13.0,body_size=11)

card(3.65,8.12,5.75,1.20,r'$H_D$ — DYADIC EXISTENCE',
     'Every prime p ≡ 1 (mod 4) has a dyadic Type II source.\nUnproved; this bridge route is now inactive.','open',body_size=10.8)
card(11.35,8.12,5.75,1.20,r'$H_N$ — NONRESIDUE EXISTENCE',
     'Every prime p ≡ 1 (mod 4) has a nonresidue denominator\ninside p/4 < x < 3p/4. Active existence target.','open',body_size=10.8)
arrow((4.7,8.74),(6.0,9.29),dashed=False,color=COL['checked_edge'])
arrow((10.3,8.74),(9.0,9.29),dashed=False,color=COL['checked_edge'])
ax.text(7.5,8.91,status.get('implications','Conditional implications await kernel check'),
        ha='center',va='center',fontsize=9.2,color=COL['checked_edge'],
        bbox={'facecolor':COL['paper'],'edgecolor':'none','pad':2})

ax.plot([.7,14.3],[6.92,6.92],color=COL['open_edge'],linestyle=(0,(5,4)),linewidth=1.2,zorder=0)
ax.text(7.5,6.93,'MISSING: a uniform existence / selection theorem',
        ha='center',va='center',fontsize=11.4,fontweight='bold',color=COL['open_edge'],
        bbox={'facecolor':COL['paper'],'edgecolor':'none','pad':7})

xs=[2.05,5.68,9.31,12.94]
width=3.12
nodes=[
('structure','TYPE II CONSTRUCTION',
 'Positive integer source triples\nOriginal bridge B1: exact gate\nCharacter conclusion: separate',
 'Supporting theorem'),
('descent','B4 RETURN + DESCENT',
 'Four rational steps, exact gate\nt = 1 and δ odd\nNo new dyadic endpoints',
 'Method restriction'),
('matching','INTEGRAL MATCHING',
 'Orientation and inverse lemmas\nFull graph statement: see ledger\nNo universal selector supplied',
 'Formalization boundary'),
('forcing','SQUARE-CLASS FORCING',
 'Complement-preserving quotient\nFinite energy certificate at 577\nUniform choice of x remains open',
 'Sufficient criterion')]
for x,(key,title,body,badge) in zip(xs,nodes):
    cfg=status.get(key,{})
    card(x,5.43,width,2.05,title,cfg.get('body',body),cfg.get('kind','partial'),
         badge=cfg.get('badge',badge),title_size=11.4,body_size=10.0)
arrow((2.05,6.47),(2.75,7.49),dashed=True)
arrow((12.94,6.47),(12.0,7.49),dashed=True)
ax.text(7.5,6.64,'B4 and matching restrict methods; they do not establish source existence.',ha='center',fontsize=8.8,color=COL['muted'])

card(3.0,2.88,4.5,1.46,'FOUNDATIONS',
     status.get('foundations','Integer ES: polynomial ⇔ fraction identity\nScaling and reduction to primes\nOpen hypotheses are definitions, not axioms'),
     status.get('foundation_kind','partial'),badge='Common trunk',title_size=11.8,body_size=10.0)
card(8.00,2.88,4.55,1.46,'MATHLIB DEPENDENCIES',
     'Dirichlet and quadratic reciprocity\nGroups, divisibility and finite sets\nImported proofs; exact versions pinned',
     'imported',badge='Established formal mathematics',title_size=11.8,body_size=10.0)
card(12.45,2.88,3.45,1.46,'REMAINING TRANSLATION',
     status.get('pending','General B1 character application\nComplete finite obstruction files\nUniform analytic existence bound'),
     'partial',badge='Not certified by this run',title_size=10.9,body_size=9.7)
arrow((2.0,3.63),(2.05,4.39))
arrow((4.0,3.63),(5.68,4.39))
arrow((8.0,3.63),(9.31,4.39),color=COL['imported_edge'])
arrow((9.9,3.63),(12.94,4.39),color=COL['imported_edge'],rad=.07)

ax.text(.65,1.67,'HOW TO READ THIS MAP',fontsize=9.2,fontweight='bold',color=COL['ink'])
legend=[('checked','Kernel checked'),('imported','Imported formal theorem'),
        ('partial','Partial / not yet formalized'),('open','Open universal assertion')]
for i,(kind,label) in enumerate(legend):
    x=.7+i*3.55
    ax.add_patch(FancyBboxPatch((x,1.13),.20,.20,boxstyle='round,pad=0.01,rounding_size=0.025',
                   facecolor=COL[kind],edgecolor=COL[kind+'_edge']))
    ax.text(x+.32,1.23,label,ha='left',va='center',fontsize=9.7,color=COL['ink'])
ax.text(.65,.70,'Solid arrows: established dependencies or conditional implications.  '
        'Dashed arrows: a missing existence / selection step.',fontsize=9.5,color=COL['muted'])
ax.text(.65,.39,'A certified conditional theorem does not prove that its premises occur.  '
        'The companion ledger lists exact Lean statements and remaining gaps.',fontsize=9.5,color=COL['muted'])
fig.subplots_adjust(left=0,right=1,bottom=0,top=1)
fig.savefig(OUT/'ES_Formal_Proof_Map_2026-10-28.pdf',bbox_inches=None)
fig.savefig(OUT/'ES_Formal_Proof_Map_2026-10-28.png',dpi=180,bbox_inches=None)
plt.close(fig)
print('Wrote proof-map PDF and PNG.')
