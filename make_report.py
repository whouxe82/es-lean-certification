from pathlib import Path
import json, html
from reportlab.pdfgen import canvas
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle, PageBreak
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib.enums import TA_LEFT

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'output'
OUT.mkdir(exist_ok=True)
status=json.loads((ROOT/'proof_status.json').read_text())
pdfmetrics.registerFont(TTFont('DejaVu','/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf'))
pdfmetrics.registerFont(TTFont('DejaVu-Bold','/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf'))
pdfmetrics.registerFontFamily('DejaVu',normal='DejaVu',bold='DejaVu-Bold',italic='DejaVu',boldItalic='DejaVu-Bold')
styles=getSampleStyleSheet()
styles.add(ParagraphStyle(name='BodyES',fontName='DejaVu',fontSize=9.2,leading=13.8,spaceAfter=8,textColor=colors.HexColor('#203443')))
styles.add(ParagraphStyle(name='TitleES',fontName='DejaVu-Bold',fontSize=23,leading=28,spaceAfter=12,textColor=colors.HexColor('#173547')))
styles.add(ParagraphStyle(name='HeadES',fontName='DejaVu-Bold',fontSize=14,leading=19,spaceBefore=11,spaceAfter=9,textColor=colors.HexColor('#173547')))
styles.add(ParagraphStyle(name='SmallES',parent=styles['BodyES'],fontSize=8,leading=11.5,spaceAfter=5))
styles.add(ParagraphStyle(name='MathES',parent=styles['BodyES'],fontSize=10,leading=16,leftIndent=12,spaceBefore=4,spaceAfter=10))
story=[]
def p(t,style='BodyES'): story.append(Paragraph(t,styles[style]))
def h(t): p(t,'HeadES')
def page(): story.append(PageBreak())
def table(rows,widths):
    cells=[[Paragraph(str(v),styles['SmallES']) for v in row] for row in rows]
    t=Table(cells,colWidths=widths,hAlign='LEFT')
    t.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#E8EFF3')),('VALIGN',(0,0),(-1,-1),'TOP'),('BOX',(0,0),(-1,-1),.5,colors.HexColor('#CAD6DC')),('INNERGRID',(0,0),(-1,-1),.35,colors.HexColor('#D9E2E7')),('LEFTPADDING',(0,0),(-1,-1),8),('RIGHTPADDING',(0,0),(-1,-1),8),('TOPPADDING',(0,0),(-1,-1),7),('BOTTOMPADDING',(0,0),(-1,-1),6)]))
    story.append(t);story.append(Spacer(1,9))
def url(label,u): return f'<link href="{html.escape(u,quote=True)}" color="#245F8B">{html.escape(label)}</link>'

p('Erdős–Straus<br/>Formal certification review','TitleES')
p('28 October 2026 · Includes the supplied Claude review · Dated formal-certification round','SmallES')
p('<b>Result:</b> Lean accepted the full integral matching theorem and the source-level B4 restriction, including its exact dyadic overlap with B1. The supporting declarations are listed below. Neither H_D, H_N, nor the Erdős–Straus conjecture has been proved. No universal witness-selection theorem has been obtained.')
p('This is an upgrade in proof assurance and a sharper record of method limits. It is not evidence that the missing all-prime existence assertion is close to resolution. No change to the user’s charter has been made.')
h('Certification ledger')
table([
['Area','Actual result and boundary'],
['Foundations','Positive-denominator semantics, scaling, prime reduction, and the conditional implications H_D ⇒ ES and H_N ⇒ ES. The hypotheses themselves remain definitions.'],
['B1 and B4','Positive rational maps, exact integer-return gates, literal fourfold iteration, norm construction, and dyadic endpoint equality. The general B1 nonresidue argument is not formalized.'],
['B4 descent','Original source + B4 gate ⇒ t=1 and δ odd. Dyadic δ ⇒ δ=t=1, B1 eligibility, and exactly the same B1/B4 endpoint. Full norm recurrence and parity also checked.'],
['Matching',status.get('matching_report','Formal orientation and inverse lemmas are checked; the full graph theorem is not certified in this package.')],
['Finite forcing','Abstract square-subgroup quotient criterion and finite energy theorem. At p=577, the actual divisor histogram has energy12 and exact avoidance minimum14; a target divisor is forced. No uniform selector.'],
['Existing family','Previously studied p=528n+505 family, positivity, nonresidue endpoint, and prime infinitude certified. Retained as a regression and dependency check; no new family search or coverage claim.'],
['Literature replay','A documented compatibility port of an existing positive ES constructor; aligned Type II algebra and Pell dictionary; imported Dirichlet and reciprocity dependencies audited.']
],[103,402])
p(status.get('audit_summary','Final audit receipt is included in the source archive.'),'SmallES')
p('The supplied Claude replay is recorded as an external reviewer report. Its stated Python hashes and assertion replay are not a substitute for, or a claim about, the separate Lean build performed here.','SmallES')

page();p('The central certified restriction','TitleES')
p('Let p, δ, r, s, t be positive integers with gcd(δ,s)=1, δ≤s, and let p=4k+1. A normalized source satisfies')
p('4δrst = pt + δ + s.','MathES')
p('Set d=4δrs−p and 4C=pd+1. Lean proves the existence and needed positivity of these parameters. The B1 endpoint and its exact integer-return condition are')
p('X=k+δrt, &nbsp; B1=(X, Xs/t, pXs/δ),<br/>B1 has positive integer coordinates ⇔ δt divides k.','MathES')
p('For T(x,y,z)=((y+pk)/p, x(y+pk)/y, z(y+pk)/y), four rational steps from the stated source orientation yield')
p('B4=(tC/s, tC/δ, pC),<br/>B4 has positive integer coordinates ⇔ 4δs divides d²−1.','MathES')
p('This is a theorem about integer endpoints of a rational path. It does not assert that its intermediate points are integers. The one-step matching result and a rational four-step return therefore concern different graphs.')
h('Source → norm → descent → restriction')
p('From the B4 gate, the proof constructs a positive integer m with d²−1=4mδs. Together with dt=δ+s this gives')
p('(δ+s)² = t²(4mδs+1).','MathES')
p('The Vieta companion is (4mt²−2)δ−s. When t&lt;δ, it is positive and strictly smaller than δ; the norm, coprimality, and divisibility conditions survive. Strong induction reaches the terminal case, which forces t=1. The original congruence d≡3 (mod4) then forces δ odd. These premises are derived from the source; the theorem does not assume its conclusion.')
p('<b>Certified conclusion:</b> every B4-eligible normalized source has t=1 and odd δ. If δ=2ʲ for a natural j, then δ=t=1. Its B1 gate already holds, and the entire B4 endpoint equals its B1 endpoint. Thus this exact B4 construction adds no dyadic endpoints.')
p('Main declarations: ESDescent.b4_source_restriction; b4_dyadic_no_rescue; normalizedII_b4_dyadic_no_rescue; b4_dyadic_endpoints_equal. The gate equivalences and fourfold map are in ESBridge. Exact machine statements and receipts are in the archive.','SmallES')
h('Classification, not a universal normalization algorithm')
p('For c=4m−2, every positive ordered terminal pair is generated from (1,c) by (a,b) ↦ (b,cb−a). The required sum modulo4 selects even indices. This descent classifies eligible shapes; it does not produce a new source for every fixed prime p. No primality assumption is needed for the source-level restriction itself.')

page();p('Integral matching: exact scope','TitleES')
p(status.get('matching_detail','The global matching formalization is being assembled. Only the checked component lemmas may be claimed until the aggregate kernel audit succeeds.'))
h('The graph being discussed')
p('Fix a prime p=4k+1. Vertices are positive integer ES denominator triples, identified up to coordinate permutation. Include a directed edge when some ordering of a source triple is sent by the literal rational map T to an integer target triple. The underlying undirected graph retains those edges. This is the graph of this specific transformation, not the graph of every algebraic move or every shared denominator.')
h('Arithmetic classification precedes graph language')
p('The polynomial ES identity forces at least one denominator to be divisible by p. All three cannot be: dividing them by p would produce three positive unit fractions summing to4. Thus a prime-input solution is Type I (one p-divisible denominator) or Type II (two). The first transformed coordinate forces the pivot to be p-divisible.')
p('A Type I source has no integral outgoing edge. For its only possible pivot, the transformed first coordinate is divisible by p; integrality would force the other transformed coordinates divisible by p as well, contradicting the preceding bound. This argument is arithmetic; quadratic reciprocity is not needed.')
h('Normalization is proved, not assumed')
p('For an arbitrary Type II triple (x,pa,pb), order a≤b. Factoring a and b by their gcd gives coprime δ,s. The reduced ES equation forces δs to divide x, so x=δrs. Primality and p∤x then force the remaining common factor to be rt. This derives the normalized source equation and all positive coordinates used by the bridge lemmas. The theorem does not start by assuming the normal form exists.')
h('Why at most one neighbor can remain')
p('The exact opposite-pivot obstruction excludes the larger p-divisible pivot. Swapping the two other coordinates only permutes the output, so an arbitrary Type II vertex has at most one outgoing neighbor. A valid image’s distinguished first coordinate lies below p/2. A positive ES triple cannot have two denominators below p/2, so the target determines that coordinate uniquely.')
p('The ordered rational inverse then determines its source, up to the harmless swap of the other coordinates. Hence an arbitrary Type I target has at most one incoming neighbor. All edges run Type II→Type I, so incoming and outgoing possibilities cannot create an extra neighbor at one vertex. The full graph theorem requires this last permutation assembly, not merely a statement about normalized sources.')
p('<b>Research consequence:</b> the matching theorem closes integral iteration of this one map and its inverse as a general normalization strategy. It does not exclude rational intermediate points, other transformations, or other source selectors. B4’s separate descent closes its proposed dyadic repair mechanism; the universal H_D and H_N propositions are not refuted.')
p('Main declarations: ES.MatchingGraph.solutionGraph_neighbors_unique, degree_at_most_one, no_self_edge, and directed_iff_literal. They use actual normalization and edge classification, with no unproved classification premise. The final receipt binds these statements to the delivered source and clean build.','SmallES')

page();p('Disposition of Claude’s review','TitleES')
table([
['Review point','Decision for this deliverable'],
['Reciprocity dependency','Accepted as audited established mathematics. The exact installed Legendre/Jacobi reciprocity declarations, Jacobi periodicity, and the nonsquare criterion were checked and their axiom dependencies printed. This does not certify every informal application.'],
['Character statements','The existing family’s endpoint_nonresidue and endpoint_HN_witness are actually formalized. General B1 character transfer and other earlier character arguments remain ordinary mathematical proofs with an audited dependency; they are not labeled Lean-certified.'],
['Infinite families','Stop generating more. The completed family formalization documents correctness and imported infinitude, not progress on universality. Infinite soluble subfamilies do not imply all primes are covered.'],
['H_D disposition','Retain as an unrefuted mathematical hypothesis, but deprioritize this bridge-based route. The p=3049 obstruction rejects universally eligible dyadic selection, not existence of every dyadic source. B4 cannot repair that route.'],
['Selector failures','The prior p=12601 minimum-source obstruction and p=3361 support-graph failure remain exact bounded claims from the earlier notebook. They are not silently upgraded to Lean certificates in this package.'],
['Novelty','No priority claim. The classical Elsholtz–Tao parameters already contain the B4 endpoint scale and its congruence intersection. The rational-iteration interpretation is a description derived here, not evidence of novelty.'],
['Labor provenance','Six parallel tasks were configured as GPT-6 Astra with extra-high reasoning. That is an orchestration record, not cryptographic model attestation. Mathematical replay verifies proof artifacts, not the identity or effort of their authors.'],
['Round numbering','Use “28 October 2026 formal-certification round.” Folder names round_z4/round_z5 are internal labels and do not establish approved charter numbering. No charter edit is included.']
],[110,395])
h('What the failures do and do not establish')
p('The failures restrict particular selectors and transformations; they do not prove H_N, H_D, or ES false or unprovable. A sequence of failed methods also does not establish a general limitation of language models. Shared source definitions were settled before dependent modules were assembled; B4 descent does not require the matching theorem. The matching obstruction is arithmetic and does not itself require quadratic reciprocity.')
p('The formal definitions H_D and H_N here quantify over primes p≡1 (mod4); their implications to ES are checked. The proposed next analytic target is restricted to the active domain p≡1 (mod24). Reduction of the stronger witness hypotheses to that narrower domain is not itself certified in this package.','SmallES')

page();p('Prior formal mathematics and provenance','TitleES')
p('The literature/source audit compared theorem statements, parameter dictionaries, toolchain pins, and proof dependencies. “No matching declaration located” is a bounded search result, not proof of absence or novelty.')
h('Already formalized foundations')
p('Dirichlet’s theorem was proved long before this work and has existing machine formalizations: '+url('Harrison, HOL Light, JFR2(1), 2009','https://jfr.unibo.it/article/view/1558')+'; '+url('Eberl, Isabelle AFP, 2017','https://isa-afp.org/entries/Dirichlet_L.html')+'; and '+url('Loeffler–Stoll, Lean/Mathlib, AFM2025','https://afm.episciences.org/15954')+'. This project imports Mathlib’s theorem; it does not newly prove Dirichlet. The exact installed API is Nat.setOf_prime_and_eq_mod_infinite.')
p('The terminal norm has a classical Pell dictionary: put A=2m−1, X=s−Aδ, Y=δ. Then X²−(A²−1)Y² equals δ²+s²−(4m−2)δs. This identity is checked locally. Mathlib’s Pell.eq_pell and Pell.yn_succ_succ were inspected and their axioms audited. The ES source-to-norm descent is an additional statement; a Pell citation alone does not supply it.')
h('ES-specific formal source comparisons')
p(url('carlok/erdos-straus-offset-lean','https://github.com/carlok/erdos-straus-offset-lean')+' at commit aa79d27…: an existing positive natural-denominator ES constructor was replayed via a documented partial port from Lean4.34.0 to4.19.0. Statements were retained; import, instance, and renamed-lemma compatibility edits are listed. This is not an original-toolchain replay of the whole repository.')
p(url('creelie/ErdosProblem1','https://github.com/creelie/ErdosProblem1')+' at commit8036770…: its Type II rational identity matches our equation exactly under (n,u,v,a,α)=(p,δ,s,t,r). A local aligned proof is checked. The upstream theorem does not include positivity, gcd normalization, or uniform existence. Its analytic paper is not thereby formally certified.')
p(url('KokunoYumeto/erdos-straus-foundation','https://github.com/KokunoYumeto/erdos-straus-foundation')+' at commit d20b32e…: source and selected author receipts were inspected. Rational shell factorization and complement identities were rederived locally. The full archive was not replayed; some additional certificate files use native_decide and are outside this package’s policy.')
h('Classical and recent papers')
p(url('Elsholtz–Tao, Proposition1.9 and Section10','https://arxiv.org/abs/1107.1010')+' give the classical Type II class p≡−e (mod4ab) and Type I class p≡−1/e (mod4ab), with their parameter conditions. Requiring e²≡1 (mod4ab) makes the classes coincide; their Type I scale is (pe+1)/(4ab). This identifies the B4 endpoint in established coordinates.')
p(url('Chamberland, Integers26(2026), A42','https://math.colgate.edu/~integers/aa42/aa42.pdf')+' is a genuine Type II characterization, not a universal existence theorem. The primary '+url('arXiv record2609.09204','https://arxiv.org/abs/2609.09204')+' explicitly marks Jiang’s v2 withdrawn, with “some errors”; this independently resolves the uncertainty in Claude’s review. It is not used as support.')
p('The archive’s literature report retains exact commits, selected CI/API receipts, copied-source license, statement comparisons, false positives, and search limits. A file with an open witness axiom or sorry is excluded from unconditional certification even if it otherwise compiles.','SmallES')

page();p('The remaining analytic obligation','TitleES')
p('The live Z direction is to prove an existence estimate, not to accumulate more examples. For a prime p≡1 (mod24), choose an integer x in p/4&lt;x&lt;3p/4 with quadratic character χₚ(x)=−1. Put d=4x−p and let H be the subgroup of units modulo d generated by the prime factors of x. Partition H into cosets C of its square subgroup H².')
p('For g∈H define wₓ(g)=#{a&gt;0 : a divides x² and a≡g (mod d)}. Divisor complementation acts by iₓ(g)=x²/g. Let A_C=C∩{−px,−x}, retaining residues in H; these are designated targets, not assumed occupied bins. Set T_C=Σwₓ(g), E_C=Σwₓ(g)² on C.')
p('Let M_C(T_C) be the minimum energy of all nonnegative integer profiles of mass T_C that obey the complement-pair and fixed-bin parity rules while vanishing on A_C. An empty feasible set has minimum +∞. The proposed assertion is')
p('Q(p): ∃ admissible nonresidue x, ∃ square-class cell C,<br/>A_C ≠ ∅ and E_C &lt; M_C(T_C).','MathES')
p('<b>Still open:</b> ∀ prime p≡1 (mod24), Q(p). The certified finite theorem proves that a compatible actual histogram with this strict inequality must occupy a target bin. It does not prove such an x or C exists. General arithmetic compatibility, target-to-ES reconstruction, and all needed domain reductions must also be connected explicitly before claiming a universal implication.')
p('The p=577 local theorem computes the complete divisor histogram and the exact minimum14, then applies the generic forcing theorem to energy12. The separate assertion that both older Jacobi tests fail is not formalized here. The prior p=3361 support-graph failure concerns a different sufficient criterion and does not refute Q(p).')
h('Reproduction and trust boundary')
p('Toolchain: Lean4.19.0 (6caaee842e94); Mathlib v4.19.0 at c44e0c8ee63ca166450922a373c7409c5d26b00b. The archive retains lake-manifest.json and dependency-pin verification. Install the pinned Lean toolchain; in lean/ run lake exe cache get, then run scripts/verify.sh from the archive root. The script cleans this project only, rebuilds ES, runs Audit.lean, and scans sources. Full commands and logs are included.')
p('All audited project theorem dependencies are restricted to propext, Classical.choice, and Quot.sound. No sorry/admit, custom mathematical axiom, or native_decide is accepted. Compiler-generated unsafe specialization stubs are inventoried separately; none is allowed in a theorem’s proof dependencies. The initial overbroad audit rejection and its diagnosis are preserved. Imported Mathlib binaries came from its cache; Mathlib was not rebuilt from source here. Formal checking still requires review of statement-to-prose alignment.')
p('This environment required a small readlink compatibility shim mapping /proc/&lt;current-pid&gt;/exe to /proc/self/exe. Its source is included and reviewed; it does not change Lean’s kernel or proof rules. Ordinary installations should not need it. Six agent lanes and a coordinating review split construction, descent, forcing, families/matching, literature, and toolchain audit; source/statement alignment was cross-reviewed.')
p('Deliverables: proof dependency map (PDF/PNG), this report, and source/receipt archive with portable rerun instructions for whouxe82. No run on that machine has occurred here. The map uses a dependency graph: shared foundations converge, while an explicit gap separates checked results from open universal assertions. Infinite families are omitted as main branches.','SmallES')

def footer(c,doc):
    c.saveState();c.setStrokeColor(colors.HexColor('#D5E0E5'));c.line(45,41,550,41)
    c.setFont('DejaVu',7.7);c.setFillColor(colors.HexColor('#607583'))
    c.drawString(45,27,'ES formal certification · 28 October 2026 · No universal proof claimed')
    c.drawRightString(550,27,str(doc.page));c.restoreState()
doc=SimpleDocTemplate(str(OUT/'ES_Formal_Certification_Review_2026-10-28.pdf'),pagesize=(595.28,841.89),rightMargin=45,leftMargin=45,topMargin=42,bottomMargin=55,title='Erdős–Straus formal certification review',author='GPT research task')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print('Report written')
