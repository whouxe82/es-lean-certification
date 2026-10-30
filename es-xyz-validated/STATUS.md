# Status of every result in this folder — 30 October 2026

Labels follow the project's evidence rules: mathematical status · review status · novelty · verification.
"Director" = Dr W. C. Houze, who ran each replication himself. Nothing below is a statement about the truth of the
Erdős–Straus conjecture.

| # | Statement | Mathematical status | Reviewed by | Novelty | Computational replication | Where |
|---|---|---|---|---|---|---|
| 1 | Two-channel divisor criterion (Lemmas 1–2): success at shift d ⇔ a divisor of x² hits −x or −p·x mod d | PROVED | Claude, GPT | KNOWN (Mordell; Bradford; Elsholtz–Tao) | — | paper App. A.1; Lean Type I/II split VERIFIED (repo root) |
| 2 | Channel depth D(p) ≤ 107 for all 444,820 primes p ≡ 1 (mod 24) below 6·10⁷; record 8,803,369 | FINITE_VERIFIED (6·10⁷) | — | KNOWN: Ionascu–Wilson 2010/2011 classes C_i, same record list, computed to ≈ 4.1·10⁹ | Claude 22 s; director Colab 34.3 s, identical | 01 |
| 3 | Exact avoidance minimum M (closed formula; GPT Thm 5), collision form, equality/parity consequences, bounds | PROVED (paper) | Claude (brute force 2,050 cases: 0 mismatches) | NOT_ASSESSED | director Colab 29 Oct, identical | 02 |
| 4 | Support obstruction: finite forcing needs every complement pair occupied (GPT Prop. 8) | PROVED (paper) | Claude (reconstruction) | NOT_ASSESSED | — | 02 |
| 5 | Uniform Q-families: d \| p+1 (Obláth), d = 7 for p mod 7 ∈ {3,5,6}, d = 15 for p mod 5 ∈ {2,3} (GPT Thms 9–11) | PROVED (paper) | Claude (all qualifying primes < 20,000: 0 violations) | restates classical coverage (Mordell, Obláth) | director Colab | 02 |
| 6 | Complete classification of infinite thresholds: central (d \| p+1); d = 15 case; Channel II with K = {1} (GPT Thm 13) | PROVED (paper) | Claude (exhaustive on every admissible input, p < 1,500: 0 violations) | POSSIBLE_NEW | director Colab | 02 |
| 7 | No finite menu of shifts gives a non-residue x for every p ≡ 1 (mod 24) (GPT Thm 14) | PROVED; depends on audited dependency Dirichlet | Claude | elementary | — | 02 |
| 7b | No finite menu of shifts has a *firing channel* at every residual prime | OPEN | — | — | no counterexample below 6·10⁷ (nor ≈ 4.1·10⁹ per Ionascu–Wilson) | 01 |
| 8 | Q holds for a relative-density-one set of primes ≡ 1 (mod 24) (GPT Cor. 12) | CONDITIONAL on the cited bound O(N/(log N)^{3/2}) for primes with p+1 free of primes ≡ 3 (mod 4) (Pomerance–Weingartner, intro) | Claude | consequence of Obláth | — | 02 |
| 9 | Pilot: Q holds with finite-threshold witnesses at all 29 primes ≡ 1 (mod 24) up to 1873 | FINITE_VERIFIED | two sealed implementations agree (Claude; GPT-DP-1.0.0) | — | director's Actions runs 29 Oct; `q_attack.py` reproduces the record exactly | 05 (implementations held by the director; GPT-DP-1.0.0 inside the ES-Q-REF-1 evidence zip) |
| 10 | Conjecture Q (ES-QP-TEST v1.0): for every p ≡ 1 (mod 24), some admissible x and eligible cell have E < M | **REFUTED** — 25 counterexamples below 10⁶, smallest 66,361 | Claude (sweep); GPT (ES-Q-REF-1 at 66,361: 54/54 cells, Prop.-15 certificate); Claude validated GPT's certificate (54/54) | — | director Colab 30 Oct (120,000 and 1,000,000), identical | 03 |
| 11 | Q-extended (x of either residuosity) | **REFUTED** at p = 944,329 | Claude | — | director Colab 30 Oct | 03 |
| 12 | Conjecture Q′ (residual form on R) | **REFUTED** (consequence of 10) | GPT concurs (its "Conjecture 16") | — | — | 03 |
| 13 | ES-MC-1.0.0 Monte Carlo (GPT): uniform sampling finds no forcing in 408 draws; small-d sampling finds it in ~10%; 95% of finite cells at baseline M = T | FINITE result (34 primes ≤ 45,361; all pass Q) | Claude recomputed all 1,979 cells: 0 mismatches | — | director Colab 29 Oct, byte-identical | 04 |
| 14 | Residue criteria A5′ (one free prime), C3-01 (two free primes), chain saturation, K5′, U1, U4; density theorem U(a′) | PROVED (A5′, C3-01, CS, K5′, U1); U4 depends on audited Dirichlet; U(a′) CONDITIONAL on Fuchs–Hsu–Rickards–Schindler–Stange 2026 Thm 1.1 | GPT (Rounds 1–3 cross-review) | POSSIBLE_NEW (A5′, C3-01); core of CS KNOWN | validators sealed blind, 0 mismatches; director's own checks of the four controls: pending | paper §4.2 (sealed round archives, not in this folder) |
| 15 | Lean-certified structural theorems (integral matching; B4 descent; B1/B4 gates; abstract forcing; p = 528n+505 family) | VERIFIED | GPT authored; Claude claim-by-declaration review (no prose outruns its declaration) | matching/descent POSSIBLE_NEW; family prior art | director's GitHub Actions run #1, 28 Oct | repo root |

Open items affecting this folder: originality assessment of 3, 6, 14; the p = 1201 class discrepancy with Ionascu–Wilson
(their C₄, computed class 6); GPT did not run the other 24 Q-failures or 944,329 (optional, not required).
