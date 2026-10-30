# Refutation of Conjecture Q — three independent artefacts

- `claude/` — the exhaustive decision programs and result records. `q_attack_results_1M_claude.json` holds, for each of the
  25 failing primes below 10^6, every eligible cell at every firing x (d, x, channel, T, E, M): the data of a Proposition-15
  refutation certificate. SHA-256 of the record: f5744897525db35904d49881a51526da12dae0b89baaabcb5cfedbfec1b2ba21.
- `director-replication/` — Dr Houze's Colab output for N = 1,000,000, identical to Claude's run.
- `gpt-confirmation/` — GPT's ES-Q-REF-1 package: unchanged sealed GPT-DP-1.0.0 core run at p = 66,361 through a disclosed
  adapter; GPT's own non-importing validator; the complete certificate with 54 explicit avoiding allocations
  (refutation_certificate.json, SHA-256 4ef0ba8518bba48477287ca511a358964f79a5ddfd19c5884401b3d053f4b163);
  Claude's independent validator of that certificate (54/54 valid, admissible and firing sets identical).

What a refutation of Q means: no cell of the specified kind forces a solution at that prime. It says nothing against the
Erdős–Straus conjecture, which holds at every failing prime with explicit solutions recorded in the paper and in GPT's report.
