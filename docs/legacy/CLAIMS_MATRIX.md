# CLAIMS_MATRIX.md — cada alegação pública → artefato → como verificar

| # | Alegação | Artefato | Verificação |
|---|---|---|---|
| 1 | Fase 3: 18 pedras, ~78 teoremas, 0 axiomas | Phase3/LatticeGauge/*.lean | `cd Phase3 && lake build`; `grep -c "^axiom" LatticeGauge/*.lean` = 0 |
| 2 | Setor β=0 do modelo caracterizado exatamente | Beta0/SingleLink/PairLink/MultiLink/HolonomyHaar | build + ler enunciados |
| 3 | ⟨Wilson-path⟩₀ = ∫χ dHaar em U(n), só condições estruturais | HolonomyHaar (…_unitary, …_closed) | build; hipóteses visíveis na assinatura |
| 4 | Continuity bound (17ª) e resposta linear (18ª), volume finito | BetaPerturbation, LinearResponse | build; docstrings declaram os limites |
| 5 | 60/126 teoremas da Fase 2 FOUNDATION_ONLY | docs/audit/KERNEL_XRAY.* | artifact do CI ou `python3 scripts/kernel_xray.py …` |
| 6 | Wrappers de axioma identificados nominalmente | KERNEL_XRAY.json (campo scientific_axioms) | grep pelo nome |
| 7 | 922 declarações vivas; ~503 arquivadas intactas | docs/audit/AUDIT_ZERO_V2* | CSV + git log de archive_peneira |
| 8 | Legado 1-2 = condicional; alegações antigas retratadas | README, VERIFICATION_STATUS, AXIOM_AUDIT | leitura |
| 9 | Nenhuma prova aceita por confiança de modelo (Fase 3) | histórico de CI por commit | Actions da main |
| 10 | Colaboração inter-lab com créditos exatos | mensagens de merge (12,14,15,17,18) | `git log --merges` |

Regra: alegação sem linha nesta matriz NÃO vai a público.
