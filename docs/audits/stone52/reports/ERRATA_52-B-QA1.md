# ERRATA — RELATÓRIO 52-B-QA1 (2026-09-11)

**Local:** §6 "Interface para a 52-C", item 1.
**Erro:** escrevi `E_T(1) − E_T(θ) = Σ_{atinge ambos os proibidos} (1 − θ^{tupleTouchCount δ})·ursell·∏w/k!`.
**Correção:** com a convenção auditada `E_T(θ) = S_P(w_θ) − S_0(w_θ)` (restrito − pleno),
`E_T(1) − E_T(θ) = [S_P(w) − S_P(w_θ)] − [S_0(w) − S_0(w_θ)] = −Σ_{atinge ambos os proibidos} (1 − θ^{tupleTouchCount δ})·ursell·∏w/k!`.
Justificativa: a primeira colchete soma apenas tuplas P-permitidas, a segunda todas as tuplas; a diferença é o negativo da soma sobre tuplas com algum P-proibido, e o fator `1 − θ^{tc}` anula-se salvo quando alguma posição toca r. Coerente com a 51-C (`region − full = connector`, logo `full − region = −connector`).
**Efeito:** nenhum sobre o capstone, os endpoints, os testes, o build ou o veredito (`52-B QA1 PASS`). Afeta apenas a orientação de sinal para a 52-C.
**Apontado por:** Sol (arquiteto). **Reconhecido por:** o auditor.
