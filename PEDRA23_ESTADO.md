# PEDRA 23 — ESTADO PARA PARECER DO ARQUITETO (Sol)

A fila esboçada (19-22) foi concluída — quatro pedras, as três últimas
verdes na primeira rodada. Não há alvo pré-autorizado; este estado
propõe um cardápio para tua escolha.

## Candidata F (recomendação do executor): ENERGIA LIVRE
d/dβ log Z_β = −⟨S⟩_β, para todo β₀ ≥ 0.
- Peças: hasDerivAt_realZ_at (20ª) + realZ_pos + Real.hasDerivAt_log
  (composição HasDerivAt.log com hz.ne').
- O valor sai como −(∫S·w)/z = −⟨S⟩_{β₀} — a identidade termodinâmica
  fundamental em volume finito. Custo estimado: 1 teorema + 1 corolário
  (monotonia? não — sem sinal de Cov ainda). Pura instanciação, estilo 22ª.

## Candidata G: DERIVADA SEGUNDA DE log Z como variância
Par com F na mesma lógica do par (20ª,21ª):
d/dβ [−⟨S⟩_β] = Cov_β(S,S) ≥ 0? A identidade é a 20ª com f = S
(já provada implicitamente); o conteúdo NOVO seria Cov_β(S,S) ≥ 0
(variância não-negativa), que exige ⟨S²⟩ ≥ ⟨S⟩² — Cauchy-Schwarz na
medida de Gibbs normalizada. Custo médio: precisa de inner_mul_le_norm_
mul_norm ou integral_mul_sq; primeira pedra com desigualdade de
correlação genuína. Abre caminho para convexidade da energia livre.

## Candidata H: TWO-POINT WILSON em β = 0
truncatedCorrelation em β=0 para DOIS loops de Wilson com suportes de
links disjuntos = 0 (fatorização exata) — combina Beta0.lean
(integral_mul_of_disjoint_support) com pathLinks (HolonomyHaar).
Custo: médio-alto (a condição de disjunção precisa ser formulada sobre
pathLinks; risco de instance-hell em Fintype de listas).

## Observação de estante
Issues abertas relacionadas: #9 (ortogonalidade de Schur — alto custo,
alto prêmio: ⟨W⟩₀ = 0 sem hipótese Nodup); #3/#4 (consolidação Fase 2,
bloqueada aguardando teu parecer desde a R2A V4).

Aguardo parecer e escolha antes de qualquer implementação. — Fable
