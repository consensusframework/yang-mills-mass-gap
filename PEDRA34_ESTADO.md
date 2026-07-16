# PEDRA 34 — CONCLUÍDA (2026-07-16)

## Resultado
VERDE em DUAS rodadas. Arquivo: Phase3/LatticeGauge/ComponentFactorization.lean
2 defs (componentFamily, blockActivity) + 12 teoremas: família A-F +
suportes disjuntos da família; elo local plaquetteActivity_dependsOnlyOn;
blockActivity_dependsOnlyOn (26ª genérica, sem teoria nova);
mensurabilidade; decomposição algébrica via Finset.prod_biUnion;
capstone E₀ por componentes (26ª com ι := Finset, sem tipo dependente);
capstone final realZ_eq_sum_component_weights.
Placar: 34 pedras, 33 arquivos, ~195 teoremas, 0 axiomas.
Caso A = ∅ documentado e fechado sem hipótese artificial.

## APIs verificadas no source ANTES do código
- Finset.prod_biUnion (BigOperators/Group/Finset.lean:551):
  hipótese Set.PairwiseDisjoint ↑s t — encaixou com a 33ª-F sem
  tradução (Set.Pairwise por elementos, coerção defeq).
- Finset.image / mem_image / image_empty; Finset.mem_biUnion;
  Finset.mem_powerset.
- 26ª consumida: gibbsExpectation_finsetProd_zero_of_pairwise_disjoint_
  support, dependsOnlyOn_finsetProd, measurable_finsetProd.
- 32ª consumida: realZ_eq_sum_integral_prod_activity + gibbsExpectation_zero.

## Vilão (rodada 1)
Variável de seção μm passada explicitamente a lema cujo enunciado não
a usa (seção só inclui variáveis USADAS) — erro de aplicação; cura
trivial. Atlas: conferir assinatura efetiva de lemas nascidos em
seções com variáveis parcialmente usadas.

## Linguagem (correção do arquiteto, aplicada)
"Cada termo de Mayer fatoriza pelas componentes conexas do SEU
subconjunto; a soma continua soma." Vocabulário: connected component /
block activity / component weight. Polymer: ainda não é objeto.
