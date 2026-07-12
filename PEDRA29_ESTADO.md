# PEDRA 29 — ESTADO PARA PARECER DO ARQUITETO (Sol)
## Independência mútua de família finita: iIndepFun / joint tuple law
(nenhuma implementação antes do teu parecer; mapa de APIs abaixo,
verificado no SOURCE da Mathlib v4.15, não em memória)

## CENSO DE APIs v4.15 (Probability/Independence/Basic.lean)
Verificados hoje, com linha do source:
- `iIndepFun (m : ∀ i, MeasurableSpace (β i)) (f : ∀ i, Ω → β i) μ`
  (def, linha 123) — família indexada por ι arbitrário.
- `iIndepFun_iff_measure_inter_preimage_eq_mul` (556) + alias
  `iIndepFun.measure_inter_preimage_eq_mul` (564):
  iIndepFun ↔ ∀ (S : Finset ι) sets (mensuráveis em S),
  μ(⋂ i∈S, fᵢ⁻¹ setsᵢ) = ∏ i∈S, μ(fᵢ⁻¹ setsᵢ).
  ESTA é a porta de entrada natural (mesma estratégia da 28ª,
  agora com Finset em vez de par).
- `iIndepFun.indepFun` (351): mútua ⇒ pairwise (i≠j).
- `iIndepFun.indepFun_finset` (631): mútua ⇒ blocos disjuntos de
  índices independentes — DE GRAÇA, o teorema "bloco vs bloco" que
  generaliza o one-vs-block da 27ª no nível de medida.
- `iIndepFun.indepFun_prod_mk` (636), `indepFun_prod_mk_prod_mk`
  (642), `indepFun_mul_left/right/mul_mul` (657-669): álgebra
  derivada, tudo de graça após iIndepFun.
- `iIndepFun.comp` (566): pós-composição mensurável preserva.
- NÃO encontrei um análogo n-ário pronto de
  indepFun_iff_map_prod_eq_prod_map_map (lei conjunta da tupla
  como pi das marginais); a versão "joint tuple law" exigiria
  Measure.map (fun U i => fᵢ U) = Measure.pi (map fᵢ) — fazível via
  Measure.pi_eq + measure_inter_preimage, mas é meia-pedra própria.

## ROTA PROPOSTA
1. Lema B' (generalização direta da 28ª-B): iIndepFun puxa para
   trás por MeasurePreserving — prova idêntica à da 28ª trocando o
   par por ⋂/∏ sobre Finset (measure_preimage nas interseções).
   ATENÇÃO: preimagem de ⋂ finita precisa Set.preimage_iInter₂.
2. Teorema principal: família (fᵢ) com DependsOnlyOn fᵢ (supp i) e
   suportes pairwise disjuntos ⇒ iIndepFun (borel) f (configMeasure).
   Rota no espaço split: em vez de UM split binário, usar o split
   POR ÍNDICE via MeasurableEquiv... — AQUI mora o custo: o split
   n-ário simultâneo não tem equiv pronto na Mathlib. Alternativa
   económica (proposta): provar iIndepFun via o critério de
   interseção finita DIRETAMENTE por indução em S (Finset), usando
   a fatorização binária da 28ª-D (bloco {i} vs resto): a 26ª já fez
   exatamente essa indução para expectativas; repetir para medidas
   de interseções (característicos são observáveis com o mesmo
   suporte!). Insight: μ(⋂ fᵢ⁻¹ Aᵢ) = ∫ ∏ 𝟙_{Aᵢ}(fᵢ U) e o
   indicador herda DependsOnlyOn do fᵢ — reduz a 29ª à 26ª aplicada
   a indicadores. Sem split novo, sem instance-hell.
   Necessário: 𝟙 composto mensurável + DependsOnlyOn de composição
   (lema trivial dependsOnlyOn_comp: φ ∘ f depende do mesmo suporte).
3. Corolários: iIndepFun.indepFun_finset dá bloco-vs-bloco de graça;
   Wilson paths/loops/U(n) como sempre.
4. Joint tuple law (map = pi das marginais): proponho DEIXAR para a
   30ª com estado próprio, dado o buraco de API apontado acima.

## PONTO DE ATENÇÃO PRINCIPAL
A igualdade μ(⋂ i∈S, ...) = ∫ ∏ indicadores exige
integral_indicator/characteristic bookkeeping em ℝ (indicadores como
funções reais limitadas C=1). Alternativa mais direta: usar a versão
para MEDIDAS da 26ª (refazer a indução de D da 26ª com μ e conjuntos,
sem passar por integrais) — mais curta ainda: só usa a 28ª-D binária
e Finset.induction. Recomendo esta.

Aguardo parecer e escolha de rota. — Fable
