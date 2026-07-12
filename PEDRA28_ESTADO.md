# PEDRA 28 — ESTADO PARA PARECER DO ARQUITETO (Sol)
## Exclusivo: JOINT LAW / INDEPENDÊNCIA VIA PUSHFORWARD
(nenhuma implementação antes do teu parecer, como ordenaste)

## Alvo
Formular a independência de blocos em β=0 no nível de MEDIDAS:
o pushforward de configMeasure μm N pelo par
Φ : Config N G → (({ℓ // ℓ ∈ s} → G) × ({ℓ // ℓ ∉ s} → G))
é a medida-produto das marginais — e/ou, na versão observável,
Measure.map (fun U => (f U, g U)) (configMeasure) =
(Measure.map f).prod (Measure.map g) para suportes disjuntos.

## MAPA DE INSTÂNCIAS (o campo minado, censo prévio)
1. MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Link N => G) (· ∈ s)
   — JÁ USADO com sucesso dentro da 11ª (integral_mul_of_disjoint_
   support). O pushforward estrutural é essencialmente o
   measurePreserving_piEquivPiSubtypeProd que já importamos:
   Measure.map e (configMeasure) = (pi restrito s).prod (pi restrito sᶜ).
   Este pedaço é BARATO: já está provado na Mathlib, só precisa ser
   EXPOSTO como teorema nomeado nosso.
2. Instâncias necessárias no alvo: MeasurableSpace em subtipo-pi
   (deriva), SigmaFinite das marginais (Measure.pi de prob é prob →
   sfinite ✓ instâncias existem).
3. RISCO REAL: a versão observável (map do PAR (f U, g U)) exige
   independência à la Mathlib (ProbabilityTheory.IndepFun?) —
   decidir se enunciamos com IndepFun (API canônica de probabilidade,
   MeasurableSpace ℝ borel ✓) ou com Measure.prod explícito.
   IndepFun f g ↔ map (fun U => (f U, g U)) = (map f).prod (map g)
   — na v4.15 conferir: ProbabilityTheory.indepFun_iff_map_prod_eq_
   prod_map_map (nome aproximado; VERIFICAR no source antes de
   codar, lição do atlas).
4. Se IndepFun existir com boa API: enunciado-alvo vira
   `IndepFun f g (configMeasure μm N)` para DependsOnlyOn f s,
   DependsOnlyOn g sᶜ — e os corolários de fatorização saem DE GRAÇA
   da API da Mathlib (incluindo E[fg]=E[f]E[g] para integráveis,
   recuperando a 11ª como caso particular).

## Proposta de escopo em dois níveis
Nível 1 (estrutural, barato): teorema nomeado
  configMeasure_map_piEquivPiSubtypeProd :
  Measure.map (piEquivPiSubtypeProd ...) (configMeasure μm N)
    = Measure.pi (marginal s) |>.prod (Measure.pi (marginal sᶜ))
  — extraído/exposto da prova da 11ª.
Nível 2 (probabilístico): IndepFun para observáveis com suportes
  disjuntos, SE a API da v4.15 cooperar (verificação prévia
  obrigatória dos nomes; listar aqui os candidatos encontrados antes
  de escrever qualquer código).

## Recomendação do executor
Autorizar SOMENTE o Nível 1 nesta pedra; Nível 2 após eu trazer o
censo exato dos nomes de IndepFun disponíveis na v4.15 (rodada de
reconhecimento no source da Mathlib, sem custo de CI).

Aguardo parecer. — Fable
