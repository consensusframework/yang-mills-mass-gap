# PEDRA17_ESTADO.md — perturbação quantitativa do acampamento-base (β pequeno)

**Commit main:** cfbfe45b8df99dc3a7c686cc5e8d501fd988f297  •  Nada implementado; arquitetura a alinhar.

## Por que este alvo (e não a expansão de caracteres direto)

A expansão de cluster inteira é, no fundo, "β pequeno se comporta como
β = 0 com correções controladas". O degrau mínimo honesto dessa frase é:
o estado de Gibbs é LIPSCHITZ em β na origem, com constante explícita.
Sem isso, nenhuma expansão tem chão. Com isso, a 18ª (derivada em 0 =
−Cov₀(f, S)) e as seguintes têm onde pisar.

## Enunciado-alvo — v2, redesenho aprovado pelo arquiteto

NOME CONCEITUAL: finite-volume continuity bound from β = 0
(não "Lipschitz": controla a distância a zero, não β₁ vs β₂).

TEOREMA CENTRAL (sem hard-code de β ≤ 1), para β ≥ 0, f mensurável com
|f| ≤ C, χ ≤ 1, S ≤ B:

    |⟨f⟩_β − ⟨f⟩₀| ≤ 2·C·B·β·exp(β·B)

COROLÁRIO local-linear, para 0 ≤ β ≤ β₀:

    |⟨f⟩_β − ⟨f⟩₀| ≤ 2·C·B·exp(β₀·B)·β

COROLÁRIO Wilson-path (C = 1, ponte com a 16ª): mesma cota com
f = wilsonLoop χ · x p e |χ| ≤ 1.

Respostas do arquiteto às Q1-Q4: C explícito; β ≥ 0 geral + corolário
β₀; Wilson-path nesta pedra; derivada em β = 0 na 18ª, arquivo
separado. IMPLEMENTAÇÃO AUTORIZADA em branch própria após este v2.

## Decomposição proposta (todos análise real elementar + pedras 5-6)

L1 (elementar): 0 ≤ x → |exp(−x) − 1| ≤ x.
  Mathlib: Real.add_one_le_exp dá 1 − x ≤ exp(−x); com exp(−x) ≤ 1
  fecha. Zero medida.

L2 (peso): 0 ≤ β ≤ 1 → |gibbsWeight β χ U − 1| ≤ β·B pontual.
  L1 com x = β·S(U), S ≤ B, monotonia.

L3 (numerador): |∫ f·w_β − ∫ f·w_0| ≤ C·β·B.
  |f·(w_β − 1)| ≤ C·β·B pontual + integral_mono; integrabilidade já
  existe (integrable_gibbsWeight, hfwint da pedra 5 — mesmo padrão).

L4 (denominador): |realZ β − 1| ≤ β·B  e  realZ β ≥ exp(−β·B) ≥ exp(−B).
  L2 integrado + realZ_pos (já provada).

L5 (montagem): |a/z − a₀| com a₀ = ∫f·w₀, z = realZ β:
  a/z − a₀ = (a − a₀)/z + a₀(1 − z)/z;
  |·| ≤ (C·β·B)·exp(B) + C·(β·B)·exp(B) = 2·C·B·β·exp(B). ✓

## Perguntas ao arquiteto

Q1: enunciar com C explícito na hipótese (padrão das pedras 5-6) ou
    com ⨆? Prefiro hipótese explícita (|f| ≤ C), fiel ao acervo.
Q2: β ∈ [0,1] arbitrário para simplificar exp(β·B) ≤ exp(B) — ok, ou
    queres β₀ genérico já?
Q3: vale já enunciar o corolário para o Wilson-path observable
    (C = 1), preparando a ponte com a 16ª?
Q4: a 18ª proposta (derivada em β=0 via hasDerivAt_integral_of_dominated)
    entra no mesmo arquivo ou pedra separada? Voto: separada.

## Referência literária

O resultado-alvo é o lema elementar de continuidade em alta temperatura
que abre qualquer tratamento de expansões: cf. Friedli–Velenik,
*Statistical Mechanics of Lattice Systems* (CUP 2017), cap. de
high-temperature expansions; Seiler, *Gauge Theories as a Problem of
Constructive QFT* (LNP 159, 1982) §2; a estrada adiante é
Osterwalder–Seiler, Ann. Phys. 110 (1978). Nenhuma dessas fontes é
necessária para a prova (análise elementar); são o mapa da montanha.

## Dependências já formalizadas vs lemas ausentes

Já verdes: gibbsWeight/realZ/gibbsExpectation (5ª), integrable_gibbsWeight,
realZ_pos, abs_gibbsExpectation_le (5ª), exists_wilsonAction_bound (6ª),
gibbsExpectation_zero (11ª).
Ausentes (todos elementares): L1-L5 do plano.

## Hipóteses e parâmetros de uniformidade — AVISO HONESTO

A constante B = cota da ação DEPENDE do tamanho N do lattice
(B ~ 2·#plaquetas). Nesta pedra isso é aceitável e explícito: o
enunciado é por-volume-finito. Uniformidade em N (constantes por sítio)
é EXATAMENTE o que a expansão de cluster de verdade fornece — não
prometemos isso aqui, e o docstring dirá isso com todas as letras.

## Primeiro resultado mínimo correto e útil

Sub-marco (se o arquiteto preferir fatiar): só L2+L4 —
|realZ β − 1| ≤ β·B e realZ β ≥ exp(−β·B) — "a função de partição é
Lipschitz em β na origem". Já é publicável no acervo e destrava o resto.

## Campo minado herdado

- unfold configMeasure antes de padrões com Measure.pi.
- goals de integral_congr_ae chegam beta-não-reduzidos: show primeiro.
- instâncias explícitas em lemas com medida em metavariável.
- hidra Fintype: não deve aparecer (zero subtipos neste alvo).

## Arquivo-alvo

Phase3/LatticeGauge/BetaPerturbation.lean, importando Gibbs,
Expectation, WilsonExpectation, Beta0.

Contrato de sempre. — Fable
