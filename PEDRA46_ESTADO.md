# PEDRA 46 — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 46ª.**
Base: main pós-45b-ii (49 arquivos, ~455 teoremas, 0 axiomas, 0 sorry).
A cadeia 44→45a→45b-i→45b-ii está completa: pequenez individual,
porteiras 4|C|, porteiras 16 por link, fatias 16·64^(2m)·(2β)^(m+1)·e^(α(m+1)).

## 1. DECOMPOSIÇÃO POR TAMANHO

polymersUsingLink ℓ = ⋃_{m} rootedLinkPolymersOfSize ℓ m, DISJUNTA
(card determina m). Formal: biUnion sobre m ∈ Finset.range (K+1) com
K := (admissiblePlaquettes N).card (todo polímero tem card ≤ K, então
m ≤ K−1; fatias com m+1 > K são vazias — sanidade D da 45b-ii).
  Σ_{D ∋ ℓ} kp = Σ_{m ∈ range K} Σ_{fatia m} kp
via Finset.sum_biUnion (disjunção pelas cards distintas) — mesma API da 42b.

## 2-3. APLICAÇÃO DA FATIA E FATORAÇÃO

Cada fatia ≤ 16·64^(2m)·(2β)^(m+1)·e^(α(m+1)). Fatoração algébrica:
  = 16·(2β·e^α) · (2β·64²·e^α)^m
provada por ring_nf/pow-manipulação em ℝ (64^(2m) = (64²)^m via pow_mul;
(2β)^(m+1) = (2β)·(2β)^m; e^(α(m+1)) = e^α·(e^α)^m via Real.exp_add/
exp_nat_mul — censar exp_nat_mul ou usar (Real.exp α)^m com
← Real.exp_nat_mul). DEFINIR:
  kpRatio β α : ℝ := 2·β·4096·Real.exp α    (64² = 4096 literal)
  kpPrefactor β α := 16·(2·β·Real.exp α).

## 4-5. SOMA GEOMÉTRICA MAJORANTE

Para r := kpRatio β α com hr : r < 1 (e hr0 : 0 ≤ r):
  Σ_{m ∈ range K} r^m ≤ 1/(1−r)
— soma PARCIAL finita ≤ limite da série: censar
`geom_sum_le` / `geom_series_bound`: candidato v4.15:
  `geom_sum_le_of_lt_one`? ou provar localmente:
  Σ_{range K} r^m = (1−r^K)/(1−r) (geom_sum_eq, r ≠ 1) ≤ 1/(1−r)
  (r^K ≥ 0, 1−r > 0, div monotone) — 3 lemas locais se o nome não
  existir; NENHUMA série infinita (tudo finito + majorante).
CAPSTONE (soma enraizada uniforme):
  rootedLink_kp_sum_le_geom :
    0 ≤ β → r < 1 → Σ_{D ∋ ℓ} kp(D) ≤ kpPrefactor/(1−r)
UNIFORME EM N: o lado direito não contém N (K só aparece na soma
finita, majorada pela série independente de K).

## 6. COMBINAÇÃO COM 45a/45b-i

  Σ_{D ≁ C} kp(D) ≤ 4·|C| · [16·(2β·e^α)/(1−r)]
via incompatible_kp_sum_le_full com B := kpPrefactor/(1−r)... na
verdade a 45b-i já embute o 16: usar incompatible_kpActivity_sum_le_four_mul
(45a) com B := bound da soma por LINK do item 5. Conferir qual fator 16
entra onde (45b-i tinha 16 por link — o item 5 acima JÁ é a soma por
link, com o 16 dentro). Total: 4|C|·16·(2βe^α)/(1−r).

## 7-9. FORMA KOTECKÝ–PREISS E ESCOLHA DE α

Condição KP alvo (forma por polímero, C polímero):
  Σ_{D ≁ C} |w(D)|e^{α|D|} ≤ α·|C|  (a(C) := α·|C| como função de tamanho)
Condição suficiente escalar derivada do item 6:
  64·(2β·e^α)/(1−r) ≤ α        [64 = 4·16]
Escolha racional SEM otimização: α := 1. Então e^α = e ≤ 3 (censar
Real.exp_one_lt_d9 ou exp_one_lt_3? há `Real.exp_one_lt_d9`: e < 2.7182818286
— dá e ≤ 3 com norm_num). Condição vira: 128·β·e/(1−8192·β·e) ≤ 1,
satisfeita p.ex. para β ≤ 1/40000 (aritmética concreta: 8192·e·β ≤
8192·2.72·β ≤ 22283·β ≤ 0.557 e 128·e·β ≤ 348.2·β ≤ 0.0087 ≤ 1−0.557 —
verificar por norm_num na implementação; declarar o β₀ escolhido como
DEFINIÇÃO: smallBeta₀ : ℝ := 1/40000, sem otimalidade).
STATUS EPISTÊMICO OBRIGATÓRIO: isto é a DESIGUALDADE KP para o nosso
gás; o TEOREMA KP completo (indução sobre árvores de clusters ⟹
convergência da série de log Z) NÃO é provado na 46ª — registrar como
próximo capítulo. Nenhuma consequência sobre clustering/massa.

## 10. SEPARAÇÃO EXPLÍCITA (docstring obrigatório)

- soma finita no volume: itens 1-2 (dependem de N via os Finsets);
- majorante por série: itens 4-5 (constantes livres de N);
- uniformidade: o bound final não menciona N;
- o que fica condicional: o uso da desigualdade KP num teorema de
  convergência da expansão — capítulo seguinte, não a 46ª.

## CABE NUMA ENTREGA?

SIM, com corte natural em (46a) itens 1-6 (soma geométrica e bound
uniforme — só álgebra e as APIs já censadas) e (46b) itens 7-9 (a
desigualdade KP com α = 1 e β₀ concreto — norm_num pesado) SE o parecer
preferir; a estimativa é que caiba inteira (~12-15 teoremas).

## O QUE NÃO ENTRA

Teorema KP completo (indução de clusters), log realZ, convergência da
expansão, decaimento, clustering, massa, limite termodinâmico,
otimização de constantes.

**Aguardando parecer. Nada será implementado antes.**
