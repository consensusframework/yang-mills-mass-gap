# PEDRA 45b — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 45b.**
Base: main pós-45a (47 arquivos, ~412 teoremas, 0 axiomas, 0 sorry; a 45a
passou verde NA PRIMEIRA RODADA — duas seguidas).

## A. GEOMETRIA LOCAL DA LATTICE

Definições candidatas (nomes reais a fixar na implementação):
- `plaquettesUsingLink ℓ := (admissiblePlaquettes N).filter (ℓ ∈ plaqLinkSet ·)`;
- M := max card sobre ℓ; Δ := grau máximo de plaquetteShareLink em admissíveis.

VERIFICAÇÃO ANTES DE QUALQUER ENUNCIADO (censo geométrico obrigatório):
o plaqLinkSet real tem os 4 lados {(x,μ), (x+μ,ν), (x+ν,μ), (x,ν)} com
admissível μ<ν. Um link fixo (y,ρ) aparece:
- como lado-base (y,ρ)=(x,μ): plaquetas (y,ρ,ν) com ρ<ν, e (y,ν,ρ) via
  posição 3 transladada… — a contagem honesta exige enumerar as 4 posições
  × direções ν≠ρ × sinais de translação. Fórmula CANDIDATA (não afirmada):
  M ≤ 4·(#Dir − 1), com valor exato possivelmente 2·(#Dir − 1) por
  cancelamentos de admissibilidade (μ<ν corta metade) e coincidências.
  DECISÃO DE MÉTODO: provar um BOUND (≤), não a igualdade — igual à
  filosofia do ≤ 4 da 45a; a igualdade fina fica registrada como
  refinamento. Rota: para ℓ fixo, injetar plaquettesUsingLink ℓ num
  produto (posição ∈ Fin 4) × (direção ∈ Dir) — injeção explícita, card
  do produto = 4·#Dir; bound bruto M ≤ 4·#Dir JÁ SUFICIENTE para 45b/46
  (constantes não otimizadas não bloqueiam convergência para β pequeno).
- Δ ≤ 4·M (cada vizinho compartilha um dos ≤ 4 links; para cada link ≤ M
  plaquetas): bound composto, independente de N. Em volumes pequenos
  (N=1,2) as identificações periódicas só DIMINUEM as contagens — o ≤
  sobrevive; nenhum caso especial.
- Uniformidade em N: as definições quantificam sobre Site N, mas os bounds
  são por injeção local em Fin 4 × Dir — nenhuma constante menciona N.

## B. CONTAGEM DE CONJUNTOS CONEXOS ENRAIZADOS

Alvo: #{S ⊆ admissíveis : |S| = k, p₀ ∈ S, IntrinsicallyConnected S} ≤ f^k.
Redução link→plaqueta pelo M de A: polímeros com ℓ no suporte =
⋃_{p ∈ plaquettesUsingLink ℓ} {S : p ∈ S} ⟹ fator M na frente
(card_biUnion_le, mesma mecânica da 45a).

## C. ROTA DO PASSEIO DOBRADO — os 4 pontos exigidos

1. TRANSPORTE Fin: a infraestrutura da 40ª vive em SimpleGraph (Fin (n+1)).
   Para S com |S| = k, k ≥ 1: transportar via a bijeção
   `Finset.equivFin`-tipo (censar nome exato: S ≃ Fin S.card existe como
   `Finset.equivFin : s ≃ Fin s.card`)? O grafo induzido de
   plaquetteShareLink em S vira SimpleGraph (Fin k) por comap da
   equivalência (mecânica idêntica ao relabel da 38ª). CUSTO: médio —
   o comap de Equiv já foi feito uma vez (UrsellSymmetry), reutilizável.
   PROBLEMA HONESTO: a equivFin não é canônica-por-construção do ponto de
   vista matemático, mas É determinística (ordem interna do Finset) — para
   INJEÇÃO basta que S ↦ (enumeração, walk) seja função; a recuperação de
   S pelo walk usa a decodificação, não a escolha.
2. TRAVESSIA CANÔNICA: DFS determinística na penroseTree (filhos em ordem
   crescente de rótulo — min já é o padrão da 40ª). Definição recursiva
   sobre a profundidade; TERMINAÇÃO: árvore finita, medida = card do
   subconjunto não visitado. Alternativa mais barata SEM recursão geral:
   codificar a árvore diretamente pela função-pai (41ª: penroseParent?
   determina a árvore) e contar CÓDIGOS em vez de walks — ver ponto 4.
3. RECUPERAÇÃO: o walk visita exatamente os vértices de S (a árvore é
   geradora de S por construção da 40ª) ⟹ S = imagem do walk na lattice
   (composta com a enumeração) — a injeção é (S ↦ walk rotulado em
   plaquetas REAIS, não em Fin k), evitando o problema da escolha.
4. CONTAGEM DE ESCOLHAS: aqui está o custo real — enumerar vizinhos por
   Fin Δ exige uma função de enumeração uniforme
   `neighborEnum : ∀ p, plaquetteNeighbors p ↪ Fin Δ`. ALTERNATIVA QUE
   EVITA WALKS COMPLETAMENTE (candidata a recomendação): contar
   FUNÇÕES-PAI: uma árvore enraizada de S (k vértices, raiz p₀) é
   determinada pelo pai de cada não-raiz, e cada pai é VIZINHO do filho
   ⟹ injeção de {S conexo, |S|=k, p₀ ∈ S} em
   (Fin (k−1) → vizinhança-iterada)… o domínio ainda depende de S.
   Versão limpa: S é determinado por (árvore abstrata em Fin k, rótulo
   de cada vértice), rótulos determinados de baixo: raiz = p₀, filho ∈
   vizinhos do pai (≤ Δ escolhas), e #árvores abstratas ≤ 4^k (códigos
   de Dyck/parênteses — formalizável como subconjunto de Fin 2^(2k)) ⟹
   #S ≤ 4^k · Δ^(k−1). O código de Dyck substitui o passeio dobrado com
   MENOS infraestrutura (sem Walk, sem recursão de travessia: só a
   sequência de subidas/descidas). AVALIAÇÃO: Dyck-bound 4^k·Δ^(k−1) vs
   Euler Δ^(2(k−1)) — mesma ordem exponencial; o Dyck evita a API Walk.
5. COMPARAÇÃO com alternativas do parecer: DFS+mínimo ≈ nossa travessia;
   palavras de vizinhos = a versão função-pai acima; fronteira clássica
   (animais) exige ordem total nas plaquetas — temos (produto de Fins);
   Mathlib v4.15: NENHUM lema de contagem de animais/subárvores censado
   até agora (a censar formalmente na Etapa Zero da implementação).

## D. RESULTADO-ALVO E MONTAGEM

Forma-alvo (após A+C):
  #{D : |D| = k, ℓ ∈ suporte D} ≤ M · A^k   (A = constante de C, dep. só de Δ)
Combinação com a 44ª (soma FINITA no volume, majorada termo a termo):
  Σ_{D ∋ ℓ} |w_β(D)| e^{α|D|} ≤ Σ_{k=1}^{K(N)} M·A^k·(2β)^k·e^{αk}
    ≤ M · Σ_{k≥1} (2βAe^α)^k   [série geométrica MAJORANTE, indep. de N]
    = M · r/(1−r) para r = 2βAe^α < 1.
Status epistêmico a manter: a passagem da soma finita à majorante
geométrica é legítima (termos não negativos, soma parcial ≤ série);
a CONDIÇÃO 2βAe^α < 1 define o regime de β pequeno; nada disso é
Kotecký–Preiss completo ainda (falta o argumento indutivo sobre a
árvore de clusters) — declarar exatamente isso.

## RECOMENDAÇÃO

45b em duas entregas: (i) geometria local A (M ≤ 4·#Dir por injeção
explícita, Δ ≤ 4·M) — custo médio, tudo censável; (ii) contagem via
CÓDIGOS DE DYCK + rótulos (evita Walk e travessia recursiva; a rota
Euler fica como alternativa registrada se o parecer preferir). A soma
geométrica final (D) é a 46ª.

**Aguardando parecer. Nada será implementado antes.**
