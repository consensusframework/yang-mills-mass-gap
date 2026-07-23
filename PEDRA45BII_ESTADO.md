# PEDRA 45b-ii — ESTADO E MAPA COMPARATIVO (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 45b-ii.**
Base: main pós-45b-i (48 arquivos, ~430 teoremas públicos, 0 axiomas, 0 sorry).
Estado analítico: Σ_{D≁C} kpWeight ≤ 4|C|·16·B reduzido a
B ≥ Σ_{D ∋ p₀ conexo} kpWeight(D); com a 44ª, cada termo ≤ (2β)^k·e^{αk};
falta APENAS: #{D : p₀ ∈ D, conexo, |D| = k} ≤ A^k com A função de Δ ≤ 64.

## COMPARAÇÃO DAS DUAS ROTAS (itens exigidos)

### ROTA EULER/WALK — bound candidato Δ^(2(k−1))

Mecânica: árvore geradora canônica de D (via grafo induzido em D) →
travessia dobrada → walk de comprimento 2(k−1) no plaquetteGraph partindo
de p₀ → D = conjunto visitado.
Ponto decisivo NOVO (reavaliação do antigo ponto 4): a contagem de walks
NÃO exige enumeração global de vizinhos. Defina
  walksFrom p₀ 0 := {caminho trivial}; walksFrom p₀ (n+1) por extensão;
prove por INDUÇÃO EM n:
  card (walksFrom p₀ (n+1)) ≤ Δ · card (walksFrom p₀ n)
usando SÓ card_biUnion_le + o degree ≤ 64 da 45b-i (cada extensão escolhe
um vizinho do último vértice — biUnion sobre o neighborFinset!). Nenhum
Fin Δ, nenhuma enumeração. Isso é EXATAMENTE a mecânica biUnion já usada
3 vezes (45a, 45b-i). Walks como listas: representar por
`List` de plaquetas com condição de adjacência consecutiva (def recursiva
própria, SEM SimpleGraph.Walk — evita a API de Walk dependente) ou pelo
Finset de "caminhos = Fin n → plaquetas"? Proposta concreta: 
  pathsFrom p₀ n := Finset de (Fin (n+1) → P) com f 0 = p₀ e adjacência
  consecutiva — subconjunto de um Fintype de funções; card por indução.
CUSTO REAL: (i) def pathsFrom + card-indução: ~5 lemas, mecânica conhecida;
(ii) A INJEÇÃO D ↦ walk: aqui mora o dragão — exige árvore geradora
canônica DE UM SUBCONJUNTO (transporte para Fin k OU BFS direta no grafo
induzido) + travessia determinística + prova de que o conjunto visitado
recupera D + injetividade. Estimativa honesta: 2-3 entregas.

### ROTA DYCK/ÁRVORE PLANA — bound candidato Catalan(k−1)·Δ^(k−1)

Mesma exigência de árvore canônica (componente compartilhado com Euler).
Adicional: códigos de Dyck (palavras balanceadas) + ordem canônica de
filhos + decodificação. Escolhas de vizinho por produto dependente: a
cardinalidade Π ≤ Δ^(k−1) por prod_le com card ≤ Δ — ok, mas a
DECODIFICAÇÃO código→árvore→conjunto é recursão estrutural nova, e
Catalan ≤ 4^(k−1) precisaria ou de prova própria ou de majorar códigos
por strings binárias de comprimento 2(k−1) (2^(2(k−1)) = 4^(k−1) — fácil:
injeção em Bool^(2(k−1))). CUSTO: tudo da rota Euler MENOS o passeio,
MAIS a camada de codificação/decodificação. 

### VEREDITO TÉCNICO (recomendação única, como pedido)

RECOMENDO A ROTA EULER/WALK — com uma SIMPLIFICAÇÃO que dispensa a
injeção via árvore: em vez de injetar D em UM walk, usar COBERTURA:
  {D : p₀ ∈ D, conexo, |D| = k} ⊆ imagem de pathsFrom p₀ (2(k−1))
    sob (f ↦ conjunto dos valores) —
porque TODO conexo com k vértices admite ALGUM walk dobrado que o
percorre (existência apenas! sem canonicidade, sem injetividade: a
COBERTURA majora card via card_image_le ≤ card pathsFrom ≤ Δ^(2(k−1))).
EXISTÊNCIA de walk percorrendo D: pela árvore geradora — MAS existência
é MUITO mais barata que canonicidade: qualquer árvore serve, e a
existência de travessia dobrada numa árvore finita conexa é indução
no tamanho (remover folha). Alternativa ainda mais barata a censar:
existência de walk de comprimento ≤ 2(k−1) visitando tudo já segue de
conectividade por indução em k (adiciona-se um vértice de fronteira com
ida-e-volta +2). SEM Penrose, SEM Fin k, SEM canonicidade, SEM
injetividade — só existência + imagem + card. Estimativa: UMA entrega
(pathsFrom + card-indução + existência por indução + capstone
count ≤ Δ^(2(k−1))), com Δ = 64 da 45b-i.
Registro honesto: o bound fica Δ^(2(k−1)) — pior que (4Δ)^(k−1) na
constante, IRRELEVANTE para o critério (β pequeno absorve).

## MONTAGEM (fica para a 46ª, não aqui)

  Σ_{D ∋ p₀, |D|=k} kp ≤ 64^(2(k−1))·(2β)^k·e^{αk};
  Σ_k finita ≤ série geométrica de razão r = 2β·64²·e^α;
  B uniforme em N para r < 1. Depois: 4|C|·16·B fecha o esquema 45.

## O QUE NÃO ENTRA na 45b-ii

Séries, escolha de α/β, KP, log Z, convergência, limite termodinâmico;
Catalan/Dyck (rota preterida — registrada, não descartada).

**Aguardando parecer. Nada será implementado antes.**
