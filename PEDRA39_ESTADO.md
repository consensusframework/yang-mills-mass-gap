# PEDRA 39 — MAPA: DEGRAU ELEMENTAR vs DEGRAU DIFÍCIL PARA |φ(G)|
# (encomenda do parecer da 38ª; NENHUMA implementação até autorização)

## Rota A — degrau elementar (cotas triviais e casos exatos)
A1. |graphUrsellCoeff G| ≤ (connectedSpanningEdgeSets G).card.
    Prova: Finset.abs_sum_le_sum_abs + |(−1)^k| = 1 + sum_const.
    CUSTO: BAIXO (3 lemas de prateleira). Infra testada: nenhuma.
A2. (connectedSpanningEdgeSets G).card ≤ 2 ^ (availableEdges G).card.
    Prova: filter ⊆ powerset + Finset.card_powerset + card_le_card.
    CUSTO: BAIXO. Corolário: |φ| ≤ 2^{|E|}.
A3. Coeficiente EXATO quando G é uma árvore (grafo conexo com
    |E| = n − 1): φ(G) = (−1)^{n−1}, pois o ÚNICO subconjunto conexo
    gerador de uma árvore é o conjunto total (remover qualquer aresta
    desconecta). Precisa: "remover aresta de árvore desconecta" —
    reconhecimento em Mathlib (SimpleGraph.IsTree existe? Acyclic +
    Connected; deleteEdges; teoremas de bridge). Se a API de árvores
    da v4.15 for magra, formular SEM a palavra árvore: para G conexo
    com todas as arestas PONTE (bridge), φ = (−1)^{|E|} — e provar
    caminho/estrela como instâncias. CUSTO: MÉDIO (depende da API).
A4. Casos caminho P_n e estrela S_n: instâncias de A3.
    CUSTO: BAIXO após A3; MÉDIO se A3 empacar (provas diretas por
    indução pequenas).

## Rota B — degrau difícil
B1. Penrose identity: partição dos subgrafos conexos em intervalos
    [árvore, grafo] via esquema de Penrose ⟹ |φ(G)| ≤ #árvores
    geradoras. Exige: escolha canônica de árvore (ordem nos vértices
    ✓ temos Fin n), o mapa de Penrose e sua involução parcial.
    CUSTO: ALTO — o primeiro teorema "de paper" do projeto.
B2. Tree-graph inequality na forma usada por Kotecký-Preiss.
B3. Contagem de árvores (Cayley n^{n−2}) para transformar B1 em cota
    numérica. Mathlib: existe Cayley? (duvidoso na v4.15 — verificar;
    alternativa: cota bruta #árvores ≤ n^{n−2} sem igualdade, ou até
    ≤ 2^{|E|·log...} — a forma exata importa menos que a
    superaditividade que KP consome).

## Quanto A ajuda a convergência — e por que não basta (pergunta tua)
A cota A2 dá |φ| ≤ 2^{|E_inc|} com |E_inc| ≤ n(n−1)/2 ⟹
|φ| ≤ 2^{n²/2}. A série de clusters tem n! tuplas e pesos w^n com
|w| ≲ (2β)^{|C|}: o fator 2^{n²/2} DEVORA qualquer (2β)^n — nenhuma
região de β sobrevive. A convergência de KP precisa de |φ| ≤ #árvores
≤ n^{n−2} ~ e^{n log n}, que casa com o 1/n! (n! ~ e^{n log n}) e
deixa a pequenez de β decidir. CONCLUSÃO HONESTA: a rota A é
infraestrutura e sanidade (e A3 já é conteúdo real: árvores atingem a
igualdade |φ| = #árvores=1... nota: para árvore, #spanning trees da
árvore = 1 e |φ| = 1 ✓ consistente com Penrose), mas SÓ B fecha
convergência. A é o degrau para subir com a perna certa, não o teto.

## Recomendação do executor
39ª = Rota A completa (A1, A2, A3 na formulação por pontes se a API
de árvores for magra, A4). Uma pedra, risco baixo-médio, testa toda a
infraestrutura de cardinalidade que B vai precisar. B1 (Penrose) como
40ª+ com estado próprio e desenho detalhado da involução — merece o
mesmo tratamento que deste à joint law: mapa antes, pedra depois.

## Verificações prévias para a 39ª (se autorizada)
- Finset.abs_sum_le_sum_abs (nome/forma em ℤ).
- Finset.card_powerset; card_le_card (mono de filter).
- SimpleGraph.IsTree / IsAcyclic / bridges / deleteEdges na v4.15:
  censo antes de escolher a formulação de A3.

Aguardo parecer. — Fable
