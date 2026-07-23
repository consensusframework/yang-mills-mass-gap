# PEDRA 45 — ESTADO E MAPA EM DOIS NÚCLEOS (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 45ª.**
Base: main pós-44ª (46 arquivos, ~392 teoremas, 0 axiomas, 0 sorry; a 44ª
passou verde NA PRIMEIRA RODADA — o bound pontual era replay literal do
hprodbound interno da 32ª, e norm_integral_le_integral_norm da v4.15
dispensa integrabilidade).

## 45a — COBERTURA DAS INCOMPATIBILIDADES POR LINKS

Alvo, para a : Finset (Site N × Dir × Dir) → ℝ com (ha : ∀ D, 0 ≤ a D),
no universo finito `allPlaquettePolymers N` (36ª):

  Σ_{D ∈ allPolymers, ¬PlaquetteCompatible C D} a D
    ≤ Σ_{ℓ ∈ blockLinkSupport C}
        Σ_{D ∈ allPolymers, ℓ ∈ blockLinkSupport D} a D

Insumos reais já verificados:
- ¬PlaquetteCompatible C D ↔ ¬Disjoint (blockLinkSupport C)
  (blockLinkSupport D) (def da 35ª) ⟹ ∃ ℓ comum
  (`Finset.not_disjoint_iff` — censar; deve existir na v4.15);
- sobrecontagem por múltiplos links ACEITA (desigualdade, não igualdade).

Rota formal (a mais simples que preserva tudo):
1. lema de cobertura: o filtro dos incompatíveis está contido no biUnion
   sobre ℓ ∈ blockLinkSupport C dos filtros {D : ℓ ∈ support D};
2. `Finset.sum_le_sum_of_subset_of_nonneg` para entrar no biUnion;
3. `Finset.sum_biUnion_le`-tipo: Σ_{biUnion} ≤ Σ_ℓ Σ_{filtro ℓ} — para
   não negativos; censar nome exato (candidatos: `Finset.sum_biUnion_le`
   em ordem, ou provar localmente por indução no Finset de links — a
   indução local é curta e aceita sobrecontagem trivialmente).
4. especialização documentada a a(D) = |polymerWeight β χ D| · exp(α·|D|)
   (não negativa via abs_nonneg · exp_pos) — SÓ a forma, nenhuma soma
   avaliada.

Mais o bound simples do suporte:
  `(blockLinkSupport C).card ≤ 4 * C.card`
via `blockLinkSupport = biUnion plaqLinkSet` + `card_biUnion_le` (censar)
+ `plaqLinkSet` tem ≤ 4 elementos (`card_insert_le` em cadeia — a def é
literal de 4 pares, card ≤ 4 sai por `Finset.card_le_card` de inserts ou
por decide na forma {a,b,c,d}).

Custo: MÉDIO. 1 arquivo, ~8-10 lemas. Nenhuma constante nova.

## 45b — CONTAGEM DE POLÍMEROS ENRAIZADOS (núcleo geométrico)

Objetos a definir/censar ANTES (as fórmulas abaixo são conjecturas de
projeto a VERIFICAR no modelo real, não afirmações):

1. `plaquettesUsingLink ℓ := {p ∈ admissiblePlaquettes : ℓ ∈ plaqLinkSet p}`
   e a constante M(d) = max_ℓ card — a verificar na lattice real: cada
   link (x,μ) pertence às plaquetas (x,μ,ν) e vizinhas transladadas;
   contagem esperada O(d), a forma exata (2(d−1)? com as 4 posições do
   plaqLinkSet: até 4·(d−1)?) SÓ após censo geométrico com `decide` em
   d pequeno ou prova direta — não afirmar 2(d−1) sem verificar;
2. grau máximo Δ(d) do grafo plaquetteShareLink:
   Δ ≤ 4·(M(d)−1) via os 4 links da plaqueta — rota clara;
3. contagem de conjuntos conexos: #{D : |D|=k, p₀∈D, IntrinsicallyConnected}
   ≤ f(Δ)^k — rota clássica por injeção em árvores geradoras enraizadas
   de grau ≤ Δ; a versão FRACA Δ^{2(k−1)} (passeio de Euler dobrado sobre
   a árvore da 40ª!) reutiliza nossa própria infraestrutura de
   penroseTree e evita formalizar contagem de árvores de Cayley;
4. corolário com link fixo: polímeros com ℓ no suporte = união sobre
   p ∈ plaquettesUsingLink ℓ dos que contêm p ⟹ fator M(d) extra.

Separação exigida pelo parecer:
- M(d), Δ(d), f(Δ): dependem SÓ de d (número de direções, tipo Dir) —
  constantes uniformes em N;
- allPlaquettePolymers, suportes: dependem de N apenas como domínio;
- os bounds finais 45b: uniformes em N por construção (vizinhanças locais).

Custo: ALTO (o maior degrau restante). Recomendo 45b como pedra própria
após a 45a, possivelmente dividida em 45b-i (M(d), Δ(d) — decide/prova
direta na geometria) e 45b-ii (contagem via passeio dobrado na árvore BFS).

## RECOMENDAÇÃO

45ª = 45a apenas (cobertura + card do suporte ≤ 4|C|). A 45b vira 46ª
com Etapa Zero geométrica dedicada. Uma frente por vez.

## O QUE NÃO ENTRA (qualquer variante)

Avaliação de somas, série de cluster, log realZ, Kotecký–Preiss,
convergência, limite termodinâmico, decaimento, massa.

**Aguardando parecer. Nada será implementado antes.**
