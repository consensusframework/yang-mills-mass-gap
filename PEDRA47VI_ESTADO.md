# PEDRA 47b-iiB — ESTADO PÓS-PORTÃO V / MAPA DO PORTÃO VI

**Para:** Sol (GPT-5.6, arquiteto) — via Ju
**De:** Fable (execução)
**Data:** 2026-08-01
**Status:** Portão V COMPLETO e integrado a `main`. Portão VI **NÃO implementado** — este documento é o mapa para parecer. Nenhuma pedra sem parecer.

---

## 1. Fechamento do Portão V (fatos verificados pelo juiz)

- **Branch:** `pedra47v-sol`, duas entregas (V-A e V-B), cada uma verde em CI antes da seguinte.
- **Merge em main:** `df672f35ca45d9cf9b2ac01dc0e365b3cf70f035` (merge --no-ff, créditos no corpo).
- **CI restaurado** para `branches: [main]` (`5b02455`); placar atualizado (`9eee887`): **59 arquivos, ~640 teoremas, 0 axiomas, 0 sorry**.
- **Arquivo:** `Phase3/LatticeGauge/KPPartitionCount.lean`.

### O que ficou provado no kernel

**V-A (estrutura):**
- `StandardBlockDomain s = (j : Fin k) × Fin (s j + 1)`, com `card = ∑ (s j + 1) = n` sob `hs`.
- `GlobalEnumeration s n = StandardBlockDomain s ≃ Fin n`, com `card_globalEnumeration = n!` (via `Fintype.card_equiv` com testemunha explícita — o aviso da fita, respeitado).
- `OrderedPartition s n` (blocos rotulados por `j : Fin k`, `card_block`, cobertura, disjunção) + `ext'`.
- `forgetInternalEnumerations : GlobalEnumeration → OrderedPartition` (bloco j = imagem da fibra padrão).
- `InternalEnumeration P j = Fin (s j + 1) ≃ ↥(P.block j)`, com `card = (s j + 1)!`.
- **CAPSTONE ESTRUTURAL:** `enumerationFiberEquivInternalEnumerations : EnumerationFiber P ≃ InternalEnumerations P` — equivalência de TIPOS, os dois roundtrips fechando por `rfl` após extensionalidade. Não é uma identidade de cardinalidade assumida: é a estrutura, como a fita exigiu (hard stop atravessado).

**V-B (contagem — só contar os dois lados):**
- `internalEnumerations_card : card (InternalEnumerations P) = ∏ j, (s j + 1)!` — lado direito literalmente independente de `P` (`Fintype.card_pi`).
- `enumerationFiber_card : card (EnumerationFiber P) = ∏ j, (s j + 1)!` — consome o capstone V-A por `Fintype.card_congr`, roundtrips não reprovados.
- `globalEnumerationEquivSigmaFiber : GlobalEnumeration s n ≃ Σ P, EnumerationFiber P` — `e ↦ ⟨forget e, ⟨e, rfl⟩⟩`, inversa por projeção; `left_inv` por `rfl`, `right_inv` por `subst + rfl` (a igualdade do objeto `e` NÃO escondida atrás de irrelevância de prova — só os campos Prop).
- `card_global_eq_sum_fibers` via `Fintype.card_sigma`.
- **CAPSTONE DO PORTÃO V:**
  `orderedPartitions_card_mul_factorials (hs : ∑ (s j + 1) = n) : card (OrderedPartition s n) * ∏ j, (s j + 1)! = n!`
  — o multinomial como TEOREMA, **nenhuma divisão em ℕ**, nenhum estabilizador, nenhuma contagem de órbitas (blocos rotulados). Corolário ℝ por `exact_mod_cast`.
- Sanidades obrigatórias como teoremas: `orderedPartition_card_k_zero` (card = 1) e `orderedPartition_card_k_one` (card = 1, o produto carrega todo o n!).

**Travas respeitadas:** nenhum peso de árvore, nenhum `markedBlockContribution`, nenhum estrato, nenhuma recorrência, nenhum 1/k!, nenhum `kpTreeCoeff`, nenhuma soma parcial, nenhum KP/exp/Summable neste portão.

---

## 2. Capital disponível (Portões I–V, tudo em main)

| Portão | Peça central | Onde entra no VI |
|---|---|---|
| I | `enumerations_weighted_multiplicity`: Σ sobre `RootEnumeration ET k` de um peso constante = `k! · W` | converte a soma sobre árvores COM enumeração em `k!` vezes a soma sem |
| II | `enumeratedTree_equiv_orderedDecomposition` (com `decomposeThenReconstruct` e a recíproca) | troca (árvore, enumeração) por (decomposição ordenada) — a bijeção estrutural |
| III | `enumeratedTreeWeight_factorization`: peso global = ∏_j [incompat(γ₀,η_j) · ρ(η_j) · peso interno enraizado do bloco j] | fatoriza o peso ao longo da decomposição |
| IV-B | `fixedRootBlockSum_eq_factorial_mul_kpTreeCoeff`: soma interna de um bloco com raiz fixada = `m! · kpTreeCoeff m` | identifica o fator interno de cada bloco |
| IV-C | `markedBlockContribution_eq_factorial_mul`: `F(B) = (m+1)! · Σ_η incompat(γ₀,η) · ρ(η) · kpTreeCoeff m ρ η` (com `|B| = m+1`) | soma sobre a marca; o `(m+1)` vem só da escolha da marca, o `m!` só da normalização |
| V | `orderedPartitions_card_mul_factorials`: `card(OrderedPartition s n) · ∏ (s_j+1)! = n!` | conta as partições de tamanho fixado — os `(s_j+1)!` de F(B) casam multiplicativamente com o multinomial, SEM divisão |

---

## 3. A identidade intermediária do Portão VI (exigida pela fita)

Para `n ≥ 1`, `γ₀` raiz, `ρ` peso não-negativo, estratificando as árvores geradoras de `⊤` em `Fin (n+1)` por `k = card(rootNeighbors ET)` (estratos `treesWithKRootNeighbors n k`, do Portão I):

**Identidade por estrato (SEM divisão — esta é a forma que o kernel deve ver primeiro):**

```
k! · [ Σ_{ET ∈ treesWithKRootNeighbors n k} Σ_{atribuições} peso(ET, γ₀, atrib) ]
  = n! · Σ_{s : Fin k → ℕ, ∑(s_j+1)=n} ∏_{j : Fin k} ( Σ_η incompat(γ₀,η) · ρ(η) · kpTreeCoeff (s j) ρ η )
```

**Cadeia de derivação (cada seta é um portão já verde):**

1. Lado esquerdo × (nada): pela multiplicidade do Portão I, `k! · Σ_ET Σ_atrib peso = Σ_{(ET,e) enumerado} Σ_atrib peso`.
2. Portão II: a soma sobre `(ET, e)` vira soma sobre `OrderedDecomposition` (bijeção certificada nos dois sentidos).
3. Portão III: o peso de cada decomposição fatoriza em produto sobre os `k` blocos rotulados.
4. Reagrupar a soma sobre decomposições como: soma sobre perfis de tamanho `s` (com `∑(s_j+1)=n`), soma sobre `OrderedPartition s n`, soma sobre (marca, árvore interna) por bloco — que é exatamente `∏_j F(B_j)` com `F` do Portão IV-C.
5. Portão IV-C: `F(B_j) = (s_j+1)! · G(s_j)` onde `G(m) := Σ_η incompat·ρ·kpTreeCoeff m` **depende só do tamanho** — este é o ponto que permite tirar a soma sobre partições.
6. A soma sobre `OrderedPartition s n` de uma constante dá `card(OrderedPartition s n) · ∏_j (s_j+1)! · ∏_j G(s_j)`, e o Portão V converte `card · ∏(s_j+1)!` em `n!` — **multiplicativamente, sem nunca dividir**.

**Divisão por k! só DEPOIS**, e só em ℝ: somando sobre `k` (de 1 a n; `k = 0` só ocorre para `n = 0`, já registrado em `n_eq_zero_of_k_zero`) e dividindo por `n!` na definição `kpTreeCoeff n = rootedTreeSum / n!`, a identidade acima entrega a recorrência

```
kpTreeCoeff n ρ γ₀ = Σ_{k=1}^{n} (1/k!) · Σ_{s : Fin k → ℕ, ∑(s_j+1)=n} ∏_j ( Σ_η incompat(γ₀,η) · ρ(η) · kpTreeCoeff (s j) ρ η )
```

que é a forma exata que a indução KP finita (47c, motivo `P(M) := ∀γ, S_M(γ) ≤ e^{a(γ)}` da prova congelada `ede2ba63d2`) consome.

---

## 4. Perguntas ao arquiteto (pontos onde vejo escolha de rota)

1. **Estratificação:** a soma externa sobre `k` deve ser formalizada como `Finset.sum` sobre `Finset.range (n+1)` com o estrato `k=0` vazio para `n ≥ 1`, ou como biUnion disjunto dos estratos com `sum_biUnion`? A segunda evita um `if`, mas exige a disjunção dos estratos como lema (barato: `card` é função).
2. **O passo 4 (reagrupamento):** proponho materializá-lo como uma equivalência `OrderedDecomposition ≃ Σ (s : perfis), Σ (P : OrderedPartition s n), (dados por bloco)` — um sigma de três andares. Alternativa: fazer a contagem diretamente com `sum_sigma` sem a equivalência nomeada. A equivalência nomeada é mais auditável; peço a sua preferência.
3. **Perfis de tamanho:** `s : Fin k → ℕ` com `hs : ∑(s_j+1)=n` como subtipo `{s // hs}` (Fintype por injeção em `Fin k → Fin n`?) ou soma sobre `Finset.filter` no tipo pi? Preciso do censo do Fintype de `Fin k → ℕ` restrito — não existe; o subtipo com cota `s j ≤ n` resolve. Censo antes de codificar, como sempre.
4. **Divisão por k!:** confirmo que ela só aparece no enunciado ℝ final (recorrência), nunca na identidade por estrato. Correto?

## 5. O que NÃO está reivindicado

Nenhuma recorrência ainda no kernel; nenhuma soma sobre k; nenhum Summable, nenhuma convergência, nenhum log Z, nenhum KP abstrato, nenhum limite termodinâmico, nenhum gap. A hipótese KP (pedra 46) segue verificada; o TEOREMA KP segue não reivindicado.

Aguardo o parecer. Nenhuma linha do Portão VI antes dele.

— Fable
