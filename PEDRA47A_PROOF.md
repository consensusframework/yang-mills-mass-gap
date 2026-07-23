# PEDRA 47a-P — PROVA EM PAPEL: A INDUÇÃO DE KOTECKÝ–PREISS FINITA
## (documento técnico para parecer; NÃO é pedra verificada; nenhum Lean)

Autoria da prova: Claude Fable 5, sob arquitetura de GPT-5.6 (Sol).
Status: manuscrito para auditoria adversarial (Kimi) e parecer (Sol).
Convenções: P = universo finito de polímeros no volume fixo
(allPlaquettePolymers N); ρ : P → ℝ≥0; a : P → ℝ≥0; "η ≁ γ" denota
¬PlaquetteCompatible (suportes de links se intersectam) — relação
REFLEXIVA no nosso gás (γ ≁ γ sempre, pois o suporte é não vazio).
φ(γ₀,…,γₙ) := ursellCoeff da tupla (37ª), invariante por permutação
incluindo multiplicidades (38ª).

---

## 1. DEFINIÇÕES EXATAS

Para γ₀ ∈ P e n ∈ ℕ:

  Aₙ(γ₀) := (1/n!) · Σ_{γ : Fin n → P} |φ(γ₀ :: γ)| · Π_{i<n} ρ(γᵢ)

onde γ₀ :: γ é a tupla Fin (n+1) → P com valor γ₀ no índice 0 e
γ(i−1) nos demais (na implementação futura: Fin.cons). Registros:

- A₀(γ₀) = |φ(γ₀)| = 1 (caso unitário da 37ª);
- a atividade ρ(γ₀) da raiz NÃO aparece (ela entra só na 48ª);
- repetições são permitidas: γ pode assumir o mesmo polímero em
  vários índices — e como ≁ é reflexiva, tais tuplas têm grafo de
  incompatibilidade com arestas entre as cópias: são termos
  matematicamente relevantes, não degenerados;
- as ocorrências são rotuladas por Fin n; a 38ª garante que φ só
  depende da tupla não ordenada COM multiplicidades.

CONVENÇÃO DE VÉRTICES (fixada antes de qualquer indicador de aresta):
o vértice 0 carrega γ₀; o vértice i.succ carrega γ(i); a atividade da
raiz γ₀ NÃO aparece no produto de atividades; cada um dos n demais
vértices contribui exatamente uma vez ao produto Π ρ(γᵢ).

O majorante de árvores (mesma normalização):

  Tₙ(γ₀) := (1/n!) · Σ_{γ : Fin n → P} Σ_{T ∈ Árvores({0,…,n})}
              Π_{{i,j} ∈ T} 1[γᵢ ≁ γⱼ] · Π_{i<n} ρ(γᵢ)

com γ₀ no índice 0, e Árvores(V) = árvores geradoras rotuladas do
completo sobre V. T₀(γ₀) = 1 (árvore única sem arestas, produtos
vazios).

## 2. TREE-GRAPH MAJORANT (43ª consumida, nada reprovado)

A 43ª dá, para cada tupla fixa — TEOREMA EXATO CONSUMIDO:
`ursellCoeff_hardCoreTree_bound` (PolymerTreeBound.lean):
  (ursellCoeff γtupla).natAbs
    ≤ Σ_{ET ∈ spanningTreeEdgeSets ⊤} hardCoreTreeIndicator γtupla ET
i.e.  |φ(γ₀ :: γ)| ≤ Σ_{T} Π_{{i,j}∈T} 1[γᵢ ≁ γⱼ].
Multiplicando por Πρ ≥ 0 e somando: **Aₙ(γ₀) ≤ Tₙ(γ₀)** para todo n.

## 3. DECOMPOSIÇÃO DA ÁRVORE NA RAIZ

Seja T árvore sobre {0,…,n}, n ≥ 1, e remova o vértice 0. Fatos
(todos elementares, todos a virar lemas na 47b):

(i) restam k := deg_T(0) ≥ 1 componentes conexas C₁,…,C_k;
(ii) cada Cⱼ contém EXATAMENTE UM vizinho de 0 em T (dois vizinhos na
     mesma componente fechariam um ciclo por 0); chame-o rⱼ;
(iii) os conjuntos de rótulos Vⱼ := V(Cⱼ) formam uma partição de
     {1,…,n} em blocos não vazios;
(iv) cada Cⱼ é uma árvore sobre Vⱼ;
(v) o peso hard-core fatoriza:
     Π_{{i,j}∈T} 1[γᵢ≁γⱼ]
       = Πⱼ ( 1[γ_{rⱼ} ≁ γ₀] · Π_{{i,j}∈Cⱼ} 1[γᵢ≁γⱼ] );
(vi) Π_{i≥1} ρ(γᵢ) = Πⱼ Π_{i∈Vⱼ} ρ(γᵢ) — a atividade de cada filho
     pertence à sua componente.

Reciprocamente, os dados (k; família NÃO ordenada de pares (Vⱼ, rⱼ)
com árvore tⱼ sobre Vⱼ) reconstroem T unicamente (arestas 0–rⱼ mais
as arestas dos tⱼ). A correspondência é bijetiva.

## 4. RECORRÊNCIA EXATA — auditoria completa dos fatoriais

**Afirmação.** T₀(γ₀) = 1 e, para n ≥ 1,

  Tₙ(γ₀) = Σ_{k=1}^{n} (1/k!) Σ_{n₁+⋯+n_k = n−k, nⱼ ≥ 0}
             Πⱼ ( Σ_{ηⱼ ∈ P} 1[ηⱼ ≁ γ₀] · ρ(ηⱼ) · T_{nⱼ}(ηⱼ) )

(composições ORDENADAS (n₁,…,n_k); soma externa finita).

**Prova/auditoria.** Trabalhe com n!·Tₙ (sem o 1/n!). Pela bijeção do
§3, e trocando a família não ordenada de k componentes por sequências
ordenadas divididas por k!:

  n!·Tₙ(γ₀) = Σ_{k≥1} (1/k!) Σ_{(B₁,…,B_k) partição ordenada de [n]}
                Πⱼ F(Bⱼ)                                            (★)

onde F(B) := Σ_{r∈B} Σ_{t árvore sobre B} Σ_{γ:B→P}
  1[γ_r ≁ γ₀] · Π_{t} 1[γᵢ≁γⱼ] · Π_{i∈B} ρ(γᵢ).

JUSTIFICATIVA DO k! EXATO: os blocos são distinguíveis COMO CONJUNTOS
DE RÓTULOS (disjuntos e não vazios), logo cada família não ordenada
corresponde a exatamente k! sequências — mesmo quando os valores
ηⱼ dos polímeros-raiz coincidem, os Bⱼ diferem; não há estabilizador.
(Ponto 1 da lista adversarial.)

CÁLCULO DE F(B) para |B| = m+1: fixe r ∈ B e uma bijeção qualquer de
B∖{r} com {1,…,m} (r ↦ 0). A soma sobre (t, γ) é invariante pela
relabelagem — LEMA DE RELABELAGEM (enunciado preciso, a formalizar na 47b-i):
para tipos finitos V, V′ com |V| = |V′| = m+1, uma equivalência
σ : V ≃ V′, uma marca r ∈ V com r′ := σ(r), e η ∈ P:
  Σ_{t ∈ Árvores(V)} Σ_{γ : V → P, γ(r) = η}
      Π_{{i,j}∈t} 1[γᵢ≁γⱼ] · Π_{i∈V∖{r}} ρ(γᵢ)
    = Σ_{t′ ∈ Árvores(V′)} Σ_{γ′ : V′ → P, γ′(r′) = η}
      Π_{{i,j}∈t′} 1[γ′ᵢ≁γ′ⱼ] · Π_{i∈V′∖{r′}} ρ(γ′ᵢ)
(a bijeção t ↦ σ(t), γ′ := γ ∘ σ⁻¹ preserva adjacência, indicadores
e o produto reindexado de atividades). REALIZAÇÃO LEAN: como o nosso
OrderedEdge usa a ordem de Fin, a versão formal será por permutações
de Fin (m+1) via a maquinaria canônica da 38ª (canonicalOrderedEdge/
relabelEdgeSet), composta com Finset.equivFin para blocos — logo

  Σ_{t sobre B} Σ_{γ:B→P, γ_r = η} (…) = m! · T_m(η) · [coef. já
    normalizado: por definição T_m(η) = (1/m!)·(a mesma soma sobre
    {0,…,m} com raiz η)]

e portanto — com a expressão m!·T_m(η) contendo atividades SOMENTE
nos vértices B∖{r}, o fator ρ(η) da raiz marcada colocado
externamente exatamente uma vez —
F(B) = Σ_{r∈B} Σ_η 1[η≁γ₀] ρ(η) · m!·T_m(η)
              = (m+1) · m! · Σ_η 1[η≁γ₀] ρ(η) T_m(η).

CONTAGEM DAS PARTIÇÕES ORDENADAS por tamanhos: para (n₁+1,…,n_k+1)
fixos com Σ(nⱼ+1) = n, há n!/Πⱼ(nⱼ+1)! partições ordenadas. Inserindo
em (★):

  n!·Tₙ = Σ_k (1/k!) Σ_{n₁+⋯+n_k=n−k}
            [ n!/Πⱼ(nⱼ+1)! ] · Πⱼ (nⱼ+1)·nⱼ! · Πⱼ(Σ_η 1 ρ T_{nⱼ}(η))

e o cancelamento central é, POR BLOCO:

  (nⱼ+1) · nⱼ! / (nⱼ+1)! = 1        (ponto 2 da lista adversarial)

deixando exatamente n!·Σ_k (1/k!) Σ_{comps} Π(Σ_η …). Divida por n!. ∎

Nenhuma "fórmula exponencial" foi invocada; a contagem é a bijeção do
§3 mais três fatoriais elementares.

## 5. AUDITORIA EM BAIXA ORDEM

n = 1: única árvore (aresta 0–1). T₁ = Σ_η 1[η≁γ₀]ρ(η).
Recorrência: k=1, n₁=0: Σ_η 1 ρ T₀(η) = Σ_η 1[η≁γ₀]ρ(η). ✓

n = 2: três árvores sobre {0,1,2} — estrela (01,02), cadeia 0–1–2
(01,12), cadeia 0–2–1 (02,12... i.e. arestas {0,2},{1,2}).
  T₂ = (1/2)Σ_{γ₁γ₂} [1[1≁0]1[2≁0] + 1[1≁0]1[2≁1] + 1[2≁0]1[1≁2]]ρρ.
Recorrência:
  k=1 (n₁=1): Σ_η 1[η≁γ₀]ρ(η)T₁(η) = Σ_{η,η'} 1[η≁γ₀]1[η'≁η]ρρ —
  que é (1/2)(cadeia₁ + cadeia₂) após troca dos índices mudos. ✓
  k=2 (n₁=n₂=0): (1/2!)(Σ_η1[η≁γ₀]ρ)² = (1/2)Σ_{η,η'}1[η≁γ₀]1[η'≁γ₀]ρρ
  = termo estrela. ✓

n = 3: 16 = 4² árvores (Cayley). Por grau da raiz: deg 1: 3 árvores
sobre o bloco de 3 × 3 marcas = 9; deg 2: 3 partições {a,b}|{c} × 2
marcas no bloco de 2 = 6; deg 3: 1 estrela. 9+6+1 = 16 ✓, e os três
grupos correspondem a k=1 (Σ_η 1ρT₂), k=2 (1/2! sobre comps (1,0) e
(0,1)) e k=3 (1/3!(Σ)³ — as 3! ordenações da estrela). ✓ O fator k!
está auditado em três ordens.

## 6. SOMAS PARCIAIS

  S_M(γ) := Σ_{n=0}^{M} Tₙ(γ).

NÃO NEGATIVIDADE EXPLÍCITA (registrada ANTES de qualquer extensão):
0 ≤ Tₙ(γ) (soma de produtos de indicadores e ρ ≥ 0), logo
0 ≤ S_M(γ), logo 0 ≤ X := Σ_{η≁γ₀} ρ(η)·S_{M−1}(η). A desigualdade
da exponencial truncada Σ_{k≤M} X^k/k! ≤ e^X será usada SOMENTE após
X ≥ 0 estabelecido.

Para n ≥ 1 na recorrência, k ≥ 1 força cada nⱼ ≤ n−k ≤ M−1 — logo só
T_{nⱼ} com nⱼ ≤ M−1 aparecem (ponto do item 6 da fita). Como todos os
termos são ≥ 0, ESTENDER a soma sobre composições ao produto de somas
independentes só aumenta (cada composição (n₁..n_k) com Σ = n−k ≤ M−k
aparece no produto Π(Σ_{nⱼ=0}^{M−1}·) exatamente uma vez, entre
outros termos ≥ 0 — ponto 3 da lista adversarial):

  S_M(γ₀) ≤ 1 + Σ_{k=1}^{M} (1/k!) Πⱼ ( Σ_{nⱼ<M} Σ_η 1 ρ T_{nⱼ}(η) )
          = Σ_{k=0}^{M} (1/k!) · X^k,   X := Σ_{η≁γ₀} ρ(η)·S_{M−1}(η).

Nenhuma série infinita: ambos os lados são somas finitas.

## 7. INDUÇÃO KP FINITA

**Hipótese (KP, provada na 46ª para o nosso gás):**
  ∀γ: Σ_{η≁γ} ρ(η)·e^{a(η)} ≤ a(γ),  com a ≥ 0.

**MOTIVO DE INDUÇÃO (correção do Kimi — SIMULTÂNEO em todas as
raízes):**
  P(M) := ∀ γ, S_M(γ) ≤ e^{a(γ)}.
A indução é em M com TODAS as raízes quantificadas dentro do motivo:
não é indução para raiz fixa, porque o passo para γ₀ consulta
S_{M−1}(η) para TODO η — inclusive η = γ₀.

Base P(0): ∀γ, S₀(γ) = T₀(γ) = 1 ≤ e^{a(γ)} pois a(γ) ≥ 0 (ponto 4 —
no nosso gás a(D) = |D| ≥ 1 > 0 ✓).
Passo P(M−1) ⟹ P(M): fixe γ₀; a hipótese P(M−1) dá
∀η, S_{M−1}(η) ≤ e^{a(η)} ⟹
  X ≤ Σ_{η≁γ₀} ρ(η)e^{a(η)} ≤ a(γ₀)   [hipótese KP — usada UMA vez,
    sem circularidade: é insumo da 46ª, não desta indução — ponto 7]
  S_M(γ₀) ≤ Σ_{k=0}^{M} X^k/k! ≤ e^X ≤ e^{a(γ₀)}
(exponencial truncada ≤ Real.exp para X ≥ 0; monotonicidade de exp).∎

## 8. RESULTADO ENRAIZADO FINITO

Para todo M:   Σ_{n=0}^{M} Aₙ(γ₀) ≤ S_M(γ₀) ≤ e^{a(γ₀)},
e recolocando a raiz:   ρ(γ₀)·Σ_{n≤M} Aₙ(γ₀) ≤ ρ(γ₀)·e^{a(γ₀)}.
A PRIMEIRA forma é a interface principal (a segunda é corolário).

## 9. APLICAÇÃO AO NOSSO GÁS (só papel)

ρ(D) := |polymerWeight β χ D| — NÃO NEGATIVA por construção (valor
absoluto); a(D) := D.card ≥ 0 (de fato ≥ 1 para polímeros);
0 ≤ β ≤ 1/40000. A 46ª (kp_hypothesis_beta_le_one_div_40000) fornece
a hipótese do §7 PARA TODA raiz D, sem caso especial de raiz pesada. Conclusão: TODAS as somas parciais da
expansão enraizada em D₀ são ≤ exp(D₀.card). Sem Summable.

## 10. STATUS EPISTÊMICO

PROVADO NESTE MANUSCRITO (condicionado à auditoria): bound uniforme
das somas parciais; raiz sem atividade; repetições preservadas;
1/n! e 1/k! auditados (§4-5). NÃO FORMALIZADO: nenhuma definição
Lean; nenhum Summable; nenhuma convergência no kernel; nenhum log Z.

## 11. MAPA LEAN (recomendação única: ARQUITETURA A)

A. coeficientes Tₙ como defs por n (somas finitas sobre
   (Fin n → P) ×ˢ trees — tudo Finset) + somas parciais por
   Finset.range + os lemas: relabel de somas de árvores (§4),
   bijeção da decomposição na raiz (§3), recorrência, extensão a
   produto, indução. Summable NUNCA aparece.
B. (rejeitada agora) família Σ n, Fin n → P com tsum: adia nada e
   antecipa API de séries.
C. (rejeitada) power series formais: máquina demais.

## 12. PORTÃO E LACUNAS DECLARADAS

O único lema de partição necessário é o do §3/§4: bijeção
árvores ↔ (partição ordenada com marcas)/k!, com a versão Lean
proposta SEM quocientes e SEM divisão em tipos discretos:
- dados ordenados de componentes empacotados como sequências
  Fin k → (Σ m : ℕ, ComponentData m) — o Σ-empacotamento evita
  transportes heterogêneos entre blocos de tamanhos distintos;
- ação de Equiv.Perm (Fin k) por PRÉ-COMPOSIÇÃO nas sequências;
- a ação é LIVRE porque os blocos são disjuntos, não vazios e
  distintos como conjuntos de rótulos (sem estabilizador);
- órbita-estabilizador com estabilizador trivial, formulado
  MULTIPLICATIVAMENTE:
    card (orderedData) = k! * card (unorderedFamilies).
Se a contagem órbita-estabilizador não fechar, a lacuna estará
EXATAMENTE aí e será formulada isolada. Nenhuma identidade de
espécies é necessária.

## LISTA EXPLÍCITA PARA REVISÃO ADVERSARIAL (Kimi)

1. Exatidão do k! com valores repetidos de ηⱼ (blocos = conjuntos de
   rótulos distintos; sem estabilizador). §4.
2. Cancelamento (nⱼ+1)·nⱼ!/(nⱼ+1)! = 1 e a multinomial n!/Π(nⱼ+1)!.
3. Passo de extensão composições → produtos independentes (usa SÓ
   não negatividade; verificar que não há dupla contagem NO SENTIDO
   ERRADO — é majorante, não igualdade). §6.
4. Base da indução exige a ≥ 0 — conferir se a definição final usará
   a(D) = |D| (≥ 1) ou precisa de a ≥ 0 explícito no enunciado.
5. Reflexividade de ≁: η = γ₀ é permitido na soma dos filhos
   (1[γ₀≁γ₀] = 1); conferir que nenhum passo assumiu η ≠ γ₀.
6. Invariância por relabelagem da soma de árvores (F(B) independe da
   bijeção escolhida) — será lema Lean; conferir o argumento.
7. Não circularidade: a hipótese KP entra apenas no passo do §7.
8. A remoção da raiz (§3): conferir (ii) — unicidade do vizinho por
   componente — e a reconstrução bijetiva.

**Nenhuma alteração em main. Nenhum commit de README. Não conta como
pedra. Aguardando: parecer de Sol + ataque de Kimi.**
