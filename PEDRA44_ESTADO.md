# PEDRA 44 — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 44ª.**
Base: main em `eb81b8e` (43ª integrada: bound hard-core por árvores, verde na
3ª rodada; 45 arquivos, ~383 teoremas, 0 axiomas, 0 sorry).
Vilões da 43ª no atlas: (i) `Finset.prod_boole` estourou whnf-timeout na
unificação da instância Decidable com Classical — vacina: by_cases +
prod_eq_one/prod_eq_zero; (ii) `Subsingleton (Fin (0+1))` não sintetiza —
vacina: Fin.ext + omega; (iii) rw fecha `Reachable v v` sozinho (@[refl]).

## A. BOUND INDIVIDUAL DA ATIVIDADE — |polymerWeight β χ C| ≤ (2β)^|C|

Estado real dos insumos:
- `polymerWeight β χ C = gibbsExpectation μm 0 χ (blockActivity β χ C)` com
  `blockActivity = ∏_{p∈C} plaquetteActivity β χ p` (34ª);
- em β'=0 a gibbsExpectation é a integral no estado produto de Haar
  (probabilidade) — `|∫ f| ≤ ∫ |f|` + cota pontual bastam;
- 32ª: `|plaquetteActivity β χ p U| ≤ 2β` PONTUAL (para |χ|≤1, β≥0).

Rota (1 arquivo, ~6 lemas):
1. cota pontual do produto: `|blockActivity β χ C U| ≤ (2β)^C.card`
   (`Finset.abs_prod` + `Finset.prod_le_prod` com fatores ≥ 0 — censar ambos);
2. integrabilidade já disponível (34ª integra blockActivity);
3. `abs_integral_le_integral_abs` + monotonia da integral + integral de
   constante em probabilidade (= constante);
4. capstone `abs_polymerWeight_le : β ≥ 0 → (∀U p, |χ …| ≤ 1) →
   |polymerWeight β χ C| ≤ (2*β)^C.card`.
Risco: plumbing MeasureTheory (integral_mono precisa integrabilidade dos
dois lados — constante ok). Custo BAIXO-MÉDIO. Hipótese sobre χ: manter a
mesma forma usada na 32ª (physicalCharacter satisfaz).

## B. SOMA DE INCOMPATIBILIDADES

Alvo estrutural (sem série): para C polímero e a ≥ 0,
  Σ_{D ∈ polímeros, ¬Compat(C,D)} |w(D)| e^{a|D|}
    ≤ Σ_{ℓ ∈ blockLinkSupport C} Σ_{D ∋ usa ℓ} |w(D)| e^{a|D|}.
Insumo geométrico: ¬PlaquetteCompatible C D ↔ ∃ link comum nos suportes
(def 35ª: ¬Disjoint blockLinkSupport). A desigualdade é uma cobertura de
conjuntos (cada D incompatível é contado por ≥1 link): rota
`Finset.sum_le_sum_of_subset` + `sum_biUnion_le` (censar; existe
`Finset.sum_biUnion_le`? senão via `sum_le_sum_of_subset_of_nonneg` na
união indexada). PURAMENTE finito no volume fixo. Custo MÉDIO.
Observação honesta: nesta pedra a soma é sobre o conjunto FINITO
allPlaquettePolymers do volume — nenhuma soma infinita.

## C. GARGALO GEOMÉTRICO — contagem de polímeros contendo plaqueta/link fixo

O que se precisa no fim: #{D polímero conexo : |D| = k, p₀ ∈ D} ≤ M^k com
M dependendo APENAS do grau máximo Δ do grafo de adjacência de plaquetas.
Fatos sobre Δ no nosso reticulado: cada plaqueta tem 4 links; cada link
está em ≤ 2(d−1) plaquetas admissíveis (d = número de direções, fixo pela
def Dir) ⟹ Δ ≤ 4·(2(d−1)−1)+... — a constante exata deve ser provada, mas
é UNIFORME NO VOLUME (não depende de N): vizinhança de uma plaqueta é
local. O que depende de d: Δ e portanto M. O que é uniforme em N: tudo —
nenhuma constante da 44ª/45ª deve mencionar N além do domínio.
Rota clássica: injetar polímeros conexos de tamanho k com raiz p₀ em
passeios/árvores de grau ≤ Δ (contagem ≤ (e·Δ)^k ou versão fraca Δ^{2k}
via passeio de Euler dobrado). Formalizar isso é pedra INTEIRA (45ª),
possivelmente dividida: (45a) grau máximo do grafo de plaquetas ≤ c(d);
(45b) contagem de subárvores enraizadas. Custo ALTO — o maior degrau
restante antes do critério.

## RECOMENDAÇÃO

44ª = A sozinho (bound da atividade), com B como 44b se o parecer preferir
uma entrega dupla. C fica para a 45ª em duas partes. Ordem: A é pré-requisito
de qualquer critério; B usa só geometria já pronta da 35ª; C é o gargalo
real e merece pedra própria com Etapa Zero dedicada (Walk/Subtree APIs).

## O QUE NÃO ENTRA (qualquer variante da 44ª)

Série de cluster, log realZ, Kotecký–Preiss, limite termodinâmico,
decaimento, massa; nenhuma contagem de polímeros (isso é a 45ª).

**Aguardando parecer. Nada será implementado antes.**
