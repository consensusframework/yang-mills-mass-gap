# PEDRA 36 — MAPA: O GÁS FINITO DE POLÍMEROS E A REINDEXAÇÃO DE Z
# (os sete pontos do teu parecer; NENHUMA implementação até autorização)

## 1. Para Γ compatível, union Γ é admissível
union Γ := Γ.biUnion id. Cada X ∈ Γ é polímero ⟹ X ⊆ admissible;
biUnion de subconjuntos ⊆ admissible: Finset.biUnion_subset (VERIFICAR
nome v4.15; fallback: mem_biUnion + destruição). BAIXO.

## 2. Cada C ∈ Γ está contido num componente de union Γ
C auto-conexo e C ⊆ union Γ ⟹ C conexo DENTRO de union Γ. Precisa da
MONOTONIA: connectedWithin C a b → C ⊆ B → connectedWithin B a b.
Prova: mapa de Walks ao longo da inclusão — indução em Walk (mesmo
padrão da 35ª; a adjacência induzida é defeq à ambiente nos dois
lados, então o cons transporta trivialmente). MÉDIO-BAIXO.

## 3. O caminho em union Γ não atravessa entre polímeros distintos
O segundo núcleo combinatório (previsto no teu corte). Lema: se
W : Walk em induce ↑(union Γ) de u até v, e ↑u ∈ X com X ∈ Γ, então
↑v ∈ X. Indução em Walk: no passo cons u→b, u ∈ X e Adj u b; b ∈
union Γ ⟹ b ∈ Y para algum Y ∈ Γ; se Y ≠ X, compatibilidade ⟹
not_adj_of_plaquetteCompatible (35ª!) contradiz Adj; logo b ∈ X, IH.
Estrutura idêntica à do lema da 35ª — mesmos vilões já vacinados
(rename_i no nil). MÉDIO.

## 4. componentFamily (union Γ) = Γ
ext C; duas inclusões:
⊆: componente D de union Γ contém algum p; p ∈ X ∈ Γ; por §3 todo
   elemento de D está em X (D conexo, caminhos não saem de X) e por
   §2 X ⊆ componente de p = D; logo D = X ∈ Γ.
⊇: X ∈ Γ; tomar p ∈ X (não vazio); mostrar X = plaquetteComponent
   (union Γ) p (mesmo argumento nos dois sentidos) e componente ∈
   componentFamily por mem_image. MÉDIO (burocracia de ext).
NOTA: §4 exige Γ SEM membro vazio — garantido por IsPlaquettePolymer
(Nonempty). O caso Γ = ∅ fecha: componentFamily ∅ = ∅ ✓ (35ª).

## 5. As duas operações são inversas
Direção A: componentFamily A é compatível (35ª) e biUnion = A (34ª) ✓
já provadas. Direção Γ: §1-§4. Empacotar como par de teoremas
"left_inverse/right_inverse" em Finsets (sem Equiv formal — ou COM
Equiv entre subtipos de Finsets? NÃO: sem subtipo; os dois teoremas
bastam para o sum_bij). BAIXO após §4.

## 6. Reindexação exata do realZ (capstone final)
compatibleFamilies N : Finset (Finset (Finset _)) :=
  ((admissiblePlaquettes N).powerset.powerset).filter
    IsCompatiblePolymerFamily
(decidável via Classical, padrão da 33ª).
realZ β χ = ∑ Γ ∈ compatibleFamilies N, ∏ X ∈ Γ, polymerWeight μm β χ X.
Rota: Finset.sum_nbij' (VERIFICAR assinatura v4.15: i/j nos dois
sentidos + hi/hj + inversas + h sobre pesos) com
i := componentFamily, j := (·.biUnion id); pesos batem pela 34ª/35ª
(realZ_eq_sum_prod_polymerWeight). O trabalho todo está nos §1-§4;
o sum_nbij' é burocracia.

## 7. Família vazia
Γ = ∅ ↔ A = ∅: componentFamily ∅ = ∅ e biUnion ∅ = ∅; peso: produto
vazio = 1 — o termo A = ∅ da soma corresponde ao Γ = ∅ do gás. Ambos
os lados incluem o termo trivial; nenhum caso especial artificial.

## Riscos e proposta
- §3 é o núcleo; estrutura já ensaiada na 35ª. Se §4 inflar na
  burocracia de ext/image, proponho separar: 36ª = §1-§4 (bijeção
  geométrica), 37ª = §5-§6 (reindexação) — MAS só se necessário;
  minha estimativa é que cabe numa pedra.
- Verificações prévias obrigatórias: Finset.biUnion_subset,
  Finset.sum_nbij' (ou sum_bij'), formas de mem_powerset aninhado.

Aguardo parecer. — Fable

## Nota da janela (dia 1 de 2)
31ª→35ª: CINCO pedras hoje + três mapas. O realZ já se escreve como
soma de produtos de pesos de polímeros sobre a decomposição canônica;
falta UMA pedra para o gás finito exato.
