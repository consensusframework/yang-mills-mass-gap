# PEDRA 35 — ESTUDO: O NASCIMENTO DO POLÍMERO
# (documento de planejamento; NENHUMA implementação até parecer)

## Alvo (conforme encomendaste no parecer da 34ª)
A bijeção exata
  subconjunto A de plaquetas
    ↔ família finita de conjuntos conexos, não vazios, pairwise
      link-disjoint (as componentes de A)
e a reindexação do realZ como soma sobre FAMÍLIAS COMPATÍVEIS.
Ainda sem convergência.

## 1. Definição mínima proposta de Polymer
Sem tipo novo (fiel à disciplina anti-subtipos):
  def IsPolymer (X : Finset (Site N × Dir × Dir)) : Prop :=
    X.Nonempty ∧ X ⊆ admissiblePlaquettes N ∧
    (∀ a ∈ X, ∀ b ∈ X, connectedWithin X a b)
NOTA CRÍTICA: conexidade DENTRO do próprio X (auto-conexo), não
dentro de um A externo. A 33ª-F entrega conectividade das componentes
DENTRO de A; precisaremos do lema-ponte:
  connectedWithin A a b → (caminho fica no componente) →
  connectedWithin (plaquetteComponent A p) a b
— i.e., o caminho entre elementos do mesmo componente pode ser
tomado inteiramente no componente. Este é o ÚNICO conteúdo
combinatório novo da 35ª (indução sobre o Walk do induce: cada
vértice do caminho é conectado a p, logo pertence ao componente).
Risco: manipular Walk.support no grafo induzido — região nova;
alternativa: provar por indução em Walk com generalização do ponto
inicial. Reconhecimento das APIs Walk.support/mem antes de codar.

## 2. Compatibilidade
  def PolymerCompatible (X Y) : Prop :=
    Disjoint (blockLinkSupport X) (blockLinkSupport Y)
(incompatibilidade = compartilhamento de link; note: X ≠ Y com
suportes disjuntos ⟹ Finsets disjuntos, pois toda plaqueta tem
link próprio no seu suporte).

## 3. A bijeção
Forward: A ↦ componentFamily A (34ª: cobertura, disjunção,
não-vazio; falta auto-conexidade = lema-ponte do §1 + IsPolymer de
cada membro).
Backward: família compatível F ↦ F.biUnion id =: A; provar
componentFamily A = F. Direção delicada: precisa que cada X ∈ F seja
EXATAMENTE um componente de A — usa (i) X conexo dentro de A (X
auto-conexo + X ⊆ A: um Walk em X é Walk em A — monotonia do induce
sobre inclusão de conjuntos; API: SimpleGraph.induceHomOfLE vista no
source (Maps.lean:434) ou mapa de Walk direto); (ii) X maximal: nada
de fora de X em A conecta a X (compatibilidade = links disjuntos ⟹
não-adjacência entre membros distintos de F).
Enunciado-alvo:
  theorem componentFamily_biUnion_eq (F : Finset (Finset _))
    (hpoly : ∀ X ∈ F, IsPolymer X)
    (hcomp : ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → PolymerCompatible X Y) :
    componentFamily (F.biUnion id) = F

## 4. Reindexação do realZ (capstone)
  realZ β χ = Σ_{F ∈ famílias compatíveis} ∏_{X∈F} E₀[blockActivity X]
com "famílias compatíveis" como Finset filtrado do powerset do
powerset — finito, sem tipos novos:
  compatibleFamilies : Finset (Finset (Finset _)) :=
    ((admissiblePlaquettes N).powerset.powerset).filter
      (fun F => (∀ X ∈ F, IsPolymer X) ∧ pairwise compatível)
Rota: Finset.sum_bij (ou sum_nbij') entre powerset e
compatibleFamilies via A ↦ componentFamily A, inversa biUnion —
os dois lemas do §3 são exatamente a boa-definição + injetividade +
sobrejetividade. Pesos batem pela 34ª (∏ sobre componentFamily A).
VERIFICAR no source: Finset.sum_bij / sum_nbij' assinaturas v4.15.

## 5. Custos e separação
- Lema-ponte (caminho fica no componente): MÉDIO (indução em Walk).
- Monotonia de connectedWithin em A ⊆ B: BAIXO (mapa de Walks).
- Maximalidade backward: MÉDIO.
- sum_bij: BAIXO-MÉDIO (burocracia de Finset).
Proposta de corte se inflar: 35ª = IsPolymer + lema-ponte + forward
(componentFamily A é família compatível de polímeros); 36ª = backward
+ bijeção + reindexação. Decisão tua.
- Ainda nível (a). Docstrings: sem Ursell, sem árvores, sem
  convergência, sem log Z, sem uniformidade, sem clustering/gap.

## Perguntas
(i) Aprova IsPolymer como Prop sobre Finset (sem tipo novo)?
(ii) Corte em 35ª/36ª conforme §5, ou tudo numa pedra?
(iii) O lema-ponte via indução em Walk.support: autorizar
     reconhecimento das APIs de Walk antes do parecer final?

Aguardo parecer. — Fable

