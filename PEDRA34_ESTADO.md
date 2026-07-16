# PEDRA 34 — MAPA DE ARQUITETURA (sequência que encomendaste no
# parecer da 33ª; NENHUMA implementação até parecer)

## Alvo
family of distinct components → cobertura e disjunção → decomposição
do produto de atividades → suportes disjuntos → FATORIZAÇÃO DA
EXPECTATIVA EM β=0 PELA 26ª:
  E₀[∏_{p∈A} m_p] = ∏_{C ∈ componentes(A)} E₀[∏_{p∈C} m_p].
Sem estimativa de convergência.

## Peças (todas verdes)
- 33ª: componentes, disjunção par a par, suportes de links disjuntos.
- 32ª: m_p, mensurabilidade, |m_p| ≤ 2β.
- 26ª: integral_finsetProd_of_pairwise_disjoint_support (a fatorização
  genérica por suportes) + dependsOnlyOn_finsetProd + measurable_finsetProd.
- Falta UM elo local: "m_p DependsOnlyOn ↑(plaqLinkSet p)" — espelho
  do wilsonPath_dependsOnlyOn (congr nos 4 fatores da plaquette;
  barato, deliberadamente deixado fora da 33ª).

## Estrutura proposta
1. componentFamily A : Finset (Finset _) := A.image (plaquetteComponent A)
   — a deduplicação via image que a 33ª adiou. Lemas: (i) membros
   não-vazios; (ii) pairwise disjoint (da 33ª-F + injetividade em
   representantes NO measure zero... cuidado: image identifica
   componentes iguais ✓ é exatamente o que queremos); (iii) cobertura:
   A = componentFamily.sup id / biUnion. Candidatos Mathlib:
   Finset.sup / Finset.biUnion / Finset.disjiUnion — VERIFICAR
   assinaturas v4.15 antes (Finset.biUnion pede DecidableEq ✓ temos).
2. Decomposição do produto:
   ∏_{p∈A} m_p U = ∏_{C ∈ componentFamily A} ∏_{p∈C} m_p U
   — Finset.prod_biUnion (exige pairwise disjoint ✓ da 33ª).
   VERIFICAR: Finset.prod_biUnion (h : pairwise Disjoint) na v4.15.
3. dependsOnlyOn_plaquetteActivity : DependsOnlyOn (fun U => m_p U)
   ↑(plaqLinkSet p) — o elo local (§Peças).
4. DependsOnlyOn do produto por componente sobre blockLinkSupport C
   (dependsOnlyOn_finsetProd da 26ª, textual).
5. Capstone: fatorização de E₀ sobre componentes — a 26ª aplicada com
   ι := Finset (índices) — ATENÇÃO: a 26ª fatoriza famílias indexadas
   (i : ι) com suportes pairwise disjoint; aqui os "índices" são os
   PRÓPRIOS componentes C ∈ componentFamily A (ι := Finset (Site×Dir×Dir)
   com DecidableEq ✓); f C U := ∏_{p∈C} m_p U; supp C := blockLinkSupport C;
   disjunção da 33ª. Encaixe direto, sem tipo dependente.
6. Wrapper físico em U(n) opcional (a 32ª não fez versões U(n); manter
   consistência: provavelmente NÃO precisa — decidir no parecer).

## Riscos nomeados
1. Finset.prod_biUnion: forma exata da hipótese de disjunção
   (Set.PairwiseDisjoint vs ∀-forma) — pode exigir tradução da 33ª-F;
   se a API pedir Set.Pairwise em ↑(componentFamily A), provar o
   pairwise por elementos (barato mas chato).
2. Cobertura A = biUnion: precisa 33ª-G (todo p em algum componente)
   + F (disjunção) — indução não; ext + constructor.
3. O passo 5 usa a 26ª com hf/mf sobre TODOS i : ι? Não — a 26ª pede
   hipóteses só ∀ i ∈ s ✓ conferido na assinatura (s := componentFamily A).

## Nível
(a) ainda: identidades exatas em volume finito. Docstrings: não é
polymer expansion completa; sem pesos conectados; sem convergência;
sem uniformidade; sem clustering; sem mass gap. "Polímero" continua
não-objeto até o teu batismo.

Aguardo parecer. — Fable
