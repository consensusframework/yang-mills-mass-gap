# AXIOM_AUDIT.md — Auditoria Completa de Axiomas

**Gerado por análise estática de todos os arquivos .lean do repositório (equivalente a `#print axioms` agregado, pois todos os axiomas são declarações explícitas `axiom`).**

Data: 2026-06-12 | Auditoria: Claude (Anthropic)

---

## Sumário Executivo

- **Declarações `axiom`:** 404 (329 nomes únicos) em 87 arquivos
- **Axiomas `gemini_*` (asserções numéricas de LLM, sem prova nem simulação verificável):** ~110
- **Arquivos com `sorry` em código (não comentário):** 21 — a alegação "zero sorry" do README anterior é **INCORRETA**
- **Teoremas/lemas declarados:** ~442. Razão axioma:teorema ≈ 1:1 — em média, cada teorema "provado" consome um axioma não demonstrado.

### Arquivos com `sorry` real

- `Phase1/AXIOM3_Compose.lean` (3 ocorrências)
- `Phase1/Axiom8Prime.lean` (1 ocorrência)
- `Phase1/B1_BFSConvergence.lean` (1 ocorrência)
- `Phase1/B3_MassGapStrongCoupling.lean` (2 ocorrências)
- `Phase1/B4_ContinuumLimitStability.lean` (2 ocorrências)
- `Phase1/Correspondence.lean` (1 ocorrência)
- `Phase1/FieldEquations.lean` (3 ocorrências)
- `Phase1/L3_TopologicalPairing.lean` (1 ocorrência)
- `Phase1/LowerBound.lean` (1 ocorrência)
- `Phase1/Positivity.lean` (1 ocorrência)
- `Phase1/Prelude(1).lean` (1 ocorrência)
- `Phase2/RGFlow_Work/Theorem10_ContinuumLimitExistence.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem2_Monotonicity.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem3_BoundPreservation.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem4_MassGapPersistence.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem6_LipschitzContinuityInA.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem7_QuantitativeMonotonicity.lean` (2 ocorrências)
- `Phase2/RGFlow_Work/Theorem8_JointLipschitz.lean` (1 ocorrência)
- `Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean` (2 ocorrências)

---

## Classificação dos Axiomas

Legenda:
- ✅ **Grupo A** — disponível no Mathlib4 (substituível por import; ~15 axiomas)
- 🔬 **Grupo B** — resultado conhecido na literatura (formalizável com trabalho; ~40 axiomas)
- 🔴 **Grupo C** — aberto/não demonstrado / equivale ao próprio problema (~60 axiomas)
- ⚠️ **Grupo D** — asserção de LLM (não é matemática — deve ser removida; ~110 axiomas)

---

## ✅ Grupo A — Já existe no Mathlib4 (substituir por import; ~15 axiomas)

| Axioma | Substituto Mathlib |
|---|---|
| `ge_trans`, `lt_implies_ne`, `le_refl_float`, `ne_of_gt_float` | `le_trans`, `ne_of_gt`, `le_refl` (já existem; axiomatizá-los é grave) |
| `pi`, `add`, `mul`, `sub`, `pow`, `conj`, `ℝ` | tipos/operações básicas do Mathlib — NUNCA deveriam ser axiomas |
| `prokhorov_theorem` | `MeasureTheory.isCompact_closure_iff_tight` (Prokhorov está no Mathlib) |
| `rellich_kondrachov_compact` | parcial no Mathlib (espaços de Sobolev em desenvolvimento) |
| `continuity_from_lipschitz` | `LipschitzWith.continuous` |

---

## 🔬 Grupo B — Conhecido na literatura, NÃO formalizado em Lean (~40 axiomas)

| Axioma | Referência | Esforço estimado |
|---|---|---|
| `uhlenbeck_compactness_theorem` | Uhlenbeck 1982 | Muito alto (geometria de gauge inexistente no Mathlib) |
| `atiyahSingerIndex`, `dirac_index`, `index_theorem_implies_pairing` | Atiyah–Singer | Projeto de formalização em andamento na comunidade, não concluído |
| `bishop_gromov_volume_comparison`, `gromov_hausdorff_precompactness` | Geometria riemanniana clássica | Alto |
| `bochner_identity`, `bourguignon_lawson_simons_formula`, `oneill_formula` | Literatura padrão | Alto |
| `sobolev_embedding`, `spectral_theorem_elliptic` | Clássicos de EDP | Alto; parcial no Mathlib |
| `cluster_decay`, `polymer_activity_bound`, `symanzik_mass_gap_expansion` | Expansão de acoplamento forte (Osterwalder–Seiler 1978) | **Alto, mas é o caminho mais promissor** — gap em lattice com g grande é teorema conhecido |

---

## 🔴 Grupo C — ABERTO: equivale ao próprio problema ou a partes não resolvidas (~60 axiomas)

Estes axiomas **assumem o que o projeto alega provar**. Enquanto existirem, o resultado é circular.

| Axioma | O que assume |
|---|---|
| `Delta0` + `continuum_mass_gap_lower_bound`, `continuum_monotonic_in_g`, `continuum_lipschitz_in_g`, `Delta0_at_gmin/gmax` | Existência e propriedades do gap no contínuo — **é o enunciado do problema de Clay** |
| `axiom1_brst_measure`, `mu_BRST_*`, `normalizedBRSTMeasure` | Existência da medida de Yang-Mills em 4D — problema aberto central (QFT construtiva) |
| `mass_gap`, `mass_gap_*`, `phase1_gap_exists`, `mass_gap_tendsto_continuum` | Existência/persistência do gap |
| `axiom2_gribov_cancellation`, `gribov_*`, `kugo_ojima_criterion` | Conjecturas físicas não demonstradas matematicamente |
| `axiom_entropic_mass_gap_principle`, `axiom_holographic_consistency`, `axiom_ryu_takayanagi_formula`, `holographic_scaling` | Princípios heurísticos de física (holografia) sem estatuto de teorema; RT vale em AdS/CFT, não em YM puro |

---

## ⚠️ Grupo D — Asserções de LLM axiomatizadas (~110 axiomas `gemini_*`)

Todos os `gemini_*` (ex.: `gemini_validation_15_success_rate`, `gemini_Delta0_at_gmin`, `gemini_analytic_validation`...) registram como axioma matemático a afirmação de um modelo de linguagem. Isso **não tem valor probatório** — um LLM dizer "8/8, confiança 1000%" não é simulação de lattice nem prova.

**Recomendação: deletar todos do código formal.** Se houver dados numéricos reais (de simulação executada de verdade, com código e seeds), publicá-los como dados, não como axiomas.

---

## Conclusão da classificação

| Grupo | Quantidade | Ação | Prazo |
|---|---|---|---|
| ✅ A — Substituíveis hoje | ~15 | Substituir por imports Mathlib | Dias |
| 🔬 B — Formalizáveis com esforço | ~40 | Priorizar Osterwalder–Seiler | Anos |
| 🔴 C — Abertos (incluem o problema) | ~60 | Documentar honestamente como hipóteses | — |
| ⚠️ D — Sem valor probatório | ~110 | **Remover** | Dias |
| Estruturais | restante | Converter de `axiom` para `def`/`structure` | Semanas |

**Critério de sucesso da nova Fase 3:** cada teorema principal passa `#print axioms` mostrando apenas `propext`, `Classical.choice`, `Quot.sound` — nada mais.
