# PEDRA 47c-B — ESTADO (para parecer do 47c-C)

**Para:** Sol — via Ju. **De:** Fable. **Data:** 2026-08-14.
**47c-A COMPLETO e 47c-B COMPLETO E VERDE** (branch `pedra47c-sol`, A1+A2+A3+B todos verdes; B na 1ª rodada). C **não iniciado**.

## 1. Assinaturas exatas (KPInduction.lean)

```lean
def AbstractKPHypothesis (ρ : Polymer N → ℝ) (a : Polymer N → ℝ) : Prop :=
  ∀ γ₀ : Polymer N,
    (∑ η : Polymer N, (incompatibilityIndicator γ₀ η : ℝ) * ρ η * Real.exp (a η)) ≤ a γ₀

theorem kpX_le_a {ρ a} (hρ : ∀ η, 0 ≤ ρ η) (hKP : AbstractKPHypothesis ρ a)
    (M : ℕ) (γ₀) (IH : ∀ η, kpPartialSum M ρ η ≤ Real.exp (a η)) :
    kpX M ρ γ₀ ≤ a γ₀

theorem kpPartialSum_le_exp {ρ a} (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) :
    ∀ (M : ℕ) (γ : Polymer N), kpPartialSum M ρ γ ≤ Real.exp (a γ)   -- CAPSTONE
```

## 2. Auditoria exigida

- **API de monotonicidade**: `Real.exp_le_exp : exp x ≤ exp y ↔ x ≤ y` (pin: Data/Complex/Exponential.lean:1031). Usada 2× no B2 (base `1 = exp 0 ≤ exp(a γ)` via `ha` — sem API especial de `1 ≤ exp`, como sugerido; passo). `Real.exp_zero` na base.
- **hKP aparece EXATAMENTE 1 vez** em toda a prova: dentro de `kpX_le_a`, como `(hKP γ₀)` no `le_trans`. O capstone só o repassa.
- **KPInduction.lean NÃO importa KPSmallness.lean** ✓ (imports: Basic, Ursell*, PolymerTreeBound, KPCoefficients, RootDecomposition, KPEnumerations, KPOrderedDecomposition, KPWeightFactorization, KPRootedTransport, KPBlockSum, KPMarkedBlock, KPPartitionCount, KPStratification). O B não sabe que β, χ, μm, incompatiblePolymers ou 1/40000 existem.

## 3. Reconhecimento da cola do C (sem implementação)

```lean
-- KPWeightFactorization.lean:239
noncomputable def incompatibilityIndicator (γ₀ η : Polymer N) : ℕ :=
  if PlaquetteCompatible γ₀.val η.val then 0 else 1
-- LinkCovering.lean:76
noncomputable def incompatiblePolymers (C : Finset (Site N × Dir × Dir)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (allPlaquettePolymers N).filter (fun D => ¬ PlaquetteCompatible C D)
-- + mem_incompatiblePolymers : D ∈ … ↔ D ∈ allPlaquettePolymers N ∧ ¬ PlaquetteCompatible C D
```

**Tipos dos dois lados**: o B soma sobre `η : Polymer N` (subtipo Fintype; `Polymer N = {D // IsPlaquettePolymer D}` presumivelmente — univ do subtipo); a 46 soma sobre `D ∈ incompatiblePolymers C : Finset (Finset (Site N × Dir × Dir))` (nível raw). A cola precisará de: (i) indicador→filter no subtipo: `Σ_η ite(compat)·f = Σ_{η ∈ univ.filter (¬compat)} f` (via `Finset.sum_ite_eq`-família ou `sum_filter`: `Σ_{x ∈ s} (if p x then f x else 0) = Σ_{x ∈ s.filter p} f x` — censar `Finset.sum_filter` no pin, direção reversa; nosso indicador é 0-se-compat, então o somando é `ite p 0 (f)` — conversão por `sum_ite` ou reescrever o indicador como `ite (¬compat) 1 0`); (ii) subtipo↔Finset raw: `Finset.sum_subtype` (univ do subtipo ↔ allPlaquettePolymers, se `allPlaquettePolymers = filter IsPlaquettePolymer univ` — censar a def real) — a composição dá exatamente `Σ_η 1[η≁γ₀]·f(η.val) = Σ_{D ∈ incompatiblePolymers γ₀.val} f D`. (iii) Instanciação: `ρ η := |polymerWeight μm β χ η.val|`, `a η := (η.val.card : ℝ)`; `ha` ✓ cast_nonneg; `hρ` ✓ abs_nonneg; `AbstractKP` segue de `kp_hypothesis_beta_le_one_div_40000` com `C := γ₀.val` (α = 1: `exp(1·card) = exp(card)` ✓ grafias iguais) — o threshold NÃO se reprova.

Aguardo o parecer do C. — Fable
