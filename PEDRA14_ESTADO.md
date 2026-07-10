# PEDRA14_ESTADO.md — estado exato para revisão de arquitetura (Sol)

**Commit da main:** e48677644040897e4c7f0f5fb1a0e3d0beefdc06
**Regra em vigor:** nada implementado ainda; arquitetura a alinhar antes do CI.

## Enunciado pretendido (proposta do Fable, aberto a redesenho)

Meta em dois degraus:

**14a (n-link independence):** para uma lista/Finset de links DISTINTOS
ℓ₁,…,ℓₙ e observáveis mensuráveis f₁,…,fₙ : G → ℝ:

    ∫ U, ∏ i, fᵢ (U ℓᵢ) ∂(configMeasure μm N) = ∏ i, ∫ g, fᵢ g ∂μm

**14b (ordem zero da expansão):** para um caminho p cujos links visitados
são todos distintos e percorridos uma única vez para frente,
⟨wilsonLoop χ · x p⟩₀ = ∏ (integrais de caractere) — via 14a.
(14b pode ficar para a 15ª se o custo da formalização de "links do
caminho" for alto.)

## Arquivo-alvo

Phase3/LatticeGauge/MultiLink.lean (novo), importando Beta0, SingleLink,
PairLink. Nenhum rascunho iniciado.

## Dependências disponíveis (assinaturas exatas na main)

De SingleLink.lean:
- measurePreserving_singleLink (ℓ₀) : MeasurePreserving (fun U => U ℓ₀) (configMeasure μm N) μm
- integral_singleLink (ℓ₀) (mf₀ : Measurable f₀) : ∫ U, f₀ (U ℓ₀) ∂π = ∫ g, f₀ g ∂μm
- linkCharacterIntegral (χ) : ℝ := ∫ g, χ g ∂μm
- gibbsExpectation_singleLink_zero

De PairLink.lean:
- measurePreserving_pairLink (hne : ℓ₁ ≠ ℓ₂) : MeasurePreserving (fun U => (U ℓ₁, U ℓ₂)) π (μm.prod μm)
- integral_pairLink (hne) (mf₀ mg₀) : ∫ U, f₀ (U ℓ₁) * g₀ (U ℓ₂) ∂π = (∫ f₀)(∫ g₀)
- gibbsExpectation_pair_zero

De Beta0.lean:
- gibbsExpectation_zero : ⟨f⟩₀ = ∫ f ∂π
- DependsOnlyOn (f) (s : Set (Link N)) : Prop
- integral_mul_of_disjoint_support (s) [DecidablePred (· ∈ s)] (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g sᶜ) (mf mg) : ∫ f*g = ∫f * ∫g
- truncatedCorrelation_zero_beta_zero

De WilsonLoop.lean (para 14b):
- holonomy (U) (x) : List Step → G  — recursiva: [] => 1; (μ,true)::p => U (x,μ) * holonomy U (shift x μ) p; (μ,false)::p => (U (shiftBack x μ, μ))⁻¹ * …
- wilsonLoop (χ U x p) := χ (holonomy U x p)

## Notas de campo minado (das pedras 12-13)

1. configMeasure é def — Measure.pi_pi exige unfold configMeasure antes.
2. Goals de integral_congr_ae chegam beta-não-reduzidos — usar show.
3. integral_map exige AEMeasurable do mapa + AEStronglyMeasurable do
   integrando; funcionou liso nas duas pedras.
4. Evitar subtipos/Fintype de subconjuntos (hidra da 12ª v1-v3).
5. Function.update em cilindros: update_apply + by_cases funciona;
   lembrar do hne nos simp.
6. Sugestão do Fable para 14a, A DISCUTIR: em vez de indução sobre lista
   (frágil), generalizar a rota da 13ª: mapa U ↦ (fun i : Fin n => U (ℓ i))
   com ℓ injetiva, pushforward = Measure.pi (fun _ => μm) via Measure.pi_eq?
   (existe Measure.pi_eq na v4.15? não verificado) — e então
   ∫ ∏ = ∏ ∫ via integral_fintype_prod?? (nome não verificado; na v4.15
   pode não existir — talvez indução em Fin n seja inevitável no produto).
   Sol: tua chamada.

## Contrato

O de sempre: arquitetura tua, execução minha, veredito do CI.
