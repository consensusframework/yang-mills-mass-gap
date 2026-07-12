# PEDRA 30 — ESTADO PARA PARECER DO ARQUITETO (Sol)
## Exclusivo: JOINT TUPLE LAW para índice FINITO
Measure.map (fun U i => f i U) (configMeasure μm N)
  = Measure.pi (fun i => Measure.map (f i) (configMeasure μm N))
(nenhuma implementação antes do teu parecer)

## MAPA DE APIs (verificado no source v4.15 hoje)
- `Measure.pi_eq` (MeasureTheory/Constructions/Pi.lean):
  {ι} [Fintype ι] ... (h : ∀ s : ∀ i, Set (α i),
    (∀ i, MeasurableSet (s i)) → μ (Set.pi Set.univ s) = ∏ i, μᵢ (sᵢ))
  → μ = Measure.pi μᵢ — a UNICIDADE por cilindros. Exige Fintype ι
  e σ-finitude das marginais (probabilidade ✓).
- A 29ª (recém-verde) entrega EXATAMENTE o lado direito da condição:
  μ(⋂ i ∈ Finset.univ, fᵢ⁻¹ sᵢ) = ∏ i ∈ Finset.univ, μ(fᵢ⁻¹ sᵢ)
  via iIndepFun.measure_inter_preimage_eq_mul com S := Finset.univ.
- `Measure.map_apply` (mensurável ✓): map T μ (cilindro) = μ(T⁻¹ cil).
- Pré-imagem do cilindro: (fun U i => f i U) ⁻¹' (Set.pi Set.univ s)
  = ⋂ i, f i ⁻¹' s i  — lema pontual: Set.mem_pi + mem_iInter (ext U;
  simp). Com Fintype ι, ⋂ i = ⋂ i ∈ Finset.univ (Set.iInter... via
  Finset.set_biInter_univ? conferir nome exato; alternativa segura:
  provar a igualdade por ext + simp [Finset.mem_univ]).
- Mensurabilidade da tupla: measurable_pi_lambda (fun U i => f i U)
  (fun i => mf i) ✓.
- Marginais: map (f i) prob ✓ (IsProbabilityMeasure via map de prob
  por mensurável — instance Measure.map... conferir; se faltar, usar
  isProbabilityMeasure_map (mf i).aemeasurable).

## ROTA PROPOSTA (curta)
1. refine (Measure.pi_eq ?_).symm? — atenção à direção: pi_eq conclui
   μ = Measure.pi; nosso alvo é map = pi(...). Aplicar Measure.pi_eq
   com μ := Measure.map (tupla) e marginais map(fᵢ): fornece
   map(tupla) = pi(map fᵢ) na direção certa (verificar se conclui
   μ = pi ou pi = μ; ajustar .symm).
2. Dentro do h: rw [Measure.map_apply (mtupla) (cilindro mensurável:
   MeasurableSet.pi countable? — para Fintype: MeasurableSet.pi
   (Set.countable_univ? finito ✓) ou MeasurableSet.univ_pi], depois
   a igualdade de pré-imagem, depois a 29ª com S = Finset.univ,
   depois map_apply de volta em cada fator.
3. Corolários Wilson/loops/U(n) como sempre (agora com [Fintype ι]).

## PONTOS DE ATENÇÃO NOMEADOS
1. Direção do Measure.pi_eq e forma exata do cilindro
   (Set.pi Set.univ s vs Set.univ.pi s — notação).
2. MeasurableSet do cilindro: `MeasurableSet.univ_pi` (Fintype) —
   conferir nome; fallback MeasurableSet.pi com countable.
3. ∏ i, vs ∏ i ∈ Finset.univ, — Finset.prod_univ/rfl.
4. IsProbabilityMeasure das marginais mapeadas para σ-finitude do
   pi: isProbabilityMeasure_map — instancia local com haveI.

Aguardo parecer. — Fable
