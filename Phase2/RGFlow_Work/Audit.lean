/- Audit.lean — kernel dependency X-ray. Instrumentação de auditoria:
   imprime no log do CI os axiomas reais de cada teorema da Fase 2. -/
import RGFlow_Work.Basic
import RGFlow_Work.GeminiValidation2
import RGFlow_Work.GeminiValidation3
import RGFlow_Work.GeminiValidation4
import RGFlow_Work.GeminiValidation5
import RGFlow_Work.GeminiValidation6
import RGFlow_Work.GeminiValidation7
import RGFlow_Work.GeminiValidation8
import RGFlow_Work.GeminiValidation12
import RGFlow_Work.GeminiValidation13
import RGFlow_Work.GeminiValidation15
import RGFlow_Work.GeminiValidation9
import RGFlow_Work.GeminiValidation10
import RGFlow_Work.GeminiValidation11
import RGFlow_Work.GeminiValidation14
import RGFlow_Work.Theorem9_AsymptoticExpansion
import RGFlow_Work.Theorem10_ContinuumLimitExistence
import RGFlow_Work.Theorem1_BetaNegativity
import RGFlow_Work.Theorem2_Monotonicity
import RGFlow_Work.Theorem2_RunningCouplingMonotonicity
import RGFlow_Work.Theorem3_BoundPreservation
import RGFlow_Work.Theorem4_MassGapPersistence
import RGFlow_Work.Theorem5_LipschitzContinuity
import RGFlow_Work.Theorem6_LipschitzContinuityInA
import RGFlow_Work.Theorem7_QuantitativeMonotonicity
import RGFlow_Work.Theorem8_JointLipschitz
import RGFlow_Work.Theorem11_ContinuumMassGapLowerBound
import RGFlow_Work.Theorem12_ContinuumLipschitzInG
import RGFlow_Work.Theorem13_ContinuumMonotonicityInG
import RGFlow_Work.Theorem14_RGInvariance
import RGFlow_Work.Theorem15_UniversalPhysicalBound

open RGFlow

#print axioms C_mono_pos
#print axioms Ioc_mem_nhdsWithin_Ioi_zero
#print axioms asymptotic_consistent_with_lipschitz
#print axioms beta_negativity
#print axioms bound_from_monotonicity_concept
#print axioms bound_preservation
#print axioms c2_is_negative
#print axioms complete_characterization
#print axioms continuum_complete_picture
#print axioms continuum_diff_eq_zero
#print axioms continuum_gap_diff_nonneg
#print axioms continuum_gap_injective
#print axioms continuum_gap_positive
#print axioms continuum_gap_positive_and_lipschitz
#print axioms continuum_gap_quantitative_bound
#print axioms continuum_gap_strictly_decreasing
#print axioms continuum_gap_well_defined
#print axioms continuum_limit_exists
#print axioms continuum_limit_exists_thm10
#print axioms continuum_limit_from_expansion
#print axioms continuum_limit_is_Delta0
#print axioms continuum_limit_unique
#print axioms continuum_limit_well_defined
#print axioms continuum_lipschitz_in_g
#print axioms continuum_mass_gap_continuous_in_g
#print axioms continuum_mass_gap_lower_bound
#print axioms continuum_mass_gap_ne_zero
#print axioms continuum_mass_gap_positive
#print axioms continuum_monotonic_in_g
#print axioms continuum_smoother_than_lattice
#print axioms coupling_bounded_above
#print axioms coupling_decreases
#print axioms coupling_decreases_from_reference
#print axioms coupling_stays_bounded
#print axioms extremes_at_endpoints
#print axioms g0_positive
#print axioms gap_bounded_across_region
#print axioms gap_change_full_range
#print axioms gap_diff_tendsto
#print axioms gap_lower_bound_positive
#print axioms gap_never_vanishes
#print axioms gap_stable_under_refinement
#print axioms gemini_all_positive
#print axioms gemini_amplitude_positive
#print axioms gemini_continuum_smoother_than_lattice
#print axioms gemini_diff_well_below_target
#print axioms gemini_min_gap_positive
#print axioms gemini_scheme_agreement_trivial
#print axioms gemini_total_gap_positive
#print axioms lattice_gap_diff_eventually_pos
#print axioms lipschitz_L_a_pos
#print axioms lipschitz_L_pos
#print axioms lipschitz_bound_eventually
#print axioms lower_bound_from_monotonicity
#print axioms mass_gap_abs_diff_tendsto
#print axioms mass_gap_amplitude
#print axioms mass_gap_asymptotic_in_a
#print axioms mass_gap_continuous
#print axioms mass_gap_diff_tendsto
#print axioms mass_gap_domesticated
#print axioms mass_gap_eventually_ge_bound
#print axioms mass_gap_is_physical_observable
#print axioms mass_gap_joint_lipschitz_L1
#print axioms mass_gap_jointly_lipschitz
#print axioms mass_gap_lipschitz_continuous
#print axioms mass_gap_lipschitz_in_a
#print axioms mass_gap_monotone_in_g
#print axioms mass_gap_never_vanishes
#print axioms mass_gap_persistence
#print axioms mass_gap_quantitative_monotonicity
#print axioms mass_gap_strictly_positive
#print axioms mass_gap_strictly_positive_strong
#print axioms mass_gap_two_sided_bound
#print axioms mass_gap_uniform_bound_at_g0
#print axioms monotonicity_from_beta_negativity_concept
#print axioms no_constant_regions
#print axioms no_landau_pole
#print axioms no_plateaus
#print axioms phase3_foundation
#print axioms rg_invariance
#print axioms rg_invariance_strong
#print axioms running_coupling_monotonicity
#print axioms scheme_diff_tendsto_zero
#print axioms scheme_diff_within_tolerance
#print axioms theorem10_perfect
#print axioms theorem10_positive
#print axioms theorem2_extensive_tests
#print axioms theorem2_validated
#print axioms theorem3_fast
#print axioms theorem4_has_margin
#print axioms theorem4_validated
#print axioms theorem5_smooth
#print axioms theorem5_tight
#print axioms theorem5_validated
#print axioms theorem6_12x_margin
#print axioms theorem6_bunker_nuclear
#print axioms theorem6_validated
#print axioms theorem7_safe
#print axioms theorem7_validated
#print axioms theorem9_c2_negative
#print axioms theorem9_good_fit
#print axioms universal_physical_bound
#print axioms upper_bound_from_monotonicity
#print axioms validation10_perfect_fit
#print axioms validation10_positive
#print axioms validation2_complete
#print axioms validation2_extensive
#print axioms validation2_high_confidence
#print axioms validation4_complete
#print axioms validation4_extensive
#print axioms validation4_margin_positive
#print axioms validation5_complete
#print axioms validation5_extensive
#print axioms validation5_smooth_avg
#print axioms validation5_tight
#print axioms validation6_absurd_margin
#print axioms validation6_complete
#print axioms validation6_extensive
#print axioms validation6_massive_margin
#print axioms validation7_complete
#print axioms validation7_extensive
#print axioms validation7_safe
#print axioms validation9_c2_negative
#print axioms validation9_consistent_thm6
#print axioms validation9_good_fit
#print axioms validation9_small_jump