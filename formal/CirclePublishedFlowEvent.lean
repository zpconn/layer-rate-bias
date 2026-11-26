module

public import CircleWidthPublished
import all CircleWidthInitTail
import all CircleInitializationConcentration
import all CircleActualTracking
import all CircleFlowPath
import all CircleTangentDrift
import all CircleGaussianBernstein
import all CircleEscapeBridge
import Mathlib.Tactic

/-! The shared Gaussian initialization event with the single-error tolerance
for both the tangent matrix and the integrated population row. -/
@[expose] public section
noncomputable section
namespace CirclePublishedFlowEvent
open Real MeasureTheory ProbabilityTheory Set CircleTangentDrift CircleEscapeBridge
  CircleInitializationConcentration CircleGaussianBernstein CircleGridSpectrum
  CircleActualTracking CircleFlowPath CircleGaussianTracking

structure StrongInit (N m : ℕ) [NeZero N] (ρ u : ℝ) (z : Seed m) : Prop where
  good : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) z
  gram : ∀ i j : Fin N, |gridGram 1 z (startGates z) i j - sampledMatrix 1 i j|≤u
  row : ∀ j : Fin N, |populationRow 1 z (startGates z) j - CircleSpectrum.k0 1|≤u

private theorem of_tests {N m : ℕ} [NeZero N] (hm : 0<m) {ρ u : ℝ}
    (r0 : 0≤ρ) (r1 : ρ≤1) (u0 : 0≤u) (u1 : u≤1) (ω : Seed m)
    (h : ∀ q : InitIndex N, |sampleAverage (initTest N 1 ρ q) ω - ∫ z, initTest N 1 ρ q z ∂atomLaw|≤u) :
    StrongInit N m ρ u ω := by
  constructor
  · simpa only [populationGram_sampled,funext (populationMeanRow_constant (N:=N) 1)] using
      goodInit_of_tests hm r0 r1 u0 u1 ω h
  · intro i j
    have ht := h (.inr (.inr (j,some i)))
    change |sampleAverage (weightedAtom 1 (circleInput N i) (circleInput N j)) ω-populationGram N 1 i j|≤u at ht
    rw [← weightedAtom_initial hm,populationGram_sampled] at ht
    exact ht
  · intro j
    have ht := h (.inr (.inr (j,none)))
    change |sampleAverage (fun z => ∫ t, weightedAtom 1 (phase t) (circleInput N j) z ∂angularLaw) ω-populationMeanRow N 1 j|≤u at ht
    rw [← angular_entry_initial hm,populationMeanRow_constant] at ht
    exact ht

private theorem strong_tail {N m : ℕ} [NeZero N] (hm : 0<m) {ρ u : ℝ}
    (r0 : 0≤ρ) (r1 : ρ≤1) (u0 : 0≤u) (u1 : u≤1) :
    (seedLaw m).real {ω | ¬StrongInit N m ρ u ω} ≤
      ((N+1:ℝ)^2+1)*(2*exp (-(m:ℝ)*u^2/4096)) := by
  let bad (q : InitIndex N) := {ω : Seed m | u ≤ |sampleAverage (initTest N 1 ρ q) ω -
    ∫ z, initTest N 1 ρ q z ∂atomLaw|}
  have tail (q : InitIndex N) : (seedLaw m).real (bad q) ≤ 2*exp (-(m:ℝ)*u^2/4096) :=
    two_sided hm _ (initTest_meas N 1 ρ q) (fun z => (CircleWidthInitTail.init_marks N ρ q z).trans_eq (by
      simp [CircleGaussianBernstein.energy,atomEnergy,Fin.sum_univ_three,add_assoc])) u0 (by linarith)
  have sub : {ω : Seed m | ¬StrongInit N m ρ u ω} ⊆ ⋃ q, bad q := by
    intro ω fail
    by_contra out
    exact fail (of_tests hm r0 r1 u0 u1 ω fun q =>
      (lt_of_not_ge (fun hq => out (Set.mem_iUnion_of_mem q hq))).le)
  apply (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun q _ => tail q)).trans_eq ?_))
  simp only [Finset.sum_const,Finset.card_univ,InitIndex,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_option,Fintype.card_unit,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
  ring

/-- All initial quantities for the printed finite flow certificate hold on
one measurable set independent of the selection and of the stopping time. -/
theorem event {N m : ℕ} [NeZero N] (hm : 0<m) {d ρ : ℝ}
    (hd : 0≤d) (dm : d≤m) (r0 : 0≤ρ) (r1 : ρ≤1) (u1 : 64*sqrt (d/m)≤1) :
    ∃ G : Set (Seed m), MeasurableSet G ∧
      (∀ ω∈G, StrongInit N m ρ (64*sqrt (d/m)) ω ∧
        ‖gridR N ω‖≤2+sqrt (8*d) ∧ ∀ j, 0<length ω j) ∧
      (seedLaw m).real Gᶜ≤min 1 (8*((N:ℝ)+1)^2*exp (-d)) := by
  let μ := seedLaw m
  let I := {ω : Seed m | ¬StrongInit N m ρ (64*sqrt (d/m)) ω} ∪
    {ω | 2+sqrt (8*d) < initialRms N m ω}
  let Z := {ω : Seed m | ¬∀ j, 0<length ω j}
  let G := (toMeasurable μ (I∪Z))ᶜ
  refine ⟨G,(measurableSet_toMeasurable μ _).compl,?_,?_⟩
  · intro ω good
    have out : ω∉I∪Z := fun hh => good (subset_toMeasurable μ (I∪Z) hh)
    exact ⟨not_not.mp (fun bad => out (Or.inl (Or.inl bad))),
      le_of_not_gt (fun bad => out (Or.inl (Or.inr bad))),
      not_not.mp (fun bad => out (Or.inr bad))⟩
  · apply le_min measureReal_le_one
    change μ.real ((toMeasurable μ (I∪Z))ᶜ)ᶜ≤_
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    have hz : μ Z=0 := ae_iff.mp (length_pos_ae m)
    have un := measureReal_union_le (μ:=μ) I Z
    rw [measureReal_def μ Z,hz,ENNReal.toReal_zero,add_zero] at un
    have a := strong_tail (N:=N) hm r0 r1 (by positivity) u1
    have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
    have eq : -(m:ℝ)*(64*sqrt (d/m))^2/4096= -d := by
      rw [mul_pow,sq_sqrt (by positivity)];field_simp;ring
    rw [eq] at a
    have b := CircleWidthResidualTail.initial_residual (N:=N) (Nat.pos_of_ne_zero (NeZero.ne N)) hm hd dm
    apply un.trans ((measureReal_union_le (μ:=μ) _ _).trans ((add_le_add a b).trans ?_))
    nlinarith only [mul_nonneg (exp_nonneg (-d)) (sq_nonneg (N:ℝ)),
      mul_nonneg (exp_nonneg (-d)) (Nat.cast_nonneg (α:=ℝ) N),exp_nonneg (-d)]

end CirclePublishedFlowEvent
