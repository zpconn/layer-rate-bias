module

public import CircleSignedRow
public import CircleInitializationConcentration
import all CircleDiscreteTracking
import all CircleSignedRow
import all CircleInitializationConcentration
import all CircleGaussianMargin
import all CircleKernelIdentification
import all CircleEscapeBridge
import all CircleTangentDrift
import all CircleFlowPath
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Readout-weighted angular margins for independent three-coordinate Gaussian neurons. -/
@[expose] public section
noncomputable section
namespace CircleReadoutMargin
open Real MeasureTheory ProbabilityTheory Set CircleInitializationConcentration
  CircleKernelIdentification CircleEscapeBridge CircleTangentDrift CircleSignedRow
open scoped InnerProductSpace

/-- Gaussian rotation of the hidden plane, retaining the actual readout coordinate. -/
private theorem rotate (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) (Φ : ℝ → ℝ → ℝ → ℝ) :
    ∫ z, Φ (atomEnergy z) (x.1*z 1+x.2*z 2) (z 0) ∂atomLaw =
    ∫ z, Φ (atomEnergy z) (z 1) (z 0) ∂atomLaw := by
  let E := EuclideanSpace ℝ (Fin 3)
  let e : E := WithLp.toLp 2 ![0,1,0]
  let v : E := WithLp.toLp 2 ![0,x.1,x.2]
  let a : E := WithLp.toLp 2 ![1,0,0]
  have hn : ‖e‖ = ‖v‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simpa [e,v,Fin.sum_univ_three] using hx.symm
  let R := (ℝ ∙ (e-v))ᗮ.reflection
  have hR : R e = v := Submodule.reflection_sub hn
  have hA : R a = a := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,inner_sub_left]
    change a ⬝ᵥ star (![0,1,0] : Fin 3 → ℝ) - a ⬝ᵥ star (![0,x.1,x.2] : Fin 3 → ℝ) = 0
    simp [a,dotProduct,Fin.sum_univ_three]
  let toE := MeasurableEquiv.toLp 2 Atom
  have ht : MeasurePreserving toE atomLaw (stdGaussian E) :=
    ⟨toE.measurable, map_pi_eq_stdGaussian⟩
  let r := R.symm.toHomeomorph.toMeasurableEquiv
  have hr : MeasurePreserving r (stdGaussian E) (stdGaussian E) :=
    ⟨r.measurable, stdGaussian_map R.symm⟩
  have en (z : Atom) : ‖toE z‖^2 = atomEnergy z := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, toE, atomEnergy]
  have ca (z : Atom) : inner ℝ a (toE z) = z 0 := by
    change z ⬝ᵥ (star (![1,0,0] : Fin 3 → ℝ)) = _
    simp [dotProduct,Fin.sum_univ_three]
  have ce (z : Atom) : inner ℝ e (toE z) = z 1 := by
    change z ⬝ᵥ (star (![0,1,0] : Fin 3 → ℝ)) = _
    simp [dotProduct,Fin.sum_univ_three]
  have cv (z : Atom) : inner ℝ v (toE z) = x.1*z 1+x.2*z 2 := by
    change z ⬝ᵥ (star (![0,x.1,x.2] : Fin 3 → ℝ)) = _
    simp [dotProduct,Fin.sum_univ_three,mul_comm]
  have iso (b u : E) : inner ℝ b (r u) = inner ℝ (R b) u := by
    change inner ℝ b (R.symm u) = _
    rw [← R.inner_map_map b (R.symm u), R.apply_symm_apply]
  let test : E → ℝ := fun u => Φ (‖u‖^2) (inner ℝ e u) (inner ℝ a u)
  have rot (z : Atom) : test (r (toE z)) = Φ (atomEnergy z) (x.1*z 1+x.2*z 2) (z 0) := by
    change Φ (‖R.symm (toE z)‖^2) (inner ℝ e (r (toE z))) (inner ℝ a (r (toE z))) = _
    rw [R.symm.norm_map,en,iso,iso,hR,hA,cv,ca]
  have al (z : Atom) : test (toE z) = Φ (atomEnergy z) (z 1) (z 0) := by simp [test,en,ce,ca]
  simp_rw [← rot, ← al]
  rw [ht.integral_comp' (fun u => test (r u)), ht.integral_comp' test, hr.integral_comp' test]

/-- The angular moment in the transverse plane factors from every radial test. -/
private theorem transverse (p : ℕ) (F : ℝ → ℝ) (c : ℝ)
    (hc : (∫ t in Ioo (-π) π, cos t^(2*p)) = c*(2*π)) :
    (∫ w : ℝ × ℝ, w.1^(2*p)*F (w.1^2+w.2^2) ∂standardPair) =
    c*(∫ w : ℝ × ℝ, (w.1^2+w.2^2)^p*F (w.1^2+w.2^2) ∂standardPair) := by
  let f : ℝ → ℝ := fun r => (r^2)^p*F (r^2)
  have radius (r t : ℝ) : (r*cos t)^2+(r*sin t)^2=r^2 := by
    linear_combination r^2*(sin_sq_add_cos_sq t)
  rw [standardPair_integral, gaussian_polar_separate _ f (fun t => cos t^(2*p)), hc,
    standardPair_integral, gaussian_polar_separate _ f (fun _ => 1)]
  · simp only [setIntegral_const, smul_eq_mul,mul_one,volume_real_Ioo_of_le (show -π≤π by linarith [pi_pos])]
    ring
  · intro r _ t
    dsimp [f]; rw [radius];ring
  · intro r _ t
    dsimp [f]; rw [radius,mul_pow,pow_mul]; ring

private theorem angular_two : (∫ t in Ioo (-π) π, cos t^(2*1)) = (1/2:ℝ)*(2*π) := by
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show -π≤π by linarith [pi_pos])]
  norm_num [integral_cos_sq];ring

private theorem angular_four : (∫ t in Ioo (-π) π, cos t^(2*2)) = (3/8:ℝ)*(2*π) := by
  rw [← integral_Icc_eq_integral_Ioo,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (show -π≤π by linarith [pi_pos])]
  change (∫ t in (-π)..π, cos t^(2+2)) = _
  rw [integral_cos_pow,integral_cos_sq];norm_num;ring

def marked (ρ E t a : ℝ) (p : ℕ) := if |t|≤ρ*√E then a^(2*p) else 0

def atom (ρ : ℝ) (x : ℝ × ℝ) (z : Atom) :=
  marked ρ (atomEnergy z) (x.1*z 1+x.2*z 2) (z 0) 1

private theorem marked_cap (ρ : ℝ) (p : ℕ) (z : ℝ × (ℝ × ℝ)) :
    |marked ρ (CircleGaussianMargin.energy z) z.1 z.2.1 p| ≤ CircleGaussianMargin.energy z^p := by
  unfold marked CircleGaussianMargin.energy
  split
  · rw [pow_mul,abs_of_nonneg (pow_nonneg (sq_nonneg _) _)]
    exact pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg z.1,sq_nonneg z.2.2]) _
  · simp;positivity

private theorem moment (ρ : ℝ) (hρ : 0≤ρ) (hu : ρ≤1) (x : ℝ × ℝ)
    (hx : x.1^2+x.2^2=1) (p : ℕ) (c : ℝ) (hc : 0≤c)
    (ang : (∫ t in Ioo (-π) π, cos t^(2*p)) = c*(2*π)) :
    (∫ z, marked ρ (atomEnergy z) (x.1*z 1+x.2*z 2) (z 0) p ∂atomLaw) ≤
       c*(ρ*∫ z, atomEnergy z^p ∂atomLaw) := by
  open CircleGaussianMargin in
  let μ := G.prod standardPair
  let E := CircleGaussianMargin.energy
  let flag (s t : ℝ) : ℝ := if |s|≤ρ*√(s^2+t) then 1 else 0
  let F := fun z : ℝ × (ℝ × ℝ) => marked ρ (E z) z.1 z.2.1 p
  let H := fun z : ℝ × (ℝ × ℝ) => (z.2.1^2+z.2.2^2)^p * flag z.1 (z.2.1^2+z.2.2^2)
  have eqE (z : Atom) : E (alignedSplit z) = atomEnergy z := by
    rw [alignedSplit_apply];dsimp [E,CircleGaussianMargin.energy,atomEnergy];ring
  have pres : MeasurePreserving alignedSplit atomLaw μ := alignedSplit_preserving
  have eqI : (∫ z, E z^p ∂μ) = ∫ z, atomEnergy z^p ∂atomLaw := by
    rw [←pres.integral_comp' (fun z => E z^p)]; simp_rw [eqE]
  have im : Integrable (fun z => E z^p) μ := by
    apply (alignedSplit_preserving.integrable_comp_emb alignedSplit.measurableEmbedding).1
    simpa only [Function.comp_def,eqE] using energy_pow_integrable p
  have fme : Measurable F := by
    dsimp [F,marked,E,CircleGaussianMargin.energy]
    apply Measurable.ite (measurableSet_le _ _) _ measurable_const <;> fun_prop
  have fi : Integrable F μ := im.mono' fme.aestronglyMeasurable (ae_of_all _ (marked_cap ρ p))
  have hm (z : ℝ × (ℝ × ℝ)) : 0≤H z ∧ H z ≤ CircleGaussianMargin.mark ρ p z.1 (E z) := by
    dsimp [H,flag,E,CircleGaussianMargin.energy,CircleGaussianMargin.mark]
    split
    · simp; exact ⟨by positivity,pow_le_pow_left₀ (by positivity) (by linarith [sq_nonneg z.1]) _⟩
    · simp
  have hi := CircleGaussianMargin.integrable_mark ρ p
  have him : Integrable H μ := by
    apply hi.mono'
    · dsimp [H,flag];apply Measurable.aestronglyMeasurable
      apply Measurable.mul _ (Measurable.ite (measurableSet_le _ _) measurable_const measurable_const) <;> fun_prop
    · exact ae_of_all _ fun z => (abs_of_nonneg (hm z).1).le.trans (hm z).2
  have fg (s : ℝ) : (∫ w : ℝ × ℝ, F (s,w) ∂standardPair) = c*∫ w : ℝ × ℝ, H (s,w) ∂standardPair := by
    have e (w : ℝ × ℝ) : F (s,w) = w.1^(2*p)*flag s (w.1^2+w.2^2) := by
      dsimp [F,marked,E,CircleGaussianMargin.energy,flag];split <;> simp
    simp_rw [e];exact transverse p (flag s) c ang
  calc
    _ = ∫ z, F z ∂μ := by
      rw [rotate x hx (fun e t a => marked ρ e t a p),←pres.integral_comp' F]
      change (∫ z, marked ρ (atomEnergy z) (z 1) (z 0) p ∂atomLaw) =
        ∫ z, marked ρ (E (alignedSplit z)) (z 1) (z 0) p ∂atomLaw
      simp_rw [eqE]
    _ = c*∫ z, H z ∂μ := by
      rw [integral_prod _ fi,integral_prod _ him];simp_rw [fg];rw [integral_const_mul]
    _ ≤ c*∫ z, CircleGaussianMargin.mark ρ p z.1 (E z) ∂μ :=
      mul_le_mul_of_nonneg_left (integral_mono him hi fun z => (hm z).2) hc
    _ = _ := by rw [CircleGaussianMargin.aligned_energy_mark ρ p hρ hu,eqI]

theorem atom_moments {ρ : ℝ} (hρ : 0≤ρ) (hu : ρ≤1) (x : ℝ × ℝ) (hx : x.1^2+x.2^2=1) :
    (∫ z, atom ρ x z ∂atomLaw) ≤ 3*ρ/2 ∧
    (∫ z, (atom ρ x z)^2 ∂atomLaw) ≤ 45*ρ/8 := by
  have a := moment ρ hρ hu x hx 1 (1/2) (by norm_num) angular_two
  have b := moment ρ hρ hu x hx 2 (3/8) (by norm_num) angular_four
  have sqr (z : Atom) : (atom ρ x z)^2 = marked ρ (atomEnergy z) (x.1*z 1+x.2*z 2) (z 0) 2 := by
    unfold atom marked;split <;> ring
  simp only [pow_one,atomEnergy_mean] at a
  simp only [atomEnergy_second] at b
  rw [show (fun z => (atom ρ x z)^2) = _ from funext sqr]
  constructor
  · unfold atom;linarith
  · linarith


private theorem atomMeas {Ω : Type*} [MeasurableSpace Ω] {v : Ω → ℝ × ℝ} {z : Ω → Atom}
    (ρ : ℝ) (hv : Measurable v) (hz : Measurable z) : Measurable fun ω => atom ρ (v ω) (z ω) := by
  unfold atom marked atomEnergy
  have a (k : Fin 3) := (measurable_pi_apply k).comp hz
  apply Measurable.ite (measurableSet_le _ _) _ measurable_const <;> fun_prop

private theorem atomCap (ρ : ℝ) (x : ℝ × ℝ) (z : Atom) : |atom ρ x z| ≤ 1*atomEnergy z := by
  unfold atom marked atomEnergy;split
  · norm_num;linarith [sq_nonneg (z 1),sq_nonneg (z 2)]
  · simp;positivity

def angularAtom (ρ : ℝ) (z : Atom) := ∫ t, atom ρ (phase t) z ∂angularLaw

private theorem angleMeas (ρ : ℝ) : Measurable (Function.uncurry (fun t z => atom ρ (phase t) z)) :=
  atomMeas _ (phase_meas.comp measurable_fst) measurable_snd

private theorem angleMem (ρ : ℝ) : MemLp (angularAtom ρ) 2 atomLaw :=
  (energy_dominated (angle_test_meas (angleMeas ρ)) (angle_cap (fun t => atomCap ρ (phase t)))).1

theorem angular_moments {ρ : ℝ} (hρ : 0≤ρ) (hu : ρ≤1) :
    (∫ z, angularAtom ρ z ∂atomLaw) ≤ 3*ρ/2 ∧
    (∫ z, (angularAtom ρ z)^2 ∂atomLaw) ≤ 45*ρ/8 := by
  let f := fun p : ℝ × Atom => atom ρ (phase p.1) p.2
  have hme : Measurable f := angleMeas ρ
  have hi : Integrable f (angularLaw.prod atomLaw) :=
    ((energy_pow_integrable 1).comp_snd angularLaw).mono' hme.aestronglyMeasurable
      (ae_of_all _ fun p => by simpa using atomCap ρ (phase p.1) p.2)
  have h2 : Integrable (fun p => f p^2) (angularLaw.prod atomLaw) := by
    apply ((energy_pow_integrable 2).comp_snd angularLaw).mono' (hme.pow_const 2).aestronglyMeasurable
    refine ae_of_all _ fun p => ?_
    have eq := pow_le_pow_left₀ (abs_nonneg _) (atomCap ρ (phase p.1) p.2) 2
    change |(atom ρ (phase p.1) p.2)^2| ≤ atomEnergy p.2^2
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs,one_mul] using eq
  have a (t : ℝ) := atom_moments hρ hu (phase t) (Real.cos_sq_add_sin_sq _)
  constructor
  · unfold angularAtom
    rw [(integral_integral_swap hi).symm]
    exact (integral_mono hi.integral_prod_left (integrable_const _) (fun t => (a t).1)).trans_eq (by simp)
  · have cmp (z : Atom) : (angularAtom ρ z)^2 ≤ ∫ t, f (t,z)^2 ∂angularLaw := by
      have me := (hme.comp (measurable_id.prodMk (measurable_const (a:=z))))
      have hm : MemLp (fun t => f (t,z)) 2 angularLaw :=
        (memLp_const (atomEnergy z)).mono' me.aestronglyMeasurable (ae_of_all _ fun t => by simpa using atomCap ρ (phase t) z)
      have h := variance_nonneg (fun t => f (t,z)) angularLaw
      rw [variance_eq_sub hm] at h
      exact sub_nonneg.mp h
    apply (integral_mono (angleMem ρ).integrable_sq h2.integral_prod_right cmp).trans
    rw [(integral_integral_swap h2).symm]
    exact (integral_mono h2.integral_prod_left (integrable_const _) (fun t => (a t).2)).trans_eq (by simp)

private theorem empirical {m : ℕ} (ρ : ℝ) (v : ℂ) (z : Seed m) :
    readoutMargin z ρ v = sampleAverage (atom ρ (coordinates v)) z := by
  unfold readoutMargin sampleAverage
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hl : length z j = √(atomEnergy (fun k => z (j,k))) := by
    rw [←sqrt_sq (show 0≤length z j from sqrt_nonneg _),length_sq];rfl
  rw [marginFlag,hl]
  unfold atom marked CircleFlowPath.pre
  split <;> simp

private def test (N : ℕ) (ρ : ℝ) : Option (Fin N) → Atom → ℝ
  | none => angularAtom ρ
  | some i => atom ρ (CircleFlowPath.circleInput N i)

private theorem angularEmpirical {m : ℕ} (ρ : ℝ) (z : Seed m) :
    (∫ u, readoutMargin z ρ (CircleSignedAngular.x u) ∂angularLaw) = sampleAverage (angularAtom ρ) z := by
  simp_rw [empirical]
  exact angle_average _ (angleMeas ρ) 1 (fun t => atomCap ρ (phase t)) z

/-- Simultaneous empirical readout-weighted count used by the deterministic drift. -/
def Good {m : ℕ} (N : ℕ) (ρ : ℝ) (z : Seed m) : Prop :=
  (∀ i, readoutMargin z ρ (CircleEscape.gridPoint N i) ≤ 2*ρ) ∧
  (∫ u, readoutMargin z ρ (CircleSignedAngular.x u) ∂angularLaw) ≤ 2*ρ

theorem failure {m N : ℕ} (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hu : ρ≤1) :
    (seedLaw m).real {z | ¬Good N ρ z} ≤ 45*(N+1:ℝ)/(2*m*ρ) := by
  let bad (q : Option (Fin N)) := {z : Seed m | ρ/2 ≤ |sampleAverage (test N ρ q) z -
    ∫ a, test N ρ q a ∂atomLaw|}
  have info (q : Option (Fin N)) : MemLp (test N ρ q) 2 atomLaw ∧
      (∫ z, test N ρ q z ∂atomLaw) ≤ 3*ρ/2 ∧ (∫ z, (test N ρ q z)^2 ∂atomLaw) ≤ 45*ρ/8 := by
    cases q with
    | none => exact ⟨angleMem ρ,angular_moments hρ.le hu⟩
    | some i => exact ⟨(energy_dominated (atomMeas ρ measurable_const measurable_id) (atomCap ρ _)).1,
        atom_moments hρ.le hu _ (unit_grid_eq i)⟩
  have sub : {z : Seed m | ¬Good N ρ z} ⊆ ⋃ q, bad q := by
    intro z hz
    by_contra h
    have bound (q : Option (Fin N)) : sampleAverage (test N ρ q) z ≤ 2*ρ := by
      have no : z ∉ bad q := fun v => h (mem_iUnion_of_mem q v)
      change ¬ρ/2 ≤ |_ - _| at no
      have less := lt_of_not_ge no
      change |_ - _| < ρ/2 at less
      linarith [(le_abs_self _).trans_lt less,(info q).2.1]
    apply hz
    constructor
    · intro i;rw [empirical];exact bound (some i)
    · rw [angularEmpirical];exact bound none
  have tail (q : Option (Fin N)) : (seedLaw m).real (bad q) ≤ 45/(2*m*ρ) := by
    have e := (variance_le_expectation_sq (info q).1.aestronglyMeasurable).trans (info q).2.2
    exact (average_concentration hm (info q).1 e (half_pos hρ)).trans_eq (by field_simp; ring)
  refine (measureReal_mono sub).trans ((measureReal_iUnion_fintype_le bad).trans
    ((Finset.sum_le_sum (fun q _ => tail q)).trans_eq ?_))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_option,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring


theorem measurable_good (m N : ℕ) (ρ : ℝ) : MeasurableSet {z : Seed m | Good N ρ z} := by
  change MeasurableSet ({z : Seed m | ∀ i, readoutMargin z ρ (CircleEscape.gridPoint N i) ≤ 2*ρ} ∩ _)
  apply MeasurableSet.inter
  · apply measurable_forall_finite
    intro i
    simp_rw [empirical]
    exact measurableSet_le (sampleAverage_meas (atomMeas _ measurable_const measurable_id)) measurable_const
  · change MeasurableSet {z : Seed m | (∫ u, readoutMargin z ρ (CircleSignedAngular.x u) ∂angularLaw) ≤ 2*ρ}
    simp_rw [angularEmpirical]
    exact measurableSet_le (sampleAverage_meas (angle_test_meas (angleMeas ρ))) measurable_const

/-- The readout-only margin consumes at most δ/6 when the square root of the
width meets the revised margin constraint. -/
theorem failure_design {m N : ℕ} (hm : 0<m) {A δ : ℝ} (hA : 0<A) (hδ : 0<δ)
    (hsmall : A/√m ≤ 1) (width : 135*(N+1:ℝ)/(δ*A) ≤ √m) :
    (seedLaw m).real {z | ¬ Good N (A/√m) z} ≤ δ/6 := by
  have hs : (0:ℝ)<√m := by positivity
  have h := (div_le_iff₀ (mul_pos hδ hA)).mp width
  apply (failure hm (div_pos hA hs) hsmall).trans
  have pos : 0 < 2*(m:ℝ)*(A/√m) := by positivity
  apply (div_le_iff₀ pos).2
  have eq : (m:ℝ)*(A/√m)=√m*A := by
    nth_rw 1 [←Real.sq_sqrt (Nat.cast_nonneg m)]
    field_simp
  rw [mul_assoc (2:ℝ),eq];linarith

/-- Readout-weighted counts control every mixed grid entry along a GD
segment. The bound 28ρ strengthens the design's 36ρ budget. -/
theorem grid_segment_drift {N m : ℕ} (hm : 0<m) {ρ : ℝ} (hρ : 0≤ρ) (hu : ρ≤1)
    {z₀ v : CircleFlowPath.State m} (s : ℝ) (tv : Tube ρ z₀ v)
    (ts : Tube ρ z₀ (CircleDiscreteTracking.seg N v s))
    (en : meanEnergy z₀≤4) (nodes : ∀ i, readoutMargin z₀ ρ (CircleEscape.gridPoint N i)≤2*ρ)
    (i j : Fin N) :
    |CircleDiscreteTracking.mixedRow N v (CircleFlowPath.circleInput N i) s j -
      gridGram 1 z₀ (startGates z₀) i j| ≤ 28*ρ := by
  let X := CircleFlowPath.circleInput N
  let z := CircleDiscreteTracking.seg N v s
  let ga := startGates (m:=m) (N:=N)
  have each (k : Fin m) := readout_atom_drift (τ:=1) (C:=1) (s:=ga z i) (t:=ga v j)
    (s₀:=ga z₀ i) (t₀:=ga z₀ j) k le_rfl (by norm_num) hρ (grid_unit i) (grid_unit j)
    ts tv (actualGate_admissible _) (actualGate_admissible _) (actualGate_admissible _) (actualGate_admissible _)
  have sums := (Finset.abs_sum_le_sum_abs _ (Finset.univ : Finset (Fin m))).trans (Finset.sum_le_sum (fun k _ => each k))
  change |entry 1 z v (X i) (X j) (ga z i) (ga v j) -
    entry 1 z₀ z₀ (X i) (X j) (ga z₀ i) (ga z₀ j)| ≤ _
  rw [entry_sum hm,entry_sum hm,← sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_nonneg (show 0≤(m:ℝ) from Nat.cast_nonneg m)]
  apply (div_le_div_of_nonneg_right sums (Nat.cast_nonneg m)).trans
  calc
    _ = (4*ρ+2*ρ^2)*meanEnergy z₀ +
      readoutMargin z₀ ρ (CircleEscape.gridPoint N i)+readoutMargin z₀ ρ (CircleEscape.gridPoint N j) := by
      unfold meanEnergy readoutMargin
      simp only [one_mul,Finset.sum_add_distrib,← Finset.mul_sum,add_div]
      simp only [CircleFlowPath.circleInput,coordinates,mul_div_assoc]
    _ ≤ _ := by
      have q : ρ^2≤ρ := by nlinarith [mul_nonneg hρ (sub_nonneg.mpr hu)]
      nlinarith only [mul_le_mul_of_nonneg_left en (show 0≤4*ρ+2*ρ^2 by positivity),nodes i,nodes j,q]

end CircleReadoutMargin
