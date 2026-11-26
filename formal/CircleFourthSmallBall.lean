module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleEscapeBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! A nondegenerate real feature coefficient has small probability of landing
near zero under the actual finite-width Gaussian initialization. -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 800000

namespace CircleFourthSmallBall
open Real MeasureTheory ProbabilityTheory Set CircleEscapeBridge CircleInitializationConcentration
open scoped ENNReal

def hiddenAt {m : ℕ} (z : Seed m) (j : Fin m) (k : Fin 2) := z (j,k.succ)

def readout {m : ℕ} (V : Layer 2 → ℝ) (z : Seed m) : ℝ :=
  (1/sqrt m)*∑ j, z (j,0)*V (hiddenAt z j)

private def single (V : Layer 2 → ℝ) (a : Atom) := V (fun k => a k.succ)^2

private theorem hidden_project :
    MeasurePreserving (fun a : Atom => fun k : Fin 2 => a k.succ) atomLaw (layerLaw 2) :=
  measurePreserving_snd.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 0)

private theorem raw_lower_tail {m : ℕ} (hm : 0<m) {V : Layer 2 → ℝ} (hV : Measurable V)
    (dom : ∀ x, V x^2 ≤ x 0^2+x 1^2) {c : ℝ} (hc : 0<c)
    (lower : c≤∫ x, V x^2 ∂layerLaw 2) :
    (seedLaw m).real {z | sampleAverage (single V) z<c/2} ≤ 15/(m*(c/2)^2) := by
  have sm : Measurable (single V) := (hV.comp hidden_project.measurable).pow_const _
  have sb (z : Atom) : single V z ≤ atomEnergy z := by
    change V (fun k => z k.succ)^2 ≤ z 0^2+z 1^2+z 2^2
    have h := dom (fun k => z k.succ)
    change _ ≤ z 1^2+z 2^2 at h
    linarith [sq_nonneg (z 0)]
  have sn (z : Atom) : 0 ≤ single V z := sq_nonneg _
  have mem : MemLp (single V) 2 atomLaw := (energy_mem 2).of_le sm.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sn z),abs_of_nonneg (atomEnergy_nonneg z)] using sb z)
  have vv : ProbabilityTheory.variance (single V) atomLaw ≤ 15 := by
    apply (variance_le_expectation_sq mem.aestronglyMeasurable).trans
    rw [← atomEnergy_second]
    exact integral_mono mem.integrable_sq (energy_pow_integrable 2)
      (fun z => pow_le_pow_left₀ (sn z) (sb z) 2)
  have mean : ∫ z, single V z ∂atomLaw = ∫ x, V x^2 ∂layerLaw 2 :=
    hidden_project.hasLaw.integral_comp (hV.pow_const 2).aestronglyMeasurable
  apply (measureReal_mono (s₂:={z | c/2≤|sampleAverage (single V) z-∫ a, single V a ∂atomLaw|})
    (fun ⦃z⦄ h => ?_)).trans (average_concentration hm mem vv (by positivity : 0<c/2))
  change sampleAverage (single V) z<c/2 at h
  change c/2 ≤ |sampleAverage (single V) z-∫ a, single V a ∂atomLaw|
  rw [mean]
  linarith [neg_le_abs (sampleAverage (single V) z-∫ x, V x^2 ∂layerLaw 2)]

private theorem gaussian_interval {v : NNReal} {q δ : ℝ} (hq : 0<q) (hv : q≤v) (hd : 0≤δ) :
    (gaussianReal 0 v).real (Icc (-δ) δ) ≤ 2*δ/sqrt q := by
  have vp : (0:ℝ)<v := hq.trans_le hv
  have nz : v ≠ 0 := by exact_mod_cast vp.ne'
  have den : q ≤ 2*π*v := hv.trans (le_mul_of_one_le_left vp.le (by linarith [pi_gt_three]))
  have bound (x : ℝ) : gaussianPDFReal 0 v x ≤ 1/sqrt q := by
    rw [gaussianPDFReal]
    apply (mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))).trans
    simpa only [one_div] using one_div_le_one_div_of_le (sqrt_pos.mpr hq) (sqrt_le_sqrt den)
  rw [measureReal_def,gaussianReal_apply_eq_integral 0 nz,
    ENNReal.toReal_ofReal (integral_nonneg (gaussianPDFReal_nonneg _ _))]
  have h := setIntegral_mono_on (s:=Icc (-δ) δ) (integrable_gaussianPDFReal 0 v).integrableOn
    (integrableOn_const (measure_Icc_lt_top.ne) (C:=1/sqrt q)) measurableSet_Icc (fun x _ => bound x)
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith),smul_eq_mul] at h
  exact h.trans_eq (by ring)

private def coeff {m : ℕ} (V : Layer 2 → ℝ) (h : Hidden m) (j : Fin m) :=
  (1/sqrt m)*V (fun k => h k j)

private def empirical {m : ℕ} (V : Layer 2 → ℝ) (h : Hidden m) := ∑ j, coeff V h j^2

private theorem empirical_split {m : ℕ} (V : Layer 2 → ℝ) (z : Seed m) :
    empirical V (splitLayer m z).2 = sampleAverage (single V) z := by
  unfold empirical coeff sampleAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((1/sqrt m)*V (hiddenAt z j))^2 = (m:ℝ)⁻¹*(V (hiddenAt z j))^2
  rw [mul_pow,one_div,inv_pow,sq_sqrt (Nat.cast_nonneg m)]

private theorem readout_split {m : ℕ} (V : Layer 2 → ℝ) (z : Seed m) :
    readout V z = linearReadout (coeff V (splitLayer m z).2) (splitLayer m z).1 := by
  rw [readout,Finset.mul_sum,linearReadout]
  apply Finset.sum_congr rfl
  intro j _
  change (1/sqrt m)*(z (j,0)*_)=(1/sqrt m)*V (hiddenAt z j)*z (j,0)
  ring

private theorem coeff_joint {m : ℕ} {V : Layer 2 → ℝ} (v : Measurable V) (j : Fin m) :
    Measurable (fun h : Hidden m => coeff V h j) := by
  apply Measurable.const_mul
  exact v.comp (measurable_pi_iff.2 fun k => (measurable_pi_apply j).comp (measurable_pi_apply k))

private theorem conditional_small {m : ℕ} {V : Layer 2 → ℝ} (hV : Measurable V)
    {q δ : ℝ} (hq : 0<q) (hd : 0≤δ) :
    let S := {p : Layer m × Hidden m | |linearReadout (coeff V p.2) p.1|≤δ ∧ q≤empirical V p.2}
    ((layerLaw m).prod (hiddenLaw m)).real S ≤ 2*δ/sqrt q := by
  intro S
  have em : Measurable (empirical (m:=m) V) :=
    Finset.measurable_fun_sum _ fun j _ => (coeff_joint hV j).pow_const 2
  have rm : Measurable (fun p : Layer m × Hidden m => linearReadout (coeff V p.2) p.1) :=
    Finset.measurable_fun_sum _ fun j _ => ((coeff_joint hV j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_fst)
  have ms : MeasurableSet S := (measurableSet_le (continuous_abs.measurable.comp rm) measurable_const).inter
    (measurableSet_le measurable_const (em.comp measurable_snd))
  let L := 2*δ/sqrt q
  have l0 : 0≤L := by dsimp [L]; positivity
  have sec (h : Hidden m) : layerLaw m ((fun a => (a,h)) ⁻¹' S) ≤ ENNReal.ofReal L := by
    by_cases good : q≤empirical V h
    · let b := coeff V h
      have o : 0≤empirical V h := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have g := gaussian_interval (v:=(empirical V h).toNNReal) hq (by simpa only [Real.coe_toNNReal _ o] using good) hd
      have law : MeasurePreserving (linearReadout b) (layerLaw m) (gaussianReal 0 (empirical V h).toNNReal) :=
        ⟨by unfold linearReadout; fun_prop,(linearReadout_law b).map_eq⟩
      have eq : (fun a => (a,h)) ⁻¹' S = linearReadout b ⁻¹' Icc (-δ) δ := by
        ext a
        change (|linearReadout b a|≤δ ∧ q≤empirical V h) ↔ -δ≤linearReadout b a ∧ linearReadout b a≤δ
        simp [good,abs_le]
      rw [eq,law.measure_preimage measurableSet_Icc.nullMeasurableSet]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      simpa only [ENNReal.toReal_ofReal l0,measureReal_def,L] using g
    · have eq : (fun a => (a,h)) ⁻¹' S = ∅ := by ext a;simp [S,good]
      simp [eq]
  rw [measureReal_def,Measure.prod_apply_symm ms]
  have top := ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_le_const (ae_of_all (hiddenLaw m) sec))
  exact top.trans_eq (ENNReal.toReal_ofReal l0)

/-- Uniform finite-width Gaussian small-ball bound for a real feature mode.
The first term is the conditional Gaussian density estimate and the second
accounts for small empirical hidden-feature variance. -/
theorem readout_small_ball {m : ℕ} (hm : 0<m) {V : Layer 2 → ℝ} (hV : Measurable V)
    (dom : ∀ x, V x^2≤x 0^2+x 1^2) {c : ℝ} (hc : 0<c) (lower : c≤∫ x, V x^2 ∂layerLaw 2)
    {δ : ℝ} (hd : 0≤δ) :
    (seedLaw m).real {z | |readout V z|≤δ} ≤ 2*δ/sqrt (c/2)+15/(m*(c/2)^2) := by
  let S := {p : Layer m × Hidden m | |linearReadout (coeff V p.2) p.1|≤δ ∧ c/2≤empirical V p.2}
  have em : Measurable (empirical (m:=m) V) :=
    Finset.measurable_fun_sum _ fun j _ => (coeff_joint hV j).pow_const 2
  have rm : Measurable (fun p : Layer m × Hidden m => linearReadout (coeff V p.2) p.1) :=
    Finset.measurable_fun_sum _ fun j _ => ((coeff_joint hV j).comp measurable_snd).mul
      ((measurable_pi_apply j).comp measurable_fst)
  have ms : MeasurableSet S := (measurableSet_le (continuous_abs.measurable.comp rm) measurable_const).inter
    (measurableSet_le measurable_const (em.comp measurable_snd))
  have hsub : {z : Seed m | |readout V z|≤δ} ⊆ (splitLayer m) ⁻¹' S ∪ {z | sampleAverage (single V) z<c/2} := by
    intro z hz
    rcases lt_or_ge (sampleAverage (single V) z) (c/2) with low | high
    · exact Or.inr low
    · exact Or.inl ⟨(readout_split V z) ▸ hz, (empirical_split V z).symm ▸ high⟩
  apply ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
  rw [(split_preserving m).measureReal_preimage ms.nullMeasurableSet]
  exact add_le_add (conditional_small hV (by positivity : 0<c/2) hd) (raw_lower_tail hm hV dom hc lower)

end CircleFourthSmallBall
