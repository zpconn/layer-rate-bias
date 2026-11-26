module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import Mathlib.Tactic

/-! Uniform anti-concentration at the decision threshold of the actual initial
grid mean. Its distribution is a mixture of centered Gaussian laws. No lower
bound on a conditional variance is needed. -/

public section
noncomputable section
namespace CircleScoreMargin
open Real MeasureTheory ProbabilityTheory CircleEscapeBridge CircleFlowPath
open CircleInitializationConcentration Set

def densityBound := 2 * exp (-(1/2)) / √(2*π)

private theorem density_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity

theorem gaussian_density_near_one (v : NNReal) (hv : v ≠ 0) (x : ℝ) (hx : 1/2 ≤ x) :
    gaussianPDFReal 0 v x ≤ densityBound := by
  let u := x / √(v:ℝ)
  have hvpos : 0 < (v:ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hv)
  have hu : 0 < u := div_pos (by linarith) (sqrt_pos_of_pos hvpos)
  have hl := log_le_sub_one_of_pos (sq_pos_of_pos hu)
  rw [log_pow] at hl
  have hmax : u * exp (-u^2/2) ≤ exp (-(1/2)) := by
    rw [← exp_log hu, ← exp_add]
    rw [exp_log hu]
    apply exp_le_exp.mpr
    norm_num at hl
    linarith
  have identity : gaussianPDFReal 0 v x = (u*exp (-u^2/2))/(x*√(2*π)) := by
    unfold gaussianPDFReal
    rw [sqrt_mul (show 0≤2*π by positivity), sub_zero]
    have hxpos : 0 < x := by linarith
    have hu2 : u^2 = x^2/(v:ℝ) := by unfold u; rw [div_pow, sq_sqrt hvpos.le]
    rw [hu2, show -(x^2/(v:ℝ))/2 = -x^2/(2*(v:ℝ)) by ring]
    unfold u
    field_simp
  rw [identity]
  calc
    _ ≤ exp (-(1/2))/(x*√(2*π)) := div_le_div_of_nonneg_right hmax (by positivity)
    _ ≤ densityBound := by
      unfold densityBound
      have ha : 0 < x := by linarith
      have hb : 0 < √(2*π) := by positivity
      apply (div_le_div_iff₀ (mul_pos ha hb) hb).mpr
      nlinarith [mul_nonneg (show 0 ≤ 2*x-1 by linarith) (mul_nonneg (exp_pos (-(1/2))).le hb.le)]

def band (δ : ℝ) := Icc (1-δ) (1+δ)

theorem gaussian_band (v : NNReal) {δ : ℝ} (hδ : 0 ≤ δ) (hu : δ ≤ 1/2) :
    (gaussianReal 0 v).real (band δ) ≤ 2*δ*densityBound := by
  by_cases hv : v = 0
  · subst v
    have hz : (0:ℝ) ∉ band δ := fun h => by linarith [h.1]
    simp only [gaussianReal_zero_var, Measure.real, Measure.dirac_apply, indicator_of_notMem hz, ENNReal.toReal_zero]
    exact mul_nonneg (by positivity) density_nonneg
  · rw [Measure.real, gaussianReal_apply_eq_integral _ hv,
      ENNReal.toReal_ofReal (integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _)]
    calc
      _ ≤ ∫ _x in band δ, densityBound := by
        apply setIntegral_mono_on (integrable_gaussianPDFReal _ _).integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc
        exact fun x hx => gaussian_density_near_one v hv x (by linarith [hx.1])
      _ = _ := by rw [setIntegral_const, band, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]; ring

/-- This is Q_N f_0 with the actual circle inputs and learner normalization. -/
def gridMean (N m : ℕ) (z : Seed m) :=
  (1/(N:ℝ))*∑ i : Fin N, output (1/√m) z (circleInput N i)

private def scoreWeights (N m : ℕ) (h : Hidden m) (j : Fin m) :=
  (1/(N:ℝ))*∑ i : Fin N, (1/√m)*hiddenFeature (circleInput N i) h j

private theorem gridMean_split (N m : ℕ) (z : Seed m) :
    gridMean N m z = linearReadout (scoreWeights N m ((splitLayer m z).2)) ((splitLayer m z).1) := by
  unfold gridMean
  simp_rw [output_split,splitOutput,linearReadout,scoreWeights, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; ring

/-- The actual finite-width grid mean obeys one uniform band estimate, for all
designs, widths, and all Gaussian seeds. This includes any zero-variance slice. -/
theorem gridMean_near_tie (N m : ℕ) {δ : ℝ} (hδ : 0≤δ) (hu : δ≤1/2) :
    (seedLaw m).real {z | |1-gridMean N m z|≤δ} ≤ 2*δ*densityBound := by
  let A := {p : Layer m × Hidden m | linearReadout (scoreWeights N m p.2) p.1 ∈ band δ}
  have hA : MeasurableSet A := by
    apply measurableSet_Icc.preimage
    unfold linearReadout scoreWeights hiddenFeature
    fun_prop
  have hpre : {z | |1-gridMean N m z|≤δ} = (splitLayer m) ⁻¹' A := by
    ext z; simp only [mem_ofPred_eq,abs_le,gridMean_split,mem_preimage,A,band,mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [hpre, (split_preserving m).measureReal_preimage hA.nullMeasurableSet]
  have hb : 0 ≤ 2*δ*densityBound := mul_nonneg (by positivity) density_nonneg
  change (((layerLaw m).prod (hiddenLaw m)) A).toReal ≤ _
  rw [← ENNReal.toReal_ofReal hb]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr
  rw [Measure.prod_apply_symm hA]
  calc
    _ ≤ ∫⁻ _h, ENNReal.ofReal (2*δ*densityBound) ∂hiddenLaw m := by
      apply lintegral_mono; intro h
      change layerLaw m {a | linearReadout (scoreWeights N m h) a ∈ band δ} ≤ _
      rw [(linearReadout_law (scoreWeights N m h)).measure_eq (p:=fun x => x ∈ band δ) measurableSet_Icc]
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal hb]
      exact gaussian_band _ hδ hu
    _ = _ := by simp

/-- Wrong or tied output signs can occur only in the score band or where
the true paired prediction error reaches the prescribed margin. -/
theorem sign_miss_bound (N m : ℕ) (D : Seed m → ℝ) (c δ : ℝ)
    (hc : 0 < c) (hδ : 0≤δ) (hu : δ≤1/2) :
    (seedLaw m).real {z | D z*(1-gridMean N m z) ≤ 0} ≤
      (seedLaw m).real {z | c*δ ≤ |D z-c*(1-gridMean N m z)|} + 2*δ*densityBound := by
  let fail := {z | c*δ ≤ |D z-c*(1-gridMean N m z)|}
  let tie := {z | |1-gridMean N m z| ≤ δ}
  have hs : {z | D z*(1-gridMean N m z) ≤ 0} ⊆ fail ∪ tie := by
    intro z hz
    by_cases ht : |1-gridMean N m z| ≤ δ
    · exact Or.inr ht
    left
    change c*δ ≤ |D z-c*(1-gridMean N m z)|
    let g := 1-gridMean N m z
    change D z*g ≤ 0 at hz
    change ¬ |g| ≤ δ at ht
    change c*δ ≤ |D z-c*g|
    rcases le_or_gt 0 g with h | h
    · rw [abs_of_nonneg h] at ht
      have hg : 0 < g := lt_of_le_of_lt hδ (lt_of_not_ge ht)
      have hy : D z ≤ 0 := le_of_not_gt (fun hh => (mul_pos hh hg).not_ge hz)
      exact (show c*δ ≤ -(D z-c*g) by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ht)) hc.le]).trans (neg_le_abs _)
    · rw [abs_of_neg h] at ht
      have hy : 0 ≤ D z := le_of_not_gt (fun hh => (mul_pos_of_neg_of_neg hh h).not_ge hz)
      exact (show c*δ ≤ D z-c*g by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ht)) hc.le]).trans (le_abs_self _)
  exact (measureReal_mono hs).trans ((measureReal_union_le fail tie).trans (add_le_add le_rfl (gridMean_near_tie N m hδ hu)))

end CircleScoreMargin
