module

public import CircleInitializationConcentration
import all CircleInitializationConcentration
import all CircleEscapeBridge
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

/-! A two-sided exponential concentration bound for empirical means of any
measurable single-neuron mark dominated by its squared Gaussian length. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped NNReal
namespace CircleGaussianBernstein
open CircleInitializationConcentration CircleEscapeBridge

def energy (z : Atom) : ℝ := ∑ k, (z k)^2

theorem energy_mgf :
    (∫ z, exp (energy z/8) ∂atomLaw) = (sqrt (4/3))^3 := by
  have hgauss : (∫ x : ℝ, exp (x^2/8) ∂gaussianReal 0 1) = sqrt (4/3) := by
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
    have row (x : ℝ) : gaussianPDFReal 0 1 x • exp (x^2/8) =
        (1/sqrt (2*π))*exp (-(3/8:ℝ)*x^2) := by
      simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul]
      rw [mul_assoc,← exp_add]
      congr 2 <;> ring
    simp_rw [row]
    rw [integral_const_mul, integral_gaussian]
    rw [one_div, mul_comm, ← div_eq_mul_inv, ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
    ring
  have split (z : Atom) : exp (energy z/8) = ∏ k, exp ((z k)^2/8) := by
    simp [energy,Finset.sum_div,Real.exp_sum]
  simp_rw [split]
  rw [atomLaw,integral_fintype_prod_eq_pow (fun x : ℝ => exp (x^2/8)),hgauss]
  simp

private theorem exp_remainder (v : ℝ) : exp v ≤ 1+v+v^2*exp |v| := by
  have b := Complex.norm_exp_sub_sum_le_norm_mul_exp (v:ℂ) 2
  have bc : (Complex.exp v - ∑ k ∈ Finset.range 2, (v:ℂ)^k / k.factorial) =
      ((exp v-(1+v):ℝ):ℂ) := by
    norm_num [Finset.sum_range_succ,Complex.ofReal_exp]
  rw [bc, Complex.norm_real,Complex.norm_real] at b
  simp only [Real.norm_eq_abs,sq_abs] at b
  linarith [le_abs_self (exp v-(1+v))]

private theorem quadratic_exp (x t S : ℝ) (hx : |x| ≤ S) (ht : |t| ≤ 1/16) :
    (t*x)^2 * exp |t*x| ≤ t^2 * (512*exp (S/8)) := by
  have lim := Real.sum_le_exp_of_nonneg (div_nonneg (abs_nonneg x) (by norm_num : (0:ℝ)≤16)) 3
  norm_num [Finset.sum_range_succ] at lim
  have hp : x^2 ≤ 512*exp (|x|/16) := by nlinarith [sq_abs x,abs_nonneg x]
  have he : exp |t*x| ≤ exp (S/16) := by
    apply exp_le_exp.mpr
    rw [abs_mul]
    linarith [mul_le_mul_of_nonneg_right ht (abs_nonneg x)]
  rw [mul_pow,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
  calc
    _ ≤ (512*exp (|x|/16))*exp (S/16) := mul_le_mul hp he (exp_nonneg _) (by positivity)
    _ = 512*exp (|x|/16+S/16) := by rw [exp_add]; ring
    _ ≤ 512*exp (S/8) := by gcongr; linarith

/-- The centered moment generating function of an actual Gaussian mark.
Centering after integration cancels its linear Taylor term exactly. -/
theorem centered_mgf (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ energy z) (t : ℝ) (ht : |t| ≤ 1/16) :
    let Y := fun z => X z - ∫ u, X u ∂atomLaw
    Integrable (fun z => exp (t*Y z)) atomLaw ∧ mgf Y atomLaw t ≤ exp (1024*t^2) := by
  let S := energy
  let D := fun z => exp (S z/8)
  have hD : Integrable D atomLaw := by
    by_contra h
    have h0 := integral_undef h
    have hp : 0 < (sqrt (4/3:ℝ))^3 := by positivity
    change (∫ z, exp (energy z/8) ∂atomLaw) = 0 at h0
    linarith [energy_mgf]
  have iX : Integrable X atomLaw := by
    apply (hD.const_mul 8).mono' hX.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have hx := dom z
    have ex := add_one_le_exp (S z/8)
    change |X z| ≤ 8*exp (S z/8)
    linarith
  have iExp : Integrable (fun z => exp (t*X z)) atomLaw := by
    apply hD.mono' (hX.const_mul t).exp.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right ht (abs_nonneg (X z))
    rw [← abs_mul] at h
    change t*X z ≤ energy z / 8
    linarith [le_abs_self (t*X z),dom z,abs_nonneg (X z)]
  have expt (z : Atom) : exp (t*X z) ≤ 1 + t*X z + (512*t^2)*D z := by
    have a := exp_remainder (t*X z)
    have b := quadratic_exp _ _ _ (dom z) ht
    change _ ≤ 1+t*X z+(512*t^2)*exp (energy z/8)
    linarith
  have hmean := integral_mono iExp (((integrable_const 1).add (iX.const_mul t)).add
    (hD.const_mul (512*t^2))) expt
  simp only [Pi.add_apply] at hmean
  have ia : Integrable (fun z => 1+t*X z) atomLaw := (integrable_const 1).add (iX.const_mul t)
  rw [integral_add ia (hD.const_mul (512*t^2)),
    integral_add (integrable_const 1) (iX.const_mul t), integral_const, integral_const_mul,
    integral_const_mul] at hmean
  have val : (∫ z, D z ∂atomLaw) ≤ 2 := by
    change (∫ z, exp (energy z/8) ∂atomLaw) ≤ 2
    rw [energy_mgf]
    have sqr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4/3)
    have ub : sqrt (4/3:ℝ) ≤ 5/4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ub (sq_nonneg (sqrt (4/3:ℝ)))]
  let M := ∫ z, X z ∂atomLaw
  have fac (z : Atom) : exp (t*(X z-M)) = exp (-(t*M)) * exp (t*X z) := by
    rw [← exp_add]; congr 1; ring
  change Integrable (fun z => exp (t*(X z-M))) atomLaw ∧
    (∫ z, exp (t*(X z-M)) ∂atomLaw) ≤ exp (1024*t^2)
  simp_rw [fac]
  refine ⟨iExp.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hupper : (∫ z, exp (t*X z) ∂atomLaw) ≤ 1 + (t*M+1024*t^2) := by
    simp only [probReal_univ,one_smul] at hmean
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left val (show 0 ≤ 512*t^2 by positivity)]
  calc
    _ ≤ exp (-(t*M))*exp (t*M + 1024*t^2) :=
      mul_le_mul_of_nonneg_left (hupper.trans (by linarith [add_one_le_exp (t*M+1024*t^2)]))
        (exp_nonneg _)
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- Chernoff transfer from a single mark to any finite empirical width. -/
theorem empirical_chernoff {m : ℕ} (hm : 0 < m) (Y : Atom → ℝ) (hy : Measurable Y)
    {u t K : ℝ} (ht : 0 ≤ t) (hint : Integrable (fun z => exp (t*Y z)) atomLaw)
    (mg : mgf Y atomLaw t ≤ exp K) :
    (seedLaw m).real {ω | u ≤ sampleAverage Y ω} ≤ exp ((m:ℝ)*(K-t*u)) := by
  let F (j : Fin m) (a : Fin m → Atom) := Y (a j)
  let ν := Measure.pi (fun _ : Fin m => atomLaw)
  have hf (j : Fin m) : Measurable (F j) := hy.comp (measurable_pi_apply j)
  have ind : iIndepFun F ν := iIndepFun_pi (fun _ => hy.aemeasurable)
  have expmeas : Measurable (fun z => exp (t*Y z)) := (hy.const_mul t).exp
  have hi (j : Fin m) : Integrable (fun a => exp (t*F j a)) ν :=
    (measurePreserving_eval (fun _ : Fin m => atomLaw) j).integrable_comp_of_integrable hint
  have subset : {ω : Seed m | u ≤ sampleAverage Y ω} ⊆
      (currySeed m) ⁻¹' {a | (m:ℝ)*u ≤ (∑ j, F j) a} := by
    intro ω hlo
    change (m:ℝ)*u ≤ (∑ j, F j) ((currySeed m) ω)
    simp only [Finset.sum_apply,F]
    change u ≤ (m:ℝ)⁻¹ * (∑ j, Y ((currySeed m) ω j)) at hlo
    have mpos : (0:ℝ)<m := by exact_mod_cast hm
    have h := mul_le_mul_of_nonneg_left hlo mpos.le
    rwa [← mul_assoc,mul_inv_cancel₀ mpos.ne',one_mul] at h
  have htarg : MeasurableSet {a | (m:ℝ)*u ≤ (∑ j, F j) a} := by
    apply measurableSet_le measurable_const
    have hs := Finset.measurable_fun_sum (Finset.univ : Finset (Fin m)) (fun j _ => hf j)
    simpa only [← Finset.sum_apply] using hs
  apply (measureReal_mono subset).trans
  rw [(curry_preserving m).measureReal_preimage htarg.nullMeasurableSet]
  have cher := measure_ge_le_exp_mul_mgf (μ := ν) ((m:ℝ)*u) ht
    (ind.integrable_exp_mul_sum hf (s := Finset.univ) (fun i _ => hi i))
  apply cher.trans
  rw [ind.mgf_sum hf]
  have single (j : Fin m) : mgf (F j) ν t ≤ exp (K) := by
    have id := (measurePreserving_eval (fun _ : Fin m => atomLaw) j).hasLaw.integral_comp
      expmeas.aestronglyMeasurable
    exact id.le.trans mg
  calc
    _ ≤ exp (-t*((m:ℝ)*u)) * ∏ _j : Fin m, exp (K) := by
      apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
      exact Finset.prod_le_prod₀ (fun j _ => mgf_nonneg) (fun j _ => single j)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_nat_mul,←exp_add]
      congr 1
      ring

private theorem upper_tail {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ energy z) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 128) :
    (seedLaw m).real {ω | u ≤ sampleAverage X ω - ∫ z, X z ∂atomLaw} ≤
      exp (-(m:ℝ)*u^2/4096) := by
  let t := u/2048
  let Y (z : Atom) := X z - ∫ z, X z ∂atomLaw
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : |t| ≤ 1/16 := by dsimp [t]; rw [abs_of_nonneg (by positivity)]; linarith
  have h := centered_mgf X hX dom t hs
  have avg (ω : Seed m) : sampleAverage Y ω = sampleAverage X ω - ∫ z, X z ∂atomLaw := by
    simp only [Y,sampleAverage,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have ch := empirical_chernoff hm Y (hX.sub measurable_const) (u:=u) ht h.1 h.2
  simp_rw [avg] at ch
  exact ch.trans_eq (by congr 1; dsimp [t]; ring)

/-- Unit-scale Bernstein regime for independent Gaussian neuron marks of any sign.
At u=64√(d/m), d≤m, its right-hand side is 2 exp(−d). -/
theorem two_sided {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ energy z) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 128) :
    (seedLaw m).real {ω | u ≤ |sampleAverage X ω - ∫ z, X z ∂atomLaw|} ≤
      2*exp (-(m:ℝ)*u^2/4096) := by
  let A := fun ω : Seed m => sampleAverage X ω - ∫ z, X z ∂atomLaw
  have hupp := upper_tail hm X hX dom hu hu'
  have hlow := upper_tail hm (fun z => -X z) hX.neg (fun z => by simpa using dom z) hu hu'
  have heq (ω : Seed m) : sampleAverage (fun z => -X z) ω = -sampleAverage X ω := by
    simp [sampleAverage]
  simp_rw [heq,integral_neg,neg_sub_neg] at hlow
  have inc : {ω | u ≤ |A ω|} ⊆ {ω | u ≤ A ω} ∪ {ω | u ≤ -A ω} := by
    intro ω h
    change u ≤ |A ω| at h
    rcases le_abs.mp h with h | h
    · exact Or.inl h
    · exact Or.inr h
  apply (measureReal_mono inc).trans ((measureReal_union_le _ _).trans _)
  dsimp only [A]
  simp only [neg_sub]
  linarith


/-- The scaled mark version applies to the separate weighted tangent blocks,
their angular integrals and the marked margin counts. -/
theorem three_energy {m : ℕ} (hm : 0 < m) (X : Atom → ℝ) (hX : Measurable X)
    (dom : ∀ z, |X z| ≤ 3*atomEnergy z) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (seedLaw m).real {ω | u ≤ |sampleAverage X ω - ∫ z, X z ∂atomLaw|} ≤
      2*exp (-(m:ℝ)*u^2/36864) := by
  let f (z : Atom) := (1/3:ℝ)*X z
  have hf : Measurable f := hX.const_mul _
  have d (z : Atom) : |f z| ≤ energy z := by
    have h := dom z
    simp only [f,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/3)]
    dsimp [energy]
    rw [Fin.sum_univ_three]
    change |X z| ≤ 3* (z 0^2 + z 1^2 + z 2^2) at h
    linarith
  have h := two_sided hm f hf d (u := u/3) (by positivity) (by linarith)
  have ha (ω : Seed m) : sampleAverage f ω = (1/3:ℝ)*sampleAverage X ω := by
    simp only [sampleAverage,f,← Finset.mul_sum]; ring
  simp_rw [ha] at h
  have me : (∫ z, f z ∂atomLaw) = (1/3:ℝ)*(∫ z, X z ∂atomLaw) := integral_const_mul _ _
  rw [me] at h
  have inc : {ω : Seed m | u ≤ |sampleAverage X ω - ∫ z, X z ∂atomLaw|} ⊆
      {ω : Seed m | u/3 ≤ |(1/3:ℝ)*sampleAverage X ω - (1/3:ℝ)*(∫ z, X z ∂atomLaw)|} := by
    intro ω hw
    change u/3 ≤ |(1/3:ℝ)*sampleAverage X ω - (1/3:ℝ)*(∫ z, X z ∂atomLaw)|
    rw [← mul_sub,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/3)]
    change u ≤ |sampleAverage X ω - ∫ z, X z ∂atomLaw| at hw
    linarith
  exact ((measureReal_mono inc).trans h).trans_eq (by congr 2; ring)

open CircleTangentDrift CircleGridSpectrum
/-- The entire finite collection of true grid, angular-row and margin tests
has an exponentially small failure probability under the original seed law. -/
theorem goodInit_exponential {m N : ℕ} [NeZero N] (hm : 0 < m) {τ ρ u : ℝ}
    (hτ : |τ| ≤ 2) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (seedLaw m).real {ω | ¬GoodInit τ ρ u (sampledMatrix τ) (fun _ : Fin N => CircleSpectrum.k0 τ) ω} ≤
      ((N+1:ℝ)^2+1) * (2*exp (-(m:ℝ)*u^2/36864)) := by
  simpa only [populationGram_sampled,funext (populationMeanRow_constant (N:=N) τ)] using
    goodInit_failure_of_tests (N:=N) hm hρ hρ' hu hu' (fun q => three_energy hm _
      (initTest_meas N τ ρ q) (initTest_cap N τ ρ hτ q) hu hu')

end CircleGaussianBernstein
