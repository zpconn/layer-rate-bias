module

public import CircleCapMoments
import all CircleCapInduction
import all CircleEscapeBridge
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! Uniform moments of the normalized initial parameter energy, for every integer
exponent up to the width. One exponential tilt suffices for all these powers. -/
@[expose] public section
noncomputable section
namespace CircleWidthGaussianEnergy
open CircleCapInduction CircleCapMoments CircleEscapeBridge MeasureTheory ProbabilityTheory Real

private theorem scalar_mgf :
    (∫ x : ℝ, exp (x^2/7) ∂gaussianReal 0 1) = sqrt (7/5) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have row (x : ℝ) : gaussianPDFReal 0 1 x • exp (x^2/7) =
      (1/sqrt (2*π))*exp (-(5/14:ℝ)*x^2) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,smul_eq_mul,one_div]
    rw [mul_assoc,←Real.exp_add]; congr 2; ring
  simp_rw [row]
  rw [integral_const_mul,integral_gaussian]
  apply (sq_eq_sq₀ (by positivity) (sqrt_nonneg _)).mp
  rw [mul_pow,div_pow,sq_sqrt (by positivity),sq_sqrt (by positivity),sq_sqrt (by norm_num)]
  field_simp; ring

private theorem cubic_bound : sqrt (7/5:ℝ)^3 ≤ exp (5/7:ℝ) := by
  have h : (sqrt (7/5:ℝ)^3)^2 ≤ (12/7:ℝ)^2 := by rw [←pow_mul,pow_mul (sqrt _) 2 3,sq_sqrt (by norm_num)]; norm_num
  have le := (sq_le_sq₀ (by positivity) (by norm_num)).mp h
  linarith [add_one_le_exp (5/7:ℝ)]

private def S {m : ℕ} (ω : Seed m) := 4+2*energy (initial ω)
private theorem S_nonneg {m : ℕ} (ω : Seed m) : 0≤ S ω := by
  unfold S energy; rw [initial_energy_coordinates]; positivity
private theorem S_meas (m : ℕ) : Measurable (S (m:=m)) := by
  unfold S energy; simp_rw [initial_energy_coordinates]; fun_prop

private def tilt {m : ℕ} (ω : Seed m) := exp ((m:ℝ)*(S ω/14-1))

private theorem tilt_expectation {m : ℕ} (hm : 0<m) :
    Integrable (tilt (m:=m)) (seedLaw m) ∧ (∫ ω, tilt ω ∂seedLaw m)≤1 := by
  have mp : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  let P (ω : Seed m) := ∏ i, exp ((ω i)^2/7)
  have moment : (∫ ω, P ω ∂seedLaw m) = (sqrt (7/5))^(m*3) := by
    unfold P seedLaw
    rw [integral_fintype_prod_eq_pow (ι:=Fin m×Fin 3) (μ:=gaussianReal 0 1) (fun x => exp (x^2/7)),scalar_mgf]
    simp
  have int : Integrable P (seedLaw m) := .of_integral_ne_zero (moment.trans_ne (by positivity))
  have eq : tilt (m:=m) = fun ω => (exp (-(5/7:ℝ)))^m*P ω := by
    funext ω
    unfold tilt S energy P
    rw [initial_energy_coordinates,←exp_nat_mul,←exp_sum,←Finset.sum_div,←exp_add]
    congr 1; field_simp; ring
  rw [eq]
  refine ⟨int.const_mul _,?_⟩
  rw [integral_const_mul,moment,Nat.mul_comm m 3,pow_mul,←mul_pow]
  apply pow_le_one₀ (by positivity)
  rw [exp_neg,inv_mul_le_one₀ (exp_pos _)]
  exact cubic_bound

private theorem power_majorant {m s : ℕ} (hm : 0<m) (hs : s≤m) (ω : Seed m) :
    (S ω)^s ≤ (14:ℝ)^s*((1-(s:ℝ)/m)+(s:ℝ)/m*tilt ω) := by
  let z := S ω/14
  let p := (s:ℝ)/(m:ℝ)
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have pp : 0≤p := by unfold p; positivity
  have p1 : p≤1 := (div_le_one mp).mpr (by exact_mod_cast hs)
  have e := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ ((m:ℝ)*(z-1)))
    (sub_nonneg.mpr p1) pp (show (1-p)+p=1 by ring)
  simp only [smul_eq_mul,mul_zero,zero_add,exp_zero,mul_one] at e
  have scale : p*((m:ℝ)*(z-1))=s*(z-1) := by dsimp [p]; field_simp
  rw [scale] at e
  have v : z^s ≤ exp ((s:ℝ)*(z-1)) := by
    rw [exp_nat_mul]; apply pow_le_pow_left₀ (div_nonneg (S_nonneg _) (by norm_num))
    change z≤exp (z-1)
    linarith [add_one_le_exp (z-1)]
  have h := mul_le_mul_of_nonneg_left (v.trans e) (by positivity : 0≤(14:ℝ)^s)
  convert h using 1
  · rw [←mul_pow]; congr 1; dsimp [z]; ring
  · rfl

private theorem moments {m s : ℕ} (hs : s≤m) :
    Integrable (fun ω : Seed m => (S ω)^s) (seedLaw m) ∧
      (∫ ω, (S ω)^s ∂seedLaw m)≤(14:ℝ)^s := by
  by_cases hm : m=0
  · subst m
    obtain rfl : s=0 := by omega
    simp
  have mp : 0<m := Nat.pos_of_ne_zero hm
  let p := (s:ℝ)/(m:ℝ)
  have pp : 0≤p := by unfold p; positivity
  have h := tilt_expectation mp
  have bound := fun ω => power_majorant mp hs ω
  have upper := (integrable_const (μ:=seedLaw m) (1-p)).add (h.1.const_mul p)
  have int := upper.const_mul ((14:ℝ)^s)
  refine ⟨int.mono' ((S_meas m).pow_const s).aestronglyMeasurable (ae_of_all _ (fun ω => ?_)),?_⟩
  · change |S ω^s| ≤ _; rw [abs_of_nonneg (pow_nonneg (S_nonneg _) _)]; exact bound ω
  calc _ ≤ ∫ ω, (14:ℝ)^s*((1-p)+p*tilt ω) ∂seedLaw m :=
         integral_mono_of_nonneg (ae_of_all _ fun _ => pow_nonneg (S_nonneg _) _) int (ae_of_all _ bound)
       _ ≤ _ := by
         rw [integral_const_mul,integral_add (integrable_const _) (h.1.const_mul p),integral_const_mul,integral_const]
         simp only [probReal_univ,one_smul]
         apply mul_le_of_le_one_right (by positivity)
         linarith [mul_le_mul_of_nonneg_left h.2 pp]

/-- Uniform in the width and in every integer power through the width, including `4*3^T`. -/
theorem initial_energy_power (m s : ℕ) (hs : s≤m) :
    ∫ ω, (4+2*energy (initial ω))^s ∂seedLaw m ≤ (14:ℝ)^s := (moments hs).2

theorem initial_energy_power_integrable (m s : ℕ) (hs : s≤m) :
    Integrable (fun ω : Seed m => (4+2*energy (initial ω))^s) (seedLaw m) := (moments hs).1

end CircleWidthGaussianEnergy
