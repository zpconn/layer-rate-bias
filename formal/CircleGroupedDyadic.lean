module

public import CircleGroupedResidual
public import CircleDiscreteBudget
import all CircleGroupedResidual
import all CircleDiscreteBudget
import all CircleSpectralPathLength
import all CircleResidualSpectrum
import all CircleGridSpectrum
import Mathlib.Tactic

/-! The exact second-moment grouped design grows at most as the square root
of the odd circle grid size. -/
@[expose] public section
noncomputable section
namespace CircleGroupedDyadic
open Real MeasureTheory Finset CircleEscapeBridge CircleGroupedResidual
  CircleSpectralPathLength CircleResidualSpectrum CircleGridSpectrum CircleDiscreteBudget
variable {N : ℕ} [NeZero N]


theorem cost_le (ho : Odd N) :
    groupCost N (N+1).log2 (shell ho) rate ≤ budgetConstant*√(N:ℝ) := by
  let J := (N+1).log2
  let C := 4*modeConstant
  have cp : 0≤C := mul_nonneg (by norm_num) modeConstant_nonneg
  have sp := shellConstant_pos
  have each (d : ℕ) :
      (rate d)⁻¹ * √(∑ r ∈ bandSet (shell ho) d,(eigen 0 r+‖normalizedCoeff (CircleFlowPath.circleLabel N) r‖^2)) ≤
        (C/shellConstant*√5)*√((2:ℝ)^d) := by
    let B (z : Seed 1) := blockNorm (bandSet (shell ho) d) (fun r => initialCoeff N 1 r z)
    have ha (r : ZMod N) := (initialCoeff_uniform (m:=1) (by decide) r).1
    have hb : MemLp B 4 (seedLaw 1) := block_mem _ _ (fun r _ => ha r)
    have mono : lpNorm B 2 (seedLaw 1) ≤ lpNorm B 4 (seedLaw 1) := by
      rw [←toReal_eLpNorm,←toReal_eLpNorm];exact ENNReal.toReal_mono hb.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    rw [←block_lp2 (m:=1) (by decide)]
    have h4 := block_lp4 (bandSet (shell ho) d) (initialCoeff N 1) (fun r _ => ha r)
      (C/((2:ℝ)^d)^2) (by positivity) (fun r hr => (Finset.mem_filter.mp hr).2 ▸ mode_shell_cap (m:=1) (by decide) ho r)
    have hd := sqrt_le_sqrt (shell_count ho d)
    rw [sqrt_mul (by norm_num : (0:ℝ)≤5)] at hd
    calc
      _ ≤ (rate d)⁻¹*(√((bandSet (shell ho) d).card:ℝ)*(C/((2:ℝ)^d)^2)) :=
        mul_le_mul_of_nonneg_left (mono.trans h4) (inv_nonneg.mpr (rate_pos _).le)
      _ = C/shellConstant*√((bandSet (shell ho) d).card:ℝ) := by unfold rate;field_simp
      _ ≤ _ := by rw [mul_assoc];gcongr
  calc
    _ ≤ ∑ d ∈ range (J+1),(C/shellConstant*√5)*√((2:ℝ)^d) := sum_le_sum (fun d _ => each d)
    _ ≤ 4*(C/shellConstant)*√5*√((2:ℝ)^J) := by
      rw [←Finset.mul_sum]
      nlinarith only [mul_le_mul_of_nonneg_left (sqrt_geom J) (by positivity : 0≤C/shellConstant*√5)]
    _ ≤ _ := by
      have hn := NeZero.pos N
      have hk : (2:ℝ)^J≤2*(N:ℝ) := by
        exact_mod_cast (Nat.log2_self_le (Nat.succ_ne_zero N)).trans (show N+1≤2*N by omega)
      have h := sqrt_le_sqrt hk
      rw [sqrt_mul (by norm_num : (0:ℝ)≤2)] at h
      have hs := mul_le_mul_of_nonneg_left h (by positivity : 0≤4*(C/shellConstant)*√5)
      dsimp [C,budgetConstant] at hs ⊢
      convert hs using 1;ring

/-- The constant teacher component supplies a uniform lower bound even on the
one-point odd grid, where the teacher modes coincide. -/
theorem one_le_cost (ho : Odd N) :
    1≤groupCost N (N+1).log2 (shell ho) rate := by
  let S := bandSet (shell ho)
  let M (r : ZMod N) := eigen 0 r+‖normalizedCoeff (CircleFlowPath.circleLabel N) r‖^2
  have mp (r : ZMod N) : 0≤M r := by
    rw [show M r = _ from (residual_mode_second (m:=1) (by decide) r).symm]
    exact integral_nonneg fun z => sq_nonneg _
  have m0 : 1≤M 0 := by
    have g := coeff_le_eigen (k:=(0:ℤ)) (r:=(0:ZMod N)) (by norm_num : 0≤(0:ℝ)) (by norm_num) (by simp)
    have ep := (tangentCoeff_nonneg (by norm_num : 0≤(0:ℝ)) 0).trans g
    unfold M;rw [normalized_teacher]
    by_cases h : (1:ZMod N)=0
    · have neg : (-1:ZMod N)=0 := by rw [←neg_eq_zero] at h;simpa using h
      simp only [ite_true,ite_eq_left h,ite_eq_left neg];norm_num;linarith
    · have neg : (-1:ZMod N)≠0 := neg_ne_zero.mpr h
      simp only [ite_true,ite_eq_right h,ite_eq_right neg];simp;exact ep
  let d := shell ho (0:ZMod N)
  have mem : (0:ZMod N)∈S d := Finset.mem_filter.mpr ⟨mem_univ _,rfl⟩
  have ge := m0.trans (single_le_sum (s:=S d) (f:=M) (fun r _ => mp r) mem)
  have sq : 1≤√(∑ r ∈ S d,M r) := one_le_sqrt.mpr ge
  have invge : 1≤(rate d)⁻¹ := (one_le_inv₀ (rate_pos d)).mpr (rate_le_one d)
  have front : 1≤(rate d)⁻¹*√(∑ r ∈ S d,M r) := (one_mul (1:ℝ)).symm.le.trans (mul_le_mul invge sq zero_le_one (inv_pos.mpr (rate_pos _)).le)
  exact front.trans (single_le_sum (s:=range ((N+1).log2+1))
    (f:=fun k => (rate k)⁻¹*√(∑ r ∈ S k,M r)) (fun k _ => mul_nonneg (inv_pos.mpr (rate_pos _)).le (sqrt_nonneg _))
    (mem_range.mpr (Nat.lt_succ_of_le (shell_le ho 0))))

theorem cost_pos (ho : Odd N) :
    0<groupCost N (N+1).log2 (shell ho) rate := zero_lt_one.trans_le (one_le_cost ho)

end CircleGroupedDyadic
