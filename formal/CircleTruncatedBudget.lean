module

public import CircleSpectralPathLength
import all CircleSpectralPathLength
import all CircleResidualSpectrum
import Mathlib.Tactic

/-! The discrete frozen-residual budget retains the smaller of the training
horizon and the geometric decay time in each dyadic shell. Its fourth norm
grows only as the fourth root of the number of updates. -/
public section
noncomputable section
namespace CircleTruncatedBudget
open Real Finset MeasureTheory CircleSpectralPathLength CircleResidualSpectrum CircleEscapeBridge
variable {N m : ℕ} [NeZero N]

def timeWeight (T d : ℕ) : ℝ := min T (shellConstant/((2:ℝ)^d)^2)⁻¹
def truncatedBudget (ho : Odd N) (m T : ℕ) (z : Seed m) : ℝ :=
  ∑ d ∈ range ((N+1).log2+1), timeWeight T d*
    blockNorm (bandSet (shell ho) d) (fun r => initialCoeff N m r z)

private theorem weight_nonneg (T d : ℕ) : 0 ≤ timeWeight T d :=
  le_min (Nat.cast_nonneg _) (inv_nonneg.mpr (div_nonneg shellConstant_pos.le (sq_nonneg _)))

theorem budget_nonneg (ho : Odd N) (m T : ℕ) (z : Seed m) :
    0 ≤ truncatedBudget ho m T z :=
  sum_nonneg fun d _ => mul_nonneg (weight_nonneg T d) (sqrt_nonneg _)

theorem budget_mem (ho : Odd N) (hm : 0<m) (T : ℕ) : MemLp (truncatedBudget ho m T) 4 (seedLaw m) :=
  memLp_finsetSum _ fun d _ => (block_mem (bandSet (shell ho) d) (initialCoeff N m)
    (fun r _ => (initialCoeff_uniform hm r).1)).const_mul _

theorem full_cap (ho : Odd N) (m T : ℕ) (z : Seed m) : truncatedBudget ho m T z ≤ seedBudget ho m z :=
  sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right (min_le_right ..) (sqrt_nonneg _)

private def shape (T d : ℕ) : ℝ := timeWeight T d * (sqrt ((2:ℝ)^d)/((2:ℝ)^d)^2)
private theorem shape_nonneg (T d : ℕ) : 0 ≤ shape T d :=
  mul_nonneg (weight_nonneg T d) (by positivity)

private theorem low (T d : ℕ) : shape T d ≤ shellConstant⁻¹*sqrt ((2:ℝ)^d) := by
  unfold shape
  apply (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)).trans_eq
  field_simp

private theorem high (T k j : ℕ) (cut : (T:ℝ) ≤ 4*((2:ℝ)^k)^2) :
    shape T (k+j) ≤ 4*sqrt ((2:ℝ)^k)*((1/2:ℝ)^j) := by
  let a := (2:ℝ)^k
  let b := (2:ℝ)^j
  have ap : 0<a := by dsimp [a]; positivity
  have bp : 1≤b := one_le_pow₀ (by norm_num)
  have bpos : 0<b := by linarith
  have sb : sqrt b ≤ b := sqrt_le_iff.mpr ⟨bpos.le,by nlinarith [mul_nonneg (sub_nonneg.mpr bp) bpos.le]⟩
  have inv : (1/2:ℝ)^j = 1/b := by simp [b]
  rw [shape,inv,pow_add,sqrt_mul (by positivity)]
  change timeWeight T (k+j)*(sqrt a*sqrt b/(a*b)^2) ≤ 4*sqrt a*(1/b)
  calc
    _ ≤ (4*a^2)*(sqrt a*b/(a*b)^2) := by
      apply mul_le_mul ((min_le_left ..).trans cut) _ (by positivity) (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left sb (sqrt_nonneg _)) (sq_nonneg _)
    _ = _ := by field_simp

private theorem geom_half (l : ℕ) : ∑ j ∈ range l, (1/2:ℝ)^j ≤ 2 := by
  have eq := geom_sum_mul_neg (1/2:ℝ) l
  norm_num at eq
  linarith [show (0:ℝ) ≤ (1/2:ℝ)^l by positivity]

private theorem sum_shape (T J : ℕ) :
    ∑ d ∈ range (J+1), shape T d ≤ (4*shellConstant⁻¹+8)*sqrt (sqrt (T+1:ℕ)) := by
  let k := (T+1).log2/2
  have lo : 2*k ≤ (T+1).log2 := by dsimp [k]; omega
  have hi : (T+1).log2+1 ≤ 2*k+2 := by dsimp [k]; omega
  have hbase : (2^k)^2 ≤ T+1 := by
    rw [← pow_mul,mul_comm k 2]
    exact (Nat.pow_le_pow_right (by decide) lo).trans (Nat.log2_self_le (Nat.succ_ne_zero _))
  have hcap : T ≤ 4*(2^k)^2 := by
    have h := (Nat.lt_log2_self (n:=T+1)).le.trans (Nat.pow_le_pow_right (by decide) hi)
    rw [pow_add,pow_mul] at h
    norm_num at h
    have eq : 4^k = (2^k)^2 := by rw [←pow_mul,mul_comm k 2,pow_mul]; norm_num
    rw [eq,mul_comm] at h
    omega
  have low_sum : ∑ d ∈ range k, shape T d ≤ 4*shellConstant⁻¹*sqrt ((2:ℝ)^k) := by
    calc
      _ ≤ ∑ d ∈ range (k+1), shape T d := sum_le_sum_of_subset_of_nonneg
        (range_mono (by omega)) (fun i _ _ => shape_nonneg T i)
      _ ≤ _ := (sum_le_sum fun d _ => low T d).trans (by
        rw [←Finset.mul_sum]; nlinarith [mul_le_mul_of_nonneg_left (sqrt_geom k) (inv_nonneg.mpr shellConstant_pos.le)])
  have high_sum : ∑ j ∈ range (J+1), shape T (k+j) ≤ 8*sqrt ((2:ℝ)^k) := by
    apply (sum_le_sum fun j _ => high T k j (by exact_mod_cast hcap)).trans
    rw [←Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left (geom_half (J+1)) (show 0≤4*sqrt ((2:ℝ)^k) by positivity)]
  have cutoff : (2:ℝ)^k ≤ sqrt (T+1:ℕ) := (le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast hbase)
  calc
    _ ≤ ∑ d ∈ range (k+(J+1)), shape T d := sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      (fun i _ _ => shape_nonneg T i)
    _ ≤ (4*shellConstant⁻¹+8)*sqrt ((2:ℝ)^k) := by rw [sum_range_add]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_le_sqrt cutoff) (by have := shellConstant_pos; positivity)

def truncConstant : ℝ := 4*modeConstant*sqrt 5*(4*shellConstant⁻¹+8)

theorem budget_lp4 (ho : Odd N) (hm : 0<m) (T : ℕ) :
    lpNorm (truncatedBudget ho m T) 4 (seedLaw m) ≤ truncConstant*sqrt (sqrt (T+1:ℕ)) := by
  let S := range ((N+1).log2+1)
  let block := fun (d : ℕ) (z : Seed m) => blockNorm (bandSet (shell ho) d) (fun r => initialCoeff N m r z)
  let X := fun (d : ℕ) => (timeWeight T d) • block d
  have hX (d : ℕ) : MemLp (X d) 4 (seedLaw m) := (block_mem _ _ (fun r _ => (initialCoeff_uniform hm r).1)).const_smul _
  have hh : truncatedBudget ho m T = ∑ d ∈ S, X d := by funext; simp [truncatedBudget,S,X,block,Finset.sum_apply]
  have cc := modeConstant_nonneg
  rw [hh]
  apply (lpNorm_sum_le (fun d _ => hX d) (by norm_num)).trans
  calc
    _ ≤ ∑ d ∈ S, (4*modeConstant*sqrt 5)*shape T d := by
      apply sum_le_sum
      intro d _
      dsimp only [X]
      rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg T d)]
      have bnd := block_lp4 (bandSet (shell ho) d) (initialCoeff N m) (fun r _ => (initialCoeff_uniform hm r).1)
        (4*modeConstant/((2:ℝ)^d)^2) (by positivity) (fun r hr => (mem_filter.mp hr).2 ▸ mode_shell_cap hm ho r)
      have hcard := sqrt_le_sqrt (shell_count ho d)
      rw [sqrt_mul (by norm_num : (0:ℝ)≤5)] at hcard
      have h := mul_le_mul_of_nonneg_left (bnd.trans (mul_le_mul_of_nonneg_right hcard (by positivity))) (weight_nonneg T d)
      exact h.trans_eq (by unfold shape; ring)
    _ ≤ _ := by
      rw [←Finset.mul_sum,truncConstant,show 4*modeConstant*sqrt 5*(4*shellConstant⁻¹+8)*sqrt (sqrt (T+1:ℕ)) = _ by rw [mul_assoc (4*modeConstant*sqrt 5)]]
      exact mul_le_mul_of_nonneg_left (sum_shape T (N+1).log2) (by positivity)


/-- Integrated frozen flow on the finite interval, using the same Gaussian
seed and the same truncated shell weights as discrete training. -/
theorem flow_area (ho : Odd N) {τ : ℝ} (ht : 1/2≤τ) (hu : τ≤2) (T : ℕ) (z : Seed m) :
    (∫ s in (0:ℝ)..(T:ℝ), ‖referencePath τ (rawResidual N m z) s‖) ≤ truncatedBudget ho m T z := by
  let J := (N+1).log2
  let rate (d : ℕ) := shellConstant/((2:ℝ)^d)^2
  let a := normalizedCoeff (rawResidual N m z)
  let B (d : ℕ) := blockNorm (bandSet (shell ho) d) a
  have rp (d : ℕ) : 0 < rate d := div_pos shellConstant_pos (by positivity)
  have hc : Continuous (referencePath τ (rawResidual N m z)) := continuous_iff_continuousAt.mpr
    fun s => (referencePath_deriv τ (by linarith) hu _ s).continuousAt
  have hi (d : ℕ) : Continuous (fun s : ℝ => exp (-rate d*s)*B d) := by fun_prop
  have tpos := Nat.cast_nonneg (α:=ℝ) T
  calc
    _ ≤ ∫ s in (0:ℝ)..(T:ℝ), ∑ d ∈ range (J+1), exp (-rate d*s)*B d := by
      apply intervalIntegral.integral_mono_on tpos (hc.norm.intervalIntegrable _ _)
        ((continuous_finsetSum _ fun d _ => hi d).intervalIntegrable _ _)
      exact fun s hs => (norm_referencePath τ _ s).trans
        (damp_block _ _ _ hs.1 J (shell ho) (shell_le ho) rate (shell_eigen ho ht hu))
    _ ≤ _ := by
      rw [intervalIntegral.integral_finsetSum (fun d _ => (hi d).intervalIntegrable _ _)]
      unfold truncatedBudget
      apply sum_le_sum
      intro d _
      rw [intervalIntegral.integral_mul_const]
      have cut : (∫ s in (0:ℝ)..(T:ℝ), exp (-rate d*s)) ≤ T := by
        calc
          _ ≤ ∫ _s in (0:ℝ)..(T:ℝ), (1:ℝ) := by
            apply intervalIntegral.integral_mono_on tpos ((show Continuous (fun u : ℝ => exp (-rate d*u)) by fun_prop).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
            exact fun s hs => exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (rp d).le) hs.1)
          _ = _ := by simp
      have same : a = fun r => initialCoeff N m r z := funext fun r => normalizedCoeff_raw _ r z
      simpa only [B,same,timeWeight,rate] using mul_le_mul_of_nonneg_right (le_min cut (exp_area (T:=T) (rp d)))
        (show 0≤B d from sqrt_nonneg _)

end CircleTruncatedBudget
