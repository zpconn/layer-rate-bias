module

public import CircleFlowTracking
import all CircleFlowTracking
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The exact benchmark training-clock substitutions on the three- and five-point grids. -/
public section
noncomputable section
namespace CircleFiniteHorizons
open Real CircleFlowTracking
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

private theorem exp_upper {s a : ℝ} (hs : 0≤s) (h1 : s≤1)
    (h : (∑ k ∈ Finset.range 12,s^k / k.factorial)+s^12*13/((12:ℕ).factorial*12)≤a) :
    exp (8*s)≤a^8 := by
  rw [show (8:ℝ)=((8:ℕ):ℝ) by norm_num,exp_nat_mul]
  exact pow_le_pow_left₀ (exp_pos _).le
    ((exp_bound' hs h1 (n:=12) (by decide)).trans (by convert h using 1; norm_num)) _

private theorem exp_lower {s a : ℝ} (hs : 0≤s) (ha : 0≤a)
    (h : a≤∑ k ∈ Finset.range 12,s^k / k.factorial) :
    a^8≤exp (8*s) := by
  rw [show (8:ℝ)=((8:ℕ):ℝ) by norm_num,exp_nat_mul]
  exact pow_le_pow_left₀ ha (h.trans (sum_le_exp_of_nonneg hs _)) _

private theorem log_three : 5.78074≤log 324 ∧ log 324≤5.78075 := by
  constructor
  · apply (le_log_iff_exp_le (by norm_num : (0:ℝ)<324)).mpr
    rw [show (5.78074:ℝ)=8*0.7225925 by norm_num]
    exact (exp_upper (a:=2.0597663) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ,Nat.factorial])).trans (by norm_num)
  · apply (log_le_iff_le_exp (by norm_num : (0:ℝ)<324)).mpr
    rw [show (5.78075:ℝ)=8*0.72259375 by norm_num]
    exact (by norm_num : (324:ℝ)≤2.0597687^8).trans (exp_lower (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ,Nat.factorial]))

private theorem log_five : 7.56863≤log (250*sqrt 60) ∧ log (250*sqrt 60)≤7.56864 := by
  constructor
  · apply (le_log_iff_exp_le (by positivity)).mpr
    rw [show (7.56863:ℝ)=8*0.94607875 by norm_num]
    apply (exp_upper (a:=2.5755904) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ,Nat.factorial])).trans
    have hs : (1936.49:ℝ)/250≤sqrt 60 := Real.le_sqrt_of_sq_le (by norm_num)
    linarith [show (2.5755904:ℝ)^8≤1936.49 by norm_num]
  · apply (log_le_iff_le_exp (by positivity)).mpr
    rw [show (7.56864:ℝ)=8*0.94608 by norm_num]
    apply le_trans _ (exp_lower (a:=2.5755934) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ,Nat.factorial]))
    have hs : sqrt 60≤(1936.5:ℝ)/250 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    linarith [show (1936.5:ℝ)≤2.5755934^8 by norm_num]

private theorem interval {x a b : ℝ} (ha : 0≤a) (hx : a≤x ∧ x≤b) :
    3.141592^2*a≤π^2*x ∧ π^2*x≤3.141593^2*b := by
  have hl : (3.141592:ℝ)≤π := by linarith only [pi_gt_d20]
  have hu : π≤3.141593 := by linarith only [pi_lt_d20]
  exact ⟨mul_le_mul (pow_le_pow_left₀ (by norm_num) hl 2) hx.1 ha (sq_nonneg _),
    mul_le_mul (pow_le_pow_left₀ pi_pos.le hu 2) hx.2 (ha.trans hx.1) (sq_nonneg _)⟩

theorem three : horizon 3=1027 := by
  have h := interval (by norm_num) log_three
  unfold horizon
  apply (Nat.ceil_eq_iff (by decide)).mpr
  norm_num [show sqrt (12*3)=6 by norm_num]
  constructor <;> linarith only [h.1,h.2]

theorem five : horizon 5=3735 := by
  have h := interval (by norm_num) log_five
  unfold horizon
  apply (Nat.ceil_eq_iff (by decide)).mpr
  norm_num
  rw [show (2*sqrt 60*125:ℝ)=250*sqrt 60 by ring]
  constructor <;> linarith only [h.1,h.2]

end CircleFiniteHorizons
