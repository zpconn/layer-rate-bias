module

public import CircleSynchronizedWidth
public import CircleFlowTracking
import Mathlib.Analysis.Complex.ExponentialBounds
import all CircleSynchronizedWidth
import all CircleFlowTracking
import Mathlib.Tactic

/-! Comparison between the probability cost of the perturbation box and the
cubic growth of the paired Euler contrast, including the exact common cap. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDCost
open Real Filter Topology CircleSynchronizedWidth

/-- The clock at width N^32 eventually exceeds every fixed multiple of log N. -/
theorem horizon_lower (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c*log N ≤ (CircleFlowTracking.horizon N:ℝ) := by
  filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop c,
    eventually_ge_atTop 1] with N hc hn
  have n1 : (1:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have p3 : (N:ℝ)≤(N:ℝ)^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤3)
  have r := Real.one_le_sqrt.mpr (by linarith : (1:ℝ)≤12*N)
  have big := p3.trans (le_mul_of_one_le_left (by positivity : 0≤(N:ℝ)^3)
    (by linarith : 1≤2*Real.sqrt (12*N)))
  have factor : c ≤ 2*π^2*(N:ℝ)^2 := by
    apply hc.trans
    have h : 1≤2*π^2 := by nlinarith [pi_gt_three]
    exact (by nlinarith [mul_nonneg (sub_nonneg.mpr n1) np.le] : (N:ℝ)≤(N:ℝ)^2).trans
      (le_mul_of_one_le_left (sq_nonneg _) h)
  apply (mul_le_mul factor (Real.log_le_log np big) (Real.log_nonneg n1) (by positivity)).trans
  exact Nat.le_ceil (2*π^2*(N:ℝ)^2 * log (2*sqrt (12*N)*(N:ℝ)^3))

def size (N m T : ℕ) := (m:ℝ)*((T:ℝ)+log N+1)

theorem cost_cap (N m T : ℕ) (hN : 0<N) (R : ℝ) :
    cost N m (2*T) (R/2) ≤
      (3*(|(2*(R/2)+1)^2/2+log (8*sqrt (2*π))|+2*log 512+1))*size N m T := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  let C := (2*(R/2)+1)^2/2+log (8*sqrt (2*π))
  have tc : 0 ≤ (T:ℝ) := Nat.cast_nonneg T
  have ln := log_nonneg hn
  have lg : 0 ≤ log 512 := log_nonneg (by norm_num)
  unfold cost size
  rw [log_mul (by positivity) np.ne']
  push_cast
  let B := |C|+2*log 512+1
  have hB : 1≤B := by dsimp [B]; linarith [abs_nonneg C]
  have hT := mul_le_mul_of_nonneg_right (by dsimp [B];linarith [abs_nonneg C] : 2*log 512≤B) tc
  have hl := le_mul_of_one_le_left ln hB
  have hC : C≤B := by dsimp [B]; linarith [le_abs_self C]
  have bound : C+log N+2*T*log 512≤B*((T:ℝ)+log N+1) := by linarith only [hT,hl,hC]
  convert mul_le_mul_of_nonneg_left bound (by positivity : 0≤3*(m:ℝ)) using 1 <;> dsimp [C,B] <;> ring

/-- A vanishing ratio of width times box log-cost to cubic growth is sufficient. -/
theorem exponential (N m T : ℕ → ℕ) {a : ℝ} (ha : 0<a) (R : ℝ)
    (grow : Tendsto T atTop atTop) (pos : ∀ᶠ j in atTop, 0<N j)
    (small : Tendsto (fun j => size (N j) (m j) (T j)/(3:ℝ)^(T j)) atTop (𝓝 0)) :
    Tendsto (fun j => exp (a*(3:ℝ)^(T j)-cost (N j) (m j) (2*T j) (R/2))) atTop atTop := by
  let C := 3*(|(2*(R/2)+1)^2/2+log (8*sqrt (2*π))|+2*log 512+1)
  have h := (small.const_mul C).eventually_le_const (show C*0<a/2 by linarith)
  have hp := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3)).comp grow
  apply tendsto_atTop_mono' atTop _ (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (by linarith : 0<a/2) hp))
  filter_upwards [h,pos] with j hj hn
  have bound := cost_cap (N j) (m j) (T j) hn R
  have hj' : C*size (N j) (m j) (T j) ≤ a/2*3^(T j) := by
    apply (div_le_iff₀ (by positivity : 0<(3:ℝ)^(T j))).mp
    simpa only [mul_div_assoc] using hj
  change exp (a/2*(3:ℝ)^(T j)) ≤ exp _
  apply exp_le_exp.mpr
  change _ ≤ C*_ at bound
  linarith only [hj',bound]

/-- Width N^32 satisfies the rare-event criterion whenever T ≥ 60 log N.
No upper bound on the number of steps is needed. -/
theorem polynomial (N T : ℕ → ℕ) (gn : Tendsto N atTop atTop)
    (sched : ∀ᶠ j in atTop, 60*log (N j) ≤ (T j:ℝ)) :
    Tendsto T atTop atTop ∧
    Tendsto (fun j => size (N j) (N j^32) (T j)/(3:ℝ)^(T j)) atTop (𝓝 0) := by
  have hg := tendsto_atTop_mono' atTop sched (Tendsto.const_mul_atTop (by norm_num : (0:ℝ)<60)
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp gn)))
  have gt : Tendsto T atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [hg.eventually_ge_atTop (n:ℝ)] with j hj
    exact_mod_cast hj
  refine ⟨gt,?_⟩
  let c : ℝ := 32/60
  have hc : c<log 3 := by dsimp [c];linarith [Real.log_three_gt_d9]
  have lim := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (log 3-c) (sub_pos.mpr hc)).comp hg).const_mul 3
  apply squeeze_zero' _ _ (by simpa [Function.comp_def] using lim :
    Tendsto (fun j => 3*((T j:ℝ)*exp (-(log 3-c)*(T j:ℝ)))) atTop (𝓝 0))
  · filter_upwards [gn.eventually_ge_atTop 1] with j hn
    have hN : (1:ℝ)≤N j := by exact_mod_cast hn
    have := log_nonneg hN
    unfold size
    positivity
  · filter_upwards [gn.eventually_ge_atTop 1,gt.eventually_ge_atTop 1,sched] with j n t clock
    have hN : (1:ℝ)≤N j := by exact_mod_cast n
    have ht : (1:ℝ)≤T j := by exact_mod_cast t
    have width : (N j:ℝ)^32 ≤ exp (c*(T j:ℝ)) := by
      apply (log_le_iff_le_exp (by positivity)).mp
      rw [log_pow]
      dsimp [c]
      linarith only [clock]
    have fac : (T j:ℝ)+log (N j)+1 ≤ 3*(T j:ℝ) := by linarith only [ht,clock]
    have ident : exp (c*(T j:ℝ)) = exp (-(log 3-c)*(T j:ℝ))*(3:ℝ)^(T j) := by
      rw [show (3:ℝ)^(T j) = exp ((T j:ℝ)*log 3) by rw [exp_nat_mul,exp_log (by norm_num)],←exp_add]
      congr 1;ring
    rw [div_le_iff₀ (by positivity),size,Nat.cast_pow]
    have np : 0≤(T j:ℝ)+log (N j)+1 := by linarith [log_nonneg hN]
    exact (mul_le_mul width fac np (exp_pos _).le).trans_eq (by rw [ident];ring)

/-- The ratio criterion in the paper implies both growth of the training clock
and the reciprocal small-cost hypothesis. -/
theorem of_ratio (N m T : ℕ→ℕ)
    (valid : ∀ᶠ j in atTop, 0<N j ∧ 0<m j)
    (ratio : Tendsto (fun j => (3:ℝ)^(T j)/size (N j) (m j) (T j)) atTop atTop) :
    Tendsto T atTop atTop ∧
    Tendsto (fun j => size (N j) (m j) (T j)/(3:ℝ)^(T j)) atTop (𝓝 0) := by
  have inv := tendsto_inv_atTop_zero.comp ratio
  refine ⟨?_,by simpa only [Function.comp_def,inv_div] using inv⟩
  have bigger : Tendsto (fun j => (3:ℝ)^(T j)) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ratio
    filter_upwards [valid] with j v
    have hn : (1:ℝ)≤N j := by exact_mod_cast v.1
    have hm : (1:ℝ)≤m j := by exact_mod_cast v.2
    have sum : 1≤(T j:ℝ)+log (N j)+1 := by linarith [log_nonneg hn,Nat.cast_nonneg (α:=ℝ) (T j)]
    exact div_le_self (by positivity) (one_le_mul_of_one_le_of_one_le hm sum)
  apply tendsto_atTop.2
  intro n
  filter_upwards [bigger.eventually_ge_atTop ((3:ℝ)^n)] with j h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<3)).mp h

end CirclePairedGDCost
