module

public import CircleReciprocalEscape
public import CircleReciprocalFinite
import all CircleFlowTracking
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The exact Gaussian moment cutoff for the reciprocal curvature step. -/

public section
noncomputable section
namespace CircleReciprocalCriterion

open MeasureTheory CircleEscapeBridge CircleCapMoments CircleReciprocalEscape

private theorem cutoff (m t : ℕ) (p : ℝ) (high : 3*(m:ℝ)≤(4*(3:ℝ)^t-2)*p) :
    ((3*m:ℕ):ℝ)≤((2*powerIndex t:ℕ):ℝ)*p := by
  have h : (powerIndex t:ℝ)+1=2*(3:ℝ)^t := by exact_mod_cast powerIndex_eq t
  push_cast
  rwa [show 2*(powerIndex t:ℝ)=4*(3:ℝ)^t-2 by linarith]

/-- The full positive-order criterion for the population prediction of the
actual network with the frozen seed-dependent reciprocal curvature rate. -/
theorem moment_iff (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    (c p : ℝ) (hc : 0<c) (hp : 0<p) :
    Integrable (fun z => |CircleReciprocal.Y N m (t+1) c z|^p) (seedLaw m) ↔
      (4*(3:ℝ)^t-2)*p < 3*(m:ℝ) := by
  constructor
  · intro yes
    by_contra! high
    exact no_moment N m t hn odd hm c p hc hp (cutoff m t p high) yes
  · exact CircleReciprocalFinite.moment N m t hn odd hm c p hc hp

/-- Subtracting the infinite-time reference evaluated on the same seed gives
the identical cutoff for every real order, including those below one. -/
theorem paired_moment_iff (N m t : ℕ) (hn : 3≤N) (odd : Odd N) (hm : 0<m)
    (c p b : ℝ) (hc : 0<c) (hp : 0<p) :
    Integrable (fun z => |CircleReciprocal.Y N m (t+1) c z-reference N m b z|^p) (seedLaw m) ↔
      (4*(3:ℝ)^t-2)*p < 3*(m:ℝ) := by
  constructor
  · intro yes
    by_contra! high
    exact no_paired_moment N m t hn odd hm c p hc hp (cutoff m t p high) b yes
  · exact CircleReciprocalFinite.paired_moment N m t hn odd hm c p b hc hp

/-- At the specified long horizon, both MSEs diverge for every width
bounded by a polynomial; the first absolute output moment already diverges. -/
theorem polynomial_horizon (N m k : ℕ) (hn : 3≤N) (hk : k+2≤N) (odd : Odd N)
    (hm : 0<m) (width : m≤N^k) (c b h : ℝ) (hc : 0<c) :
    ¬Integrable (fun z => |CircleReciprocal.Y N m (CircleFlowTracking.horizon N) c z|) (seedLaw m) ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N m (CircleFlowTracking.horizon N) c z-reference N m b z)^2) ∂seedLaw m)=⊤ ∧
    (∫⁻ z, ENNReal.ofReal ((CircleReciprocal.Y N m (CircleFlowTracking.horizon N) c z-h)^2) ∂seedLaw m)=⊤ := by
  have n3 : (3:ℝ)≤N := by exact_mod_cast hn
  have n1 : (1:ℝ)≤N := by linarith
  have sq : 1≤Real.sqrt (12*N) := Real.one_le_sqrt.mpr (by linarith)
  have cu : (N:ℝ)≤(N:ℝ)^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤3)
  have v : (3:ℝ) ≤ 2*Real.sqrt (12*N)*(N:ℝ)^3 := (n3.trans cu).trans
    (le_mul_of_one_le_left (by positivity : 0≤(N:ℝ)^3) (by linarith))
  have lg : 1≤Real.log (2*Real.sqrt (12*N)*(N:ℝ)^3) :=
    (by linarith [Real.log_three_gt_d9] : (1:ℝ)≤Real.log 3).trans (Real.log_le_log (by norm_num) v)
  have factor : 1≤2*Real.pi^2 := by nlinarith [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have big : N*(k+2)≤CircleFlowTracking.horizon N := by
    have hkr : (k:ℝ)+2≤N := by exact_mod_cast hk
    have a : (N:ℝ)*((k:ℝ)+2) ≤ (N:ℝ)^2 := by rw [pow_two];gcongr
    have b := le_mul_of_one_le_left (sq_nonneg (N:ℝ)) factor
    have d := le_mul_of_one_le_right (show 0≤2*Real.pi^2*(N:ℝ)^2 by positivity) lg
    have e := ((a.trans b).trans d).trans (Nat.le_ceil (2*Real.pi^2*(N:ℝ)^2*Real.log (2*Real.sqrt (12*N)*(N:ℝ)^3)))
    dsimp [CircleFlowTracking.horizon]
    exact_mod_cast e
  have alpha : N≤3^N := (N.lt_pow_self (by decide : 1<3)).le
  have base : 9*m ≤ 3^(CircleFlowTracking.horizon N) := by
    calc
      9*m ≤ N^2*N^k := Nat.mul_le_mul (by nlinarith) width
      _ = N^(k+2) := by rw [pow_add,mul_comm]
      _ ≤ (3^N)^(k+2) := Nat.pow_le_pow_left alpha _
      _ = 3^(N*(k+2)) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) big
  cases H : CircleFlowTracking.horizon N with
  | zero => rw [H,pow_zero] at base;omega
  | succ t =>
    rw [H,pow_succ (3:ℕ) t] at base
    have hi := powerIndex_eq t
    have high : 3*m≤2*powerIndex t := by omega
    refine ⟨?_,infinite_mse N m t hn odd hm c hc (by omega) b h⟩
    simpa using no_moment N m t hn odd hm c 1 hc (by norm_num)
      (by simpa only [mul_one] using (Nat.cast_le (α:=ℝ)).mpr high)

end CircleReciprocalCriterion
