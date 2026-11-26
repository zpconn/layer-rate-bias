module

public import CirclePairedGDScalar
public import CirclePairedGDGeometry
import all CirclePairedGDScalar
import all CirclePairedGDGeometry
import all CircleWeightedStep
import Mathlib.Tactic

/-! Exact centered trajectories of the two circle networks, and separation of
their output amplitudes on the same initialization. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDCenter
open Real CirclePairedGDGeometry
open CirclePairedGDScalar (nextMag)
open CircleFlowPath CircleWeightedStep

def sign (t : ℕ) : ℝ := (-1)^t

theorem sign_zero : sign 0 = 1 := by simp [sign]
theorem sign_succ (t : ℕ) : sign (t+1) = -sign t := by simp [sign,pow_succ]
theorem abs_sign (t : ℕ) : |sign t|=1 := by simp [sign,abs_pow]

def qs (N t : ℕ) : ℝ := q N (sign t)
def ys (N m t : ℕ) : ℝ := sign t * b N (sign t) / sqrt m

def orbit (N m : ℕ) (τ η R : ℝ) : ℕ → ℝ × ℝ :=
  CirclePairedGDScalar.orbit (qs N) (ys N m) τ η R

theorem orbit_zero (N m : ℕ) (τ η R : ℝ) : orbit N m τ η R 0 = (R,R) := rfl

theorem orbit_succ (N m : ℕ) (τ η R : ℝ) (t : ℕ) :
    let z := orbit N m τ η R t
    orbit N m τ η R (t+1) = (nextMag 1 η (qs N t) (ys N m t) z.1 z.2,
      nextMag τ η (qs N t) (ys N m t) z.2 z.1) := rfl

theorem qs_lower {N : ℕ} (hN : 3≤N) (t : ℕ) : 1/16≤qs N t :=
  q_lower N hN (sign t) (abs_sign t)

theorem ys_bound {m : ℕ} (hm : 0<m) (N t : ℕ) : |ys N m t|≤2 := by
  have m1 : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have r1 : 1 ≤ sqrt m := Real.one_le_sqrt.mpr m1
  have rp : 0 < sqrt m := by linarith
  rw [ys,abs_div,abs_mul,abs_sign,one_mul,abs_of_nonneg (b_nonneg ..),
    abs_of_nonneg (sqrt_nonneg _),div_le_iff₀ rp]
  linarith only [b_upper N (sign t) (abs_sign t), r1]

theorem orbit_large {N m : ℕ} {τ η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hτ : 1/2≤τ) (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    R≤(orbit N m τ η R t).1 ∧ R≤(orbit N m τ η R t).2 :=
  CirclePairedGDScalar.orbit_large hτ hη (qs_lower hN) (ys_bound hm N) hR hlarge t

theorem orbit_step_lower {N m : ℕ} {τ η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hτ : 1/2≤τ) (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let z := orbit N m τ η R t
    (15/256)*η*z.1*z.2^2 ≤ (orbit N m τ η R (t+1)).1 ∧
    (15/256)*η*τ*z.2*z.1^2 ≤ (orbit N m τ η R (t+1)).2 := by
  have hr := orbit_large hN hm hτ hη hR hlarge t
  dsimp only
  rw [orbit_succ]
  constructor
  · simpa only [mul_one] using CirclePairedGDScalar.nextMag_lower (τ:=1) (by norm_num)
      hη (qs_lower hN t) (ys_bound hm N t) hR hlarge hr.1 hr.2
  · exact CirclePairedGDScalar.nextMag_lower hτ hη (qs_lower hN t) (ys_bound hm N t) hR hlarge hr.2 hr.1

theorem orbit_scale {N m : ℕ} {τ η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hτ : 1/2≤τ) (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let z := orbit N m τ η R t
    1≤η*z.2^2 ∧ 1≤η*τ*z.1^2 := by
  intro z
  have hr := orbit_large hN hm hτ hη hR hlarge t
  have mass := (div_le_iff₀ hη).mp (show 32/η ≤ R^2/16-32 by linarith)
  have e : 512≤η*R^2 := by nlinarith only [mass, hη]
  have aa : R^2≤z.1^2 := by exact pow_le_pow_left₀ (by linarith : 0≤R) hr.1 2
  have ww : R^2≤z.2^2 := by exact pow_le_pow_left₀ (by linarith : 0≤R) hr.2 2
  constructor
  · linarith only [e,mul_le_mul_of_nonneg_left ww hη.le]
  · nlinarith only [e,mul_le_mul_of_nonneg_left aa hη.le,
      mul_le_mul_of_nonneg_right hτ (mul_nonneg hη.le (sq_nonneg z.1))]

theorem ratio_growth {N m : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let S := orbit N m (1/2) η R (t+1)
    let F := orbit N m 2 η R (t+1)
    (2:ℝ)^(3^t)*(S.1*S.2)≤F.1*F.2 :=
  CirclePairedGDScalar.ratio_growth hη (qs_lower hN) (ys_bound hm N) hR hlarge t

/-- Solving the lower-bound recursion starting from identical products gives the
geometric sum of exponents over the entire training clock. -/
theorem ratio_growth_exact {N m : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let S := orbit N m (1/2) η R t
    let F := orbit N m 2 η R t
    (2:ℝ)^((3^t-1)/2 : ℕ)*(S.1*S.2)≤F.1*F.2 := by
  induction t with
  | zero => simp [orbit_zero]
  | succ t ih =>
    let e := (3^t-1)/2
    have he : (3^(t+1)-1)/2 = 1+e*3 := by
      obtain ⟨k,hk⟩ := (show Odd ((3:ℕ)^t) from (by decide : Odd (3:ℕ)).pow)
      dsimp [e]
      rw [pow_succ]
      omega
    have h := CirclePairedGDScalar.ratio_step hη (qs_lower hN) (ys_bound hm N)
      hR hlarge t ((2:ℝ)^e) (by positivity) ih
    dsimp only
    rw [he,pow_add,pow_mul,pow_one]
    exact h

theorem fast_product {N m : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    let F := orbit N m 2 η R (t+1)
    (2:ℝ)^(3^t)*R^2≤F.1*F.2 := by
  intro F
  have hr := orbit_large (τ:=1/2) hN hm (by norm_num) hη hR hlarge (t+1)
  have low := mul_le_mul hr.1 hr.2 (by linarith : 0≤R) (by linarith only [hr.1,hR])
  apply le_trans _ (ratio_growth hN hm hη hR hlarge t)
  exact mul_le_mul_of_nonneg_left (by simpa [sq] using low) (by positivity)

theorem separation {N m : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (T : ℕ) (ht : 2≤T) :
    let S := orbit N m (1/2) η R T
    let F := orbit N m 2 η R T
    8*(S.1*S.2)≤F.1*F.2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le' (show 1≤T by omega)
  have h1 : 1≤t := by omega
  have h3 : 3≤3^t := by simpa using Nat.pow_le_pow_right (by decide : 0<3) h1
  have hp : (8:ℝ)≤2^(3^t) := (by norm_num : (8:ℝ)≤2^(3:ℕ)).trans
    (pow_le_pow_right₀ (by norm_num) h3)
  have hr := orbit_large (τ:=1/2) hN hm (by norm_num) hη hR hlarge (t+1)
  exact (mul_le_mul_of_nonneg_right hp (mul_nonneg ((by linarith : 0≤R).trans hr.1)
    ((by linarith : 0≤R).trans hr.2))).trans (ratio_growth hN hm hη hR hlarge t)

/-- The hidden vectors all point along the signed horizontal axis. -/
def state (N m : ℕ) (τ η R : ℝ) (t : ℕ) : State m :=
  let z := orbit N m τ η R t
  center m (sign t * z.1) (sign t * z.2)

theorem state_zero (N m : ℕ) (τ η R : ℝ) : state N m τ η R 0 = center m R R := by
  simp [state, orbit_zero, sign_zero]

/-- The scalar recurrence agrees at each step with the simultaneous network update. -/
theorem state_step {N m : ℕ} {τ η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hτ : 1/2≤τ) (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    segment τ N (state N m τ η R t) η = state N m τ η R (t+1) := by
  let z := orbit N m τ η R t
  have hz := orbit_large hN hm hτ hη hR hlarge t
  have hw : 0<z.2 := (by linarith : 0<R).trans_le hz.2
  change segment τ N (center m (sign t*z.1) (sign t*z.2)) η = _
  rw [center_segment N m (by omega) hm η τ (sign t) (sign t) z.1 z.2 (abs_sign _) (abs_sign _) hw]
  simp only [state, orbit_succ, sign_succ, qs, ys, nextMag]
  change center m _ _ = center m (-sign t * (η*1*(q N (sign t)*z.1*z.2^2 -
    (sign t*b N (sign t)/sqrt m)*z.2) - z.1)) (-sign t * (η*τ*(q N (sign t)*z.2*z.1^2 -
    (sign t*b N (sign t)/sqrt m)*z.1) - z.2))
  have hs : sign t = 1 ∨ sign t = -1 := (abs_eq (by norm_num)).mp (abs_sign t)
  rcases hs with h|h <;> rw [h] <;> congr 1 <;> ring

/-- The closed recurrence represents the actual discrete GD trajectory for every horizon. -/
theorem iterate_center {N m : ℕ} {τ η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hτ : 1/2≤τ) (hη : 0<η) (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    iterate τ η N (center m R R) t = state N m τ η R t := by
  induction t with
  | zero => exact (state_zero ..).symm
  | succ t ih => rw [iterate,ih,state_step hN hm hτ hη hR hlarge t]

end CirclePairedGDCenter
