module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Scalar deep-linear flow, the precision equation of the transpose-paired flow,
and the Schur-complement and log-time bounds used in the feature-learning note. -/
public section

namespace FeatureFlow

/-- The scalar tangent kernel is determined by the represented slope and imbalance. -/
theorem scalar_kernel (a w : ℝ) :
    Real.sqrt ((a ^ 2 - w ^ 2) ^ 2 + 4 * (a*w)^2) = a^2 + w^2 := by
  rw [show (a ^ 2 - w ^ 2) ^ 2 + 4 * (a*w)^2 = (a^2+w^2)^2 by ring]
  exact Real.sqrt_sq (by positivity)

theorem scalar_flow {a w : ℝ → ℝ} {s t : ℝ}
    (ha : HasDerivAt a ((s - a t*w t)*w t) t)
    (hw : HasDerivAt w ((s - a t*w t)*a t) t) :
    HasDerivAt (fun u => a u ^ 2 - w u ^ 2) 0 t ∧
    HasDerivAt (fun u => a u * w u)
      (Real.sqrt ((a t^2 - w t^2)^2 + 4*(a t*w t)^2) * (s - a t*w t)) t := by
  constructor
  · convert (ha.pow 2).sub (hw.pow 2) using 1
    ring
  · rw [scalar_kernel]
    convert ha.mul hw using 1
    ring

/-- Constancy on the actual forward training interval. -/
theorem imbalance_conserved {a w : ℝ → ℝ} {s T : ℝ} (hT : 0 ≤ T)
    (ha : ∀ t ∈ Set.Icc 0 T, HasDerivAt a ((s-a t*w t)*w t) t)
    (hw : ∀ t ∈ Set.Icc 0 T, HasDerivAt w ((s-a t*w t)*a t) t) :
    a T ^ 2 - w T ^ 2 = a 0 ^ 2 - w 0 ^ 2 := by
  have h t (ht : t ∈ Set.Icc 0 T) := (scalar_flow (ha t ht) (hw t ht)).1
  apply constant_of_has_deriv_right_zero (f := fun t => a t ^ 2 - w t ^ 2)
    (fun t ht => (h t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h t (Set.mem_Icc_of_Ico ht)).hasDerivWithinAt) T ⟨hT, le_rfl⟩

/-- The aligned mode with amplitude s and initial odds k. -/
noncomputable def aligned (s k t : ℝ) := s / (1 + k * Real.exp (-2*s*t))

theorem aligned_ode (s k t : ℝ) (hk : 0 ≤ k) :
    HasDerivAt (aligned s k) (2 * aligned s k t * (s - aligned s k t)) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2*s)).exp.const_mul k).const_add 1
  have hp : 0 < 1 + k * Real.exp (-2*s*t) := by positivity
  unfold aligned
  convert (hasDerivAt_const t s).div hd hp.ne' using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- Inverse differentiation cancels both quadratic factors in the Riccati equation. -/
theorem precision_rhs {R : Type*} [Ring R] (T B P : R) (hBP : B*P = 1) (hPB : P*B = 1) :
    -P * (T*B + B*T - (B*B+B*B)) * P = -(P*T) - (T*P) + (1+1) := by
  calc
    _ = -(P*T*(B*P)) - (P*B)*T*P + ((P*B)*(B*P)+(P*B)*(B*P)) := by noncomm_ring
    _ = _ := by simp [hBP, hPB]

/-- Every precision entry relaxes linearly about its teacher-dependent equilibrium. -/
theorem precision_entry_ode (s r limit init t : ℝ) :
    HasDerivAt (fun u => limit + (init-limit)*Real.exp (-(s+r)*u))
      (-(s+r)*((limit+(init-limit)*Real.exp (-(s+r)*t))-limit)) t := by
  have h := (((hasDerivAt_id t).const_mul (-(s+r))).exp.const_mul (init-limit)).const_add limit
  have hx : HasDerivAt (fun u : ℝ => limit+(init-limit)*Real.exp (-(s+r)*u))
      ((init-limit)*(Real.exp (-(s+r)*t)*(-(s+r)*1))) t := h
  convert hx using 1
  ring

/-- Reciprocal diagonals satisfy two Schur-complement bounds. -/
theorem schur_envelope (base Dii Djj z u v other : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hj : 0 < Djj) (ho : 0 < other)
    (hdom : v*Djj ≤ other) :
    base + u*(Dii-z^2/Djj) ≤ base + u*(Dii-z^2*v/other) ∧
      base + u*(Dii-z^2*v/other) ≤ base + u*Dii := by
  have hratio : z^2*v/other ≤ z^2/Djj := by
    rw [div_le_div_iff₀ ho hj]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdom (sq_nonneg z)
  constructor
  · exact add_le_add (le_refl base) (mul_le_mul_of_nonneg_left (sub_le_sub_left hratio Dii) hu)
  · have hz : 0 ≤ z^2*v/other := by positivity
    exact add_le_add (le_refl base) (mul_le_mul_of_nonneg_left (sub_le_self Dii hz) hu)

/-- Any crossing whose decaying reciprocal correction is bracketed by two positive
coefficients has a two-sided log-time bound. -/
theorem crossing_bounds (s H lo hi t : ℝ) (hs : 0 < s) (hH : 0 < H)
    (hlo : 0 < lo) (hhi : 0 < hi)
    (hl : lo*Real.exp (-2*s*t) ≤ H) (hu : H ≤ hi*Real.exp (-2*s*t)) :
    Real.log (lo/H)/(2*s) ≤ t ∧ t ≤ Real.log (hi/H)/(2*s) := by
  have hE : 0 < Real.exp (2*s*t) := Real.exp_pos _
  have heq : Real.exp (-2*s*t) = (Real.exp (2*s*t))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [heq, ← div_eq_mul_inv] at hl hu
  have l := (div_le_iff₀ hE).mp hl
  have u := (le_div_iff₀ hE).mp hu
  constructor
  · rw [div_le_iff₀ (by positivity : 0 < 2*s)]
    apply (Real.log_le_iff_le_exp (div_pos hlo hH)).mpr
    rw [div_le_iff₀ hH, mul_comm t (2*s), mul_comm (Real.exp _) H]
    exact l
  · rw [le_div_iff₀ (by positivity : 0 < 2*s)]
    apply (Real.le_log_iff_exp_le (div_pos hhi hH)).mpr
    rw [le_div_iff₀ hH, mul_comm t (2*s), mul_comm (Real.exp _) H]
    exact u

/-- Exact rotation entries, written using z = sin² θ and positive product eigenvalues. -/
def diagonal (a b z : ℝ) : ℝ := (1-z)*a + z*b

noncomputable def initialPrecision (a b z : ℝ) : ℝ := diagonal (1/a) (1/b) z

noncomputable def offDiagonalSq (a b z : ℝ) : ℝ := (1/a-1/b)^2*z*(1-z)

theorem diagonal_pos {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    0 < diagonal a b z := by
  unfold diagonal
  rcases eq_or_lt_of_le hz with h | h
  · simp [← h, ha]
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) ha.le) (mul_pos h hb)

/-- The lower coefficient in the Schur envelope is the inverse starting response. -/
theorem rotation_schur {a b z : ℝ} (ha : 0 < a) (hb : 0 < b) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    initialPrecision a b z - offDiagonalSq a b z / initialPrecision b a z =
      1 / diagonal a b z := by
  have h₁ := diagonal_pos ha hb hz hz'
  have h₂ := diagonal_pos (one_div_pos.mpr hb) (one_div_pos.mpr ha) hz hz'
  unfold initialPrecision diagonal offDiagonalSq at *
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt h₁, ne_of_gt h₂]
  ring

/-- Inverse precision diagonal at time t for a mode with teacher strength s,
other strength r, and initial product eigenvalues a,b. -/
noncomputable def reciprocalMode (s r a b z t : ℝ) : ℝ :=
  let u := Real.exp (-2*s*t)
  let v := Real.exp (-2*r*t)
  let other := (1-v)/r + v*initialPrecision b a z
  (1-u)/s + u*(initialPrecision a b z - offDiagonalSq a b z*v/other)

/-- Every directional threshold crossing in the rotated matrix solution lies in
this interval. The two endpoints use the observable starting response and initial
precision, respectively. This applies to either teacher mode. -/
theorem rotated_crossing_window {s r a b q z t : ℝ}
    (hs : 0 < s) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hq : 0 < q) (hq' : q < 1) (hz : 0 ≤ z) (hz' : z ≤ 1) (ht : 0 ≤ t)
    (hstart : diagonal a b z < q*s)
    (hcross : reciprocalMode s r a b z t = 1/(q*s)) :
    Real.log ((1 / diagonal a b z - 1/s)/(1/(q*s)-1/s))/(2*s) ≤ t ∧
      t ≤ Real.log ((initialPrecision a b z - 1/s)/(1/(q*s)-1/s))/(2*s) := by
  let u := Real.exp (-2*s*t)
  let v := Real.exp (-2*r*t)
  let other := (1-v)/r + v*initialPrecision b a z
  have hu : 0 < u := Real.exp_pos _
  have hv : 0 < v := Real.exp_pos _
  have hv' : v ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hr.le ht])
  have hj := diagonal_pos (one_div_pos.mpr hb) (one_div_pos.mpr ha) hz hz'
  change 0 < initialPrecision b a z at hj
  have hdom : v*initialPrecision b a z ≤ other := by
    change _ ≤ (1-v)/r + _
    linarith [div_nonneg (sub_nonneg.mpr hv') hr.le]
  have hop : 0 < other := (mul_pos hv hj).trans_le hdom
  have hzq : 0 ≤ offDiagonalSq a b z := by
    unfold offDiagonalSq
    exact mul_nonneg (mul_nonneg (sq_nonneg _) hz) (sub_nonneg.mpr hz')
  have env := schur_envelope ((1-u)/s) (initialPrecision a b z)
    (initialPrecision b a z) (Real.sqrt (offDiagonalSq a b z)) u v other
    hu.le hv.le hj hop hdom
  rw [Real.sq_sqrt hzq, rotation_schur ha hb hz hz'] at env
  change (1-u)/s + u*(initialPrecision a b z - offDiagonalSq a b z*v/other) = _ at hcross
  rw [hcross] at env
  have hlo : 0 < 1 / diagonal a b z - 1/s := sub_pos.mpr
    (one_div_lt_one_div_of_lt (diagonal_pos ha hb hz hz') (hstart.trans (by nlinarith)))
  have hH : 0 < 1/(q*s)-1/s := sub_pos.mpr
    (one_div_lt_one_div_of_lt (mul_pos hq hs) (by nlinarith))
  have l : (1 / diagonal a b z - 1/s)*u ≤ 1/(q*s)-1/s := by
    convert sub_le_sub_right env.1 (1/s) using 1
    ring
  have h : 1/(q*s)-1/s ≤ (initialPrecision a b z - 1/s)*u := by
    convert sub_le_sub_right env.2 (1/s) using 1
    ring
  have hp : 0 < initialPrecision a b z - 1/s := by
    exact (mul_pos_iff_of_pos_right hu).mp (lt_of_lt_of_le hH h)
  exact crossing_bounds s _ _ _ t hs hH hlo hp l h

/-- The upper (fast-mode) coefficient contains the teacher gap times sin² θ. -/
theorem fast_coefficient (s r a z : ℝ) (hs : 0 < s) (hr : 0 < r) (ha : 0 < a) (ha' : a < 1) :
    initialPrecision (a*s) (a*r) z - 1/s =
      (1/(a*s)-1/s)*(1+(s-r)*z/((1-a)*r)) := by
  unfold initialPrecision diagonal
  field_simp [ne_of_gt hs, ne_of_gt hr, ne_of_gt ha, sub_ne_zero.mpr ha'.ne']
  ring

/-- The lower (slow-mode) coefficient gives the opposite sign. -/
theorem slow_coefficient (s r a z : ℝ) (hs : 0 < s) (hr : 0 < r) (ha : 0 < a) (ha' : a < 1)
    (hz : 0 ≤ z) (hz' : z ≤ 1) :
    1 / diagonal (a*r) (a*s) z - 1/r =
      (1/(a*r)-1/r)*(1-(s-r)*z/((1-a)*(r+(s-r)*z))) := by
  have h := diagonal_pos hr hs hz hz'
  unfold diagonal at *
  have hd : 0 < r+(s-r)*z := by linarith
  rw [show (1-z)*(a*r)+z*(a*s) = a*(r+(s-r)*z) by ring]
  field_simp [ne_of_gt hr, ne_of_gt ha, ne_of_gt hd, sub_ne_zero.mpr ha'.ne']
  ring

/-- Under a teacher-independent isotropic start, the larger teacher strength has
the larger learned strength at every positive time. -/
theorem isotropic_modes_separate {s r p t : ℝ} (hps : 0 < p) (hpr : p < r)
    (hrs : r < s) (ht : 0 < t) : aligned r (r/p-1) t < aligned s (s/p-1) t := by
  have hr := hps.trans hpr
  have hs := hr.trans hrs
  let u := Real.exp (-2*s*t)
  let v := Real.exp (-2*r*t)
  have huv : u < v := Real.exp_lt_exp.mpr (by nlinarith [mul_pos (sub_pos.mpr hrs) ht])
  have hv : v < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hr ht])
  have hpsi : 0 < 1/p-1/s := sub_pos.mpr (one_div_lt_one_div_of_lt hps (hpr.trans hrs))
  have hprec : (1-u)/s+u/p < (1-v)/r+v/p := by
    calc
      (1-u)/s+u/p = 1/s+u*(1/p-1/s) := by ring
      _ < 1/s+v*(1/p-1/s) := by gcongr
      _ = (1-v)*(1/s)+v/p := by ring
      _ < (1-v)*(1/r)+v/p := by
        exact add_lt_add_left (mul_lt_mul_of_pos_left (one_div_lt_one_div_of_lt hr hrs)
          (sub_pos.mpr hv)) _
      _ = _ := by ring
  have hform (x : ℝ) (hx : 0 < x) (hp : p < x) :
      1 / aligned x (x/p-1) t = (1-Real.exp (-2*x*t))/x + Real.exp (-2*x*t)/p := by
    unfold aligned
    have hxp : 0 < x/p-1 := sub_pos.mpr ((lt_div_iff₀ hps).mpr (by linarith))
    have hk : 0 < 1+(x/p-1)*Real.exp (-2*x*t) := by positivity
    field_simp [ne_of_gt hx, ne_of_gt hps, ne_of_gt hk]
    ring
  have hpos : 0 < aligned r (r/p-1) t := by
    have h : 0 < r/p-1 := sub_pos.mpr ((lt_div_iff₀ hps).mpr (by linarith))
    unfold aligned
    positivity
  have hpos' : 0 < aligned s (s/p-1) t := by
    have h : 0 < s/p-1 := sub_pos.mpr ((lt_div_iff₀ hps).mpr (by linarith))
    unfold aligned
    positivity
  apply (one_div_lt_one_div hpos' hpos).mp
  rw [hform s hs (hpr.trans hrs), hform r hr hpr]
  exact hprec

end FeatureFlow
