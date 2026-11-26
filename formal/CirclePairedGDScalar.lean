module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Magnitudes at a synchronized axial seed, and comparison of the fast and slow recurrences. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDScalar

/-- The signed label term is shared by both layer updates at each time. -/
def nextMag (τ η q y a w : ℝ) : ℝ := η*τ*(q*a*w^2-y*w)-a

def factor (τ η q y a w : ℝ) : ℝ :=
  1-1/(η*τ*q*w^2)-y/(q*a*w)

private theorem factor_bounds {τ η q y a w R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : 1/16≤q) (hy : |y|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (ha : R≤a) (hw : R≤w) :
    15/16 ≤ factor τ η q y a w ∧ factor τ η q y a w ≤ 17/16 := by
  have r : 0<R := by linarith
  have a0 : 0<a := lt_of_lt_of_le r ha
  have w0 : 0<w := lt_of_lt_of_le r hw
  have τ0 : 0<τ := by linarith
  have q0 : 0<q := by linarith
  have hmass := (div_le_iff₀ hη).mp (show 32/η ≤ R^2/16-32 by linarith)
  have hqr := mul_le_mul_of_nonneg_right hq (sq_nonneg R)
  have hmain : 32+32*η≤η*q*R^2 := by
    nlinarith only [hmass, mul_le_mul_of_nonneg_left hqr hη.le]
  have sum : 2/(η*q*R^2)+2/(q*R^2)≤1/16 := by
    field_simp [hη.ne',q0.ne',r.ne']
    nlinarith only [hmain]
  have den : 1/(η*τ*q*w^2) ≤ 2/(η*q*R^2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hrw : R^2 ≤ w^2 := by gcongr
    have hh : R^2≤2*τ*w^2 := by
      nlinarith only [hrw,mul_le_mul_of_nonneg_right hτ (sq_nonneg w)]
    have := mul_le_mul_of_nonneg_left hh (mul_nonneg hη.le q0.le)
    linarith only [this]
  have baw : R^2≤a*w := by rw [sq]; gcongr
  have upper : |y|/(q*a*w) ≤ 2/(q*R^2) := by
    apply (div_le_div_of_nonneg_right hy (by positivity)).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left baw q0.le
  have byabs : |y/(q*a*w)| ≤ 2/(q*R^2) := by
    rwa [abs_div,abs_of_pos (show 0<q*a*w by positivity)]
  have cy := abs_le.mp byabs
  have invp : 0 ≤ 1/(η*τ*q*w^2) := by positivity
  have tp : 0 ≤ 2/(η*q*R^2) := by positivity
  unfold factor
  constructor <;> linarith

theorem nextMag_bounds {τ η q y a w R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : 1/16≤q) (hy : |y|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (ha : R≤a) (hw : R≤w) :
    (15/16)*(η*τ*q*a*w^2) ≤ nextMag τ η q y a w ∧
      nextMag τ η q y a w ≤ (17/16)*(η*τ*q*a*w^2) := by
  have a0 : 0<a := by linarith
  have w0 : 0<w := by linarith
  have τ0 : 0<τ := by linarith
  have q0 : 0<q := by linarith
  have eq : nextMag τ η q y a w = factor τ η q y a w*(η*τ*q*a*w^2) := by
    unfold nextMag factor
    field_simp [hη.ne',τ0.ne',q0.ne',a0.ne',w0.ne']
    ring
  have hh := factor_bounds hτ hη hq hy hR hlarge ha hw
  rw [eq]
  exact ⟨mul_le_mul_of_nonneg_right hh.1 (by positivity),
    mul_le_mul_of_nonneg_right hh.2 (by positivity)⟩

theorem nextMag_lower {τ η q y a w R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : 1/16≤q) (hy : |y|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (ha : R≤a) (hw : R≤w) :
    (15/256)*η*τ*a*w^2 ≤ nextMag τ η q y a w := by
  have a0 : 0≤a := by linarith
  have τ0 : 0≤τ := by linarith
  have hh := (nextMag_bounds hτ hη hq hy hR hlarge ha hw).1
  have hhq := mul_le_mul_of_nonneg_right hq (show 0≤η*τ*a*w^2 by positivity)
  nlinarith only [hh,hhq]

theorem nextMag_growth {τ η q y a w R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : 1/16≤q) (hy : |y|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (ha : R≤a) (hw : R≤w) :
    2*a ≤ nextMag τ η q y a w := by
  have r : 0<R := by linarith
  have a0 : 0<a := by linarith
  have w0 : 0<w := by linarith
  have hmass := (div_le_iff₀ hη).mp (show 32/η ≤ R^2/16-32 by linarith)
  have hrw : R^2≤w^2 := by gcongr
  have hh : 512 ≤ η*w^2 := by
    nlinarith only [hmass, mul_le_mul_of_nonneg_left hrw hη.le, hη]
  have h1 := mul_le_mul_of_nonneg_right hτ (show 0≤η*w^2 by positivity)
  have h2 : 2≤(15/256)*η*τ*w^2 := by nlinarith only [hh,h1]
  calc
    2*a ≤ (15/256)*η*τ*w^2*a := mul_le_mul_of_nonneg_right h2 a0.le
    _ = (15/256)*η*τ*a*w^2 := by ring
    _ ≤ _ := nextMag_lower hτ hη hq hy hR hlarge ha hw

def orbit (q y : ℕ → ℝ) (τ η R : ℝ) : ℕ → ℝ × ℝ
  | 0 => (R,R)
  | t+1 =>
    let z := orbit q y τ η R t
    (nextMag 1 η (q t) (y t) z.1 z.2, nextMag τ η (q t) (y t) z.2 z.1)

theorem orbit_large {q y : ℕ → ℝ} {τ η R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : ∀ t, 1/16≤q t) (hy : ∀ t, |y t|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    R ≤ (orbit q y τ η R t).1 ∧ R ≤ (orbit q y τ η R t).2 := by
  induction t with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ t ih =>
    have a := nextMag_growth (τ := 1) (by norm_num) hη (hq t) (hy t) hR hlarge ih.1 ih.2
    have w := nextMag_growth hτ hη (hq t) (hy t) hR hlarge ih.2 ih.1
    change R ≤ nextMag 1 _ _ _ _ _ ∧ R ≤ nextMag τ _ _ _ _ _
    constructor <;> linarith only [a,w,ih.1,ih.2,hR]

def product (z : ℝ × ℝ) := z.1*z.2

private theorem product_bounds {q y : ℕ → ℝ} {τ η R : ℝ}
    (hτ : 1/2 ≤ τ) (hη : 0<η) (hq : ∀ t, 1/16≤q t) (hy : ∀ t, |y t|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    (15/16)^2*η^2*τ*(q t)^2*(product (orbit q y τ η R t))^3 ≤
      product (orbit q y τ η R (t+1)) ∧
    product (orbit q y τ η R (t+1)) ≤
      (17/16)^2*η^2*τ*(q t)^2*(product (orbit q y τ η R t))^3 := by
  let z := orbit q y τ η R t
  have hr := orbit_large hτ hη hq hy hR hlarge t
  have a0 : 0≤z.1 := (show 0≤R by linarith).trans hr.1
  have w0 : 0≤z.2 := (show 0≤R by linarith).trans hr.2
  have τ0 : 0<τ := by linarith
  have q0 : 0≤q t := (show (0:ℝ)≤1/16 by norm_num).trans (hq t)
  have ha := nextMag_bounds (τ:=1) (by norm_num) hη (hq t) (hy t) hR hlarge hr.1 hr.2
  have hw := nextMag_bounds hτ hη (hq t) (hy t) hR hlarge hr.2 hr.1
  change (15/16)^2*η^2*τ*(q t)^2*(z.1*z.2)^3 ≤
    nextMag 1 η (q t) (y t) z.1 z.2 * nextMag τ η (q t) (y t) z.2 z.1 ∧
    nextMag 1 η (q t) (y t) z.1 z.2 * nextMag τ η (q t) (y t) z.2 z.1 ≤ (17/16)^2*η^2*τ*(q t)^2*(z.1*z.2)^3
  change (15/16)*(η*1*q t*z.1*z.2^2) ≤ _ ∧ _ ≤ (17/16)*(η*1*q t*z.1*z.2^2) at ha
  change (15/16)*(η*τ*q t*z.2*z.1^2) ≤ _ ∧ _ ≤ (17/16)*(η*τ*q t*z.2*z.1^2) at hw
  have ap := (show 0≤(15/16)*(η*1*q t*z.1*z.2^2) by positivity).trans ha.1
  have wp := (show 0≤(15/16)*(η*τ*q t*z.2*z.1^2) by positivity).trans hw.1
  constructor
  · convert mul_le_mul ha.1 hw.1 (by positivity) ap using 1; ring
  · convert mul_le_mul ha.2 hw.2 wp (by positivity) using 1; ring

theorem ratio_step {q y : ℕ → ℝ} {η R : ℝ} (hη : 0<η)
    (hq : ∀ t, 1/16≤q t) (hy : ∀ t, |y t|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) (D : ℝ) (hD : 0≤D)
    (sep : D*product (orbit q y (1/2) η R t) ≤ product (orbit q y 2 η R t)) :
    (2*D^3)*product (orbit q y (1/2) η R (t+1)) ≤
      product (orbit q y 2 η R (t+1)) := by
  let S := product (orbit q y (1/2) η R t)
  let F := product (orbit q y 2 η R t)
  have s := product_bounds (τ:=1/2) (by norm_num) hη hq hy hR hlarge t
  have f := product_bounds (τ:=2) (by norm_num) hη hq hy hR hlarge t
  have a := orbit_large (τ:=1/2) (by norm_num) hη hq hy hR hlarge t
  have s0 : 0≤S := mul_nonneg ((show 0≤R by linarith).trans a.1)
    ((show 0≤R by linarith).trans a.2)
  have f0 : 0≤F := (mul_nonneg hD s0).trans sep
  have h3 : (D*S)^3 ≤ F^3 := pow_le_pow_left₀ (mul_nonneg hD s0) sep 3
  calc
    _ ≤ (2*D^3)*((17/16)^2*η^2*(1/2)*(q t)^2*S^3) :=
      mul_le_mul_of_nonneg_left s.2 (by positivity)
    _ = ((17/16)^2)*(η^2*(q t)^2)*(D*S)^3 := by ring
    _ ≤ ((17/16)^2)*(η^2*(q t)^2)*F^3 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ (15/16)^2*η^2*2*(q t)^2*F^3 := by
      have h : 0 ≤ η^2*(q t)^2*F^3 := by positivity
      nlinarith only [h]
    _ ≤ _ := f.1

/-- The fast-to-slow product ratio grows at least cubically at every update. -/
theorem ratio_growth {q y : ℕ → ℝ} {η R : ℝ} (hη : 0<η)
    (hq : ∀ t, 1/16≤q t) (hy : ∀ t, |y t|≤2)
    (hR : 1≤R) (hlarge : 16*(32/η+32)≤R^2) (t : ℕ) :
    (2:ℝ)^(3^t)*product (orbit q y (1/2) η R (t+1)) ≤
      product (orbit q y 2 η R (t+1)) := by
  induction t with
  | zero =>
    have h := ratio_step hη hq hy hR hlarge 0 1 (by norm_num) (by simp [orbit, product])
    simpa using h
  | succ t ih =>
    let d := (2:ℝ)^(3^t)
    have dp : 0≤d := by dsimp [d];positivity
    have h := ratio_step hη hq hy hR hlarge (t+1) d dp ih
    have he : (2:ℝ)^(3^(t+1))=d^3 := by dsimp [d];rw [←pow_mul,pow_succ 3 t]
    rw [he]
    apply le_trans _ h
    apply mul_le_mul_of_nonneg_right (by nlinarith only [pow_nonneg dp 3])
    have hr := orbit_large (τ:=1/2) (by norm_num) hη hq hy hR hlarge (t+1+1)
    exact mul_nonneg ((show 0≤R by linarith).trans hr.1) ((show 0≤R by linarith).trans hr.2)

end CirclePairedGDScalar
