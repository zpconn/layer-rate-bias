module

public import TwoLayerMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Finite-confidence infinite-time movement of the original Gaussian
two-layer LeakyReLU network. -/
@[expose] public section
noncomputable section
namespace TwoLayerLimit
open NonlinearBudget TwoLayerNetwork TwoLayerBudget TwoLayerMoments TwoLayerInitialization
open MeasureTheory ProbabilityTheory Set Filter Real
open scoped InnerProduct NNReal Topology
variable {n d k : ℕ}

/-- The endpoint comparison uses the same seed's Gram matrix. -/
def Endpoint (F : Params n d → Space k) (J : Params n d → Params n d →L[ℝ] Space k)
    (A : Params n d →L[ℝ] Space k) (h E : ℝ) : Prop :=
  ∃ K : Space k ≃L[ℝ] Space k, (∀ y, K y = A ((A†) y)) ∧
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧
      |‖D‖^2-inner ℝ (F 0) (K.symm (F 0))| ≤ E

/-- Joint bounds for the full displacement vector and its squared norm. -/
def JointEndpoint (F : Params n d → Space k) (J : Params n d → Params n d →L[ℝ] Space k)
    (A : Params n d →L[ℝ] Space k) (h e E : ℝ) : Prop :=
  ∃ K : Space k ≃L[ℝ] Space k, (∀ y, K y = A ((A†) y)) ∧
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧
      ‖D-(A†) (K.symm (-F 0))‖ ≤ e ∧ |‖D‖^2-inner ℝ (F 0) (K.symm (F 0))| ≤ E

theorem JointEndpoint.squared {F : Params n d → Space k} {J : Params n d → Params n d →L[ℝ] Space k}
    {A : Params n d →L[ℝ] Space k} {h e E : ℝ} (v : JointEndpoint F J A h e E) : Endpoint F J A h E := by
  obtain ⟨K,gram,D,lim,fit,_,bound⟩ := v
  exact ⟨K,gram,D,lim,fit,bound⟩

theorem joint_endpoint_bound (F : Params n d → Space k) (J : Params n d → Params n d →L[ℝ] Space k)
    (A : Params n d →L[ℝ] Space k) {h R l V : ℝ} (δ : ℝ≥0) (hl : 0<l) (hp : 0<h) (hR : 0≤R)
    (frame : ∀ y, l*‖y‖^2 ≤ ‖(A†) y‖^2) (res : ‖F 0‖≤V)
    (cert : BallControl F J A h R (1-h*l/4) δ) :
    let e := (δ:ℝ)*(R/sqrt l+4*V/l)
    JointEndpoint F J A h e (2*(V/sqrt l)*e+e^2) := by
  intro e
  let K := gramEquiv A h (gram_strict cert)
  let B := (A†).comp K.symm.toContinuousLinearMap
  have Bn : ‖B‖ ≤ 1/sqrt l := inverse_norm A h (gram_strict cert) l hl frame
  have v0 := (norm_nonneg _).trans res
  have z0 := Real.sqrt_pos.mpr hl
  have ee : 0≤e := by dsimp [e]; positivity
  have B0 : ‖B (F 0)‖ ≤ V/sqrt l :=
    (B.le_opNorm _).trans ((mul_le_mul Bn res (norm_nonneg _) (by positivity)).trans_eq (by ring))
  let s := h*(δ:ℝ)*‖F 0‖/(1-(1-h*l/4))
  have sId : s = 4*(δ:ℝ)*‖F 0‖/l := by dsimp [s];field_simp;ring
  have s0 : 0≤s := by rw [sId]; positivity
  have b₁ : ‖B‖*((δ:ℝ)*R) ≤ (δ:ℝ)*(R/sqrt l) := by
    calc _ ≤ (1/sqrt l)*((δ:ℝ)*R) := mul_le_mul_of_nonneg_right Bn (mul_nonneg δ.2 hR)
         _ = _ := by ring
  have b₂ : s ≤ (δ:ℝ)*(4*V/l) := by rw [sId]; apply (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left res (by positivity : 0≤4*(δ:ℝ))) hl.le).trans_eq;ring
  let t := sqrt ((‖B‖*((δ:ℝ)*R))^2+s^2)
  have te : t≤e := by
    apply (Real.sqrt_le_iff.mpr ⟨ee,?_⟩)
    have b := add_le_add b₁ b₂
    have non : 0≤‖B‖*((δ:ℝ)*R) := by positivity
    dsimp [e]; rw [mul_add]
    nlinarith only [mul_nonneg non s0,pow_le_pow_left₀ (add_nonneg non s0) b 2]
  obtain ⟨D,lim,hit,close,bound⟩ := vector_and_quadratic_budget cert
  refine ⟨K,fun _ => rfl,D,lim,hit,close.trans te,bound.trans ?_⟩
  change 2*‖B (F 0)‖*t+t^2 ≤ _
  exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left B0 (by norm_num)) te
    (sqrt_nonneg _) (by positivity)) (pow_le_pow_left₀ (sqrt_nonneg _) te 2)

theorem endpoint_bound (F : Params n d → Space k) (J : Params n d → Params n d →L[ℝ] Space k)
    (A : Params n d →L[ℝ] Space k) {h R l V : ℝ} (δ : ℝ≥0) (hl : 0<l) (hp : 0<h) (hR : 0≤R)
    (frame : ∀ y, l*‖y‖^2 ≤ ‖(A†) y‖^2) (res : ‖F 0‖≤V)
    (cert : BallControl F J A h R (1-h*l/4) δ) :
    let e := (δ:ℝ)*(R/sqrt l+4*V/l)
    Endpoint F J A h (2*(V/sqrt l)*e+e^2) :=
  (joint_endpoint_bound F J A δ hl hp hR frame res cert).squared

/-- Dimensionless row tolerance. Here n=u³; fixed-confidence thresholds C
and p do not depend on width. -/
def tolerance (n : ℕ) (u p C R α S : ℝ) : ℝ≥0 :=
  ⟨sqrt (2*S*(R^2/n + (2*log (4*n/p))*(1-α)^2*((C+R^2)/u))),sqrt_nonneg _⟩

/-- Full finite-confidence certificate under the actual original Gaussian
law. The fit and inverse-Gram movement conclusion hold for the entire
discrete infinite-time trajectory, with one frozen reciprocal-Gram step.
All width tests are deterministic. -/
theorem gaussian_joint_endpoint (hn : 0<n) (hk : 0<k) (α ell u p ε U V R : ℝ)
    (hα : 0<α) (h1 : α≤1) (hl : 0<ell) (hu : 0<u) (width : (n:ℝ)=u^3)
    (hp : 0<p) (p1 : p≤1) (ep : 0<ε) (u0 : 0<U) (v0 : 0<V)
    (b : Fin k → ℝ) (bp : ∀ j, 0<b j) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1)
    (y : Space k) (frame : ∀ v : Space k, ell*‖v‖^2 ≤ ‖∑ j, (v j*b j) • x j‖^2)
    (s : Params n d → Fin k → Fin n → ℝ) (gs : ∀ z, gate α b x z (s z)) :
    let S := ∑ j, (b j)^2
    let l := ell*α^2*(ε^2/2)
    let δ := tolerance n u p (4*k/p) R α S
    let e := (δ:ℝ)*(R/sqrt l+4*V/l)
    let F := fun z => residual (leaky α) b x y z
    let J := fun z v => matrixOp (rows (leaky α) b x (z+v) (s (z+v)))
    let A := fun z => matrixOp (rows (leaky α) b x z (s z))
    (2*U+δ)*δ ≤ l/4 → 4*(U+δ)*V/l ≤ R →
    (stdGaussian (Params n d)).real {z |
      ¬JointEndpoint (F z) (J z) (A z) (‖A z‖^2)⁻¹ e (2*(V/sqrt l)*e+e^2)} ≤
      p+4*ε+2*S/U^2+(2*S*gaussianFourth+2*‖y‖^2)/V^2 := by
  intro S l δ e F J A small radius
  let μ := stdGaussian (Params n d)
  let M := sqrt (2*log (4*n/p))
  let C := 4*(k:ℝ)/p
  let near := fun (z : Params n d) j =>
    (Finset.univ.filter (fun i => |inner ℝ (TwoLayerNetwork.hidden z i) (x j)| ≤ 1/u)).card
  let B₁ := {z : Params n d | (∃ i, M≤|readout z i|) ∨ ∃ j, 4*k*u^2/p ≤ (near z j:ℝ)}
  let B₂ := {z : Params n d | ∃ v : Space k, ‖((A z)†) v‖^2 < l*‖v‖^2}
  let B₃ := {z : Params n d | U^2 ≤ ‖A z‖^2}
  let B₄ := {z : Params n d | V^2 ≤ ‖F z 0‖^2}
  have b₁ : μ.real B₁ ≤ p := fixed_confidence hn hk u p hu width hp p1 x hx
  have b₂ : μ.real B₂ ≤ 4*ε := gram_conditioning hn α ell ε hα.le hl.le ep b x frame s gs
  have b₃ : μ.real B₃ ≤ 2*S/U^2 := gram_upper_tail α hα.le h1 b x hx hn s gs _ (sq_pos_of_pos u0)
  have b₄ : μ.real B₄ ≤ (2*S*gaussianFourth+2*‖y‖^2)/V^2 :=
    residual_initial_tail α hα.le h1 b x hx y hn _ (sq_pos_of_pos v0)
  have union := (measureReal_union_le (μ:=μ) ((B₁∪B₂)∪B₃) B₄).trans (add_le_add
    ((measureReal_union_le _ B₃).trans (add_le_add ((measureReal_union_le _ _).trans (add_le_add b₁ b₂)) b₃)) b₄)
  apply (measureReal_mono ?_).trans union
  intro z hz
  by_contra bad
  have hB₁ : z ∉ B₁ := fun m => bad (Or.inl (Or.inl (Or.inl m)))
  have hB₂ : z ∉ B₂ := fun m => bad (Or.inl (Or.inl (Or.inr m)))
  have hB₃ : z ∉ B₃ := fun m => bad (Or.inl (Or.inr m))
  have hB₄ : z ∉ B₄ := fun m => bad (Or.inr m)
  have lp : 0<l := by dsimp [l]; positivity
  have fr (v : Space k) : l*‖v‖^2 ≤ ‖((A z)†) v‖^2 := le_of_not_gt (fun m => hB₂ ⟨v,m⟩)
  change ¬ U^2 ≤ ‖A z‖^2 at hB₃
  change ¬ V^2 ≤ ‖F z 0‖^2 at hB₄
  have ua : ‖A z‖≤U := (sq_le_sq₀ (norm_nonneg _) u0.le).mp (lt_of_not_ge hB₃).le
  have va : ‖F z 0‖≤V := (sq_le_sq₀ (norm_nonneg _) v0.le).mp (lt_of_not_ge hB₄).le
  let v : Space k := EuclideanSpace.single ⟨0,hk⟩ 1
  have vn : ‖v‖=1 := by simp [v]
  have low := (fr v).trans (pow_le_pow_left₀ (norm_nonneg _) (((A z)†).le_opNorm v) 2)
  rw [vn,one_pow,mul_one,LinearIsometryEquiv.norm_map,mul_one] at low
  let h := (‖A z‖^2)⁻¹
  have hh : 0<h := inv_pos.mpr (lp.trans_le low)
  have ht : h*‖A z‖^2 = 1 := inv_mul_cancel₀ (lp.trans_le low).ne'
  have hlow : h*l≤1 := (mul_le_mul_of_nonneg_left low hh.le).trans ht.le
  have Rp : 0≤R := (show 0≤4*(U+δ)*V/l by positivity).trans radius
  have n1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have md : 1 ≤ (4*n/p:ℝ) := (le_div_iff₀ hp).mpr (by linarith)
  have msq : M^2=2*log (4*n/p) := sq_sqrt (mul_nonneg (by norm_num) (log_nonneg md))
  have mass := leaky_rate_mass u hu width R M α C b (near z) (fun j => by
    have : (near z j:ℝ)<4*k*u^2/p := lt_of_not_ge (fun h => hB₁ (Or.inr ⟨j,h⟩))
    exact this.le.trans_eq (by dsimp [C];ring))
  have rows : (∑ j, 2*(b j)^2*(R^2+M^2*(1-α)^2*((near z j:ℝ)+R^2/(1/u)^2))) ≤ n*(δ:ℝ)^2 := by
    apply mass.trans_eq; congr 1
    rw [msq]
    change _ = (sqrt _)^2
    apply (sq_sqrt ?_).symm
    positivity [log_nonneg md]
  have q0 : 0≤1-h*l/4 := by linarith
  have q1 : 1-h*l/4<1 := by linarith [mul_pos hh lp]
  have spec := frame_contraction (A z) h l hh.le ht.le hlow fr
  have small' : (2*‖A z‖+δ)*δ ≤ l/4 := (mul_le_mul_of_nonneg_right
    (by linarith : 2*‖A z‖+δ ≤ 2*U+δ) δ.2).trans small
  have size : h*(‖A z‖+δ)*‖F z 0‖/(1-(1-h*l/4)) ≤ R := by
    rw [show 1-(1-h*l/4)=h*l/4 by ring]
    apply le_trans (b := 4*(‖A z‖+δ)*‖F z 0‖/l)
    · apply le_of_eq;field_simp
    · apply le_trans _ radius
      gcongr
  have control : BallControl (F z) (J z) (A z) h R (1-h*l/4) δ :=
    leaky_ball δ hα.le h1 (sqrt_nonneg _) (by positivity) b bp x (fun j => (hx j).le) y z s gs
      (fun i => (lt_of_not_ge (fun m => hB₁ (Or.inl ⟨i,m⟩))).le) rows hh q0 q1
      (by linarith [mul_le_mul_of_nonneg_left small' hh.le]) size
  exact hz (joint_endpoint_bound (F z) (J z) (A z) δ lp hh Rp fr va control)

theorem gaussian_endpoint (hn : 0<n) (hk : 0<k) (α ell u p ε U V R : ℝ)
    (hα : 0<α) (h1 : α≤1) (hl : 0<ell) (hu : 0<u) (width : (n:ℝ)=u^3)
    (hp : 0<p) (p1 : p≤1) (ep : 0<ε) (u0 : 0<U) (v0 : 0<V)
    (b : Fin k → ℝ) (bp : ∀ j, 0<b j) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1)
    (y : Space k) (frame : ∀ v : Space k, ell*‖v‖^2 ≤ ‖∑ j, (v j*b j) • x j‖^2)
    (s : Params n d → Fin k → Fin n → ℝ) (gs : ∀ z, gate α b x z (s z)) :
    let S := ∑ j, (b j)^2
    let l := ell*α^2*(ε^2/2)
    let δ := tolerance n u p (4*k/p) R α S
    let e := (δ:ℝ)*(R/sqrt l+4*V/l)
    let F := fun z => residual (leaky α) b x y z
    let J := fun z v => matrixOp (rows (leaky α) b x (z+v) (s (z+v)))
    let A := fun z => matrixOp (rows (leaky α) b x z (s z))
    (2*U+δ)*δ ≤ l/4 → 4*(U+δ)*V/l ≤ R →
    (stdGaussian (Params n d)).real {z |
      ¬Endpoint (F z) (J z) (A z) (‖A z‖^2)⁻¹ (2*(V/sqrt l)*e+e^2)} ≤
      p+4*ε+2*S/U^2+(2*S*gaussianFourth+2*‖y‖^2)/V^2 := by
  intro S l δ e F J A small radius
  apply (measureReal_mono ?_).trans
    (gaussian_joint_endpoint hn hk α ell u p ε U V R hα h1 hl hu width hp p1 ep u0 v0 b bp x hx y frame s gs small radius)
  intro z hz joint
  exact hz joint.squared

def cube (n : ℕ) := (n:ℝ)^((3:ℝ)⁻¹)

theorem cube_width (n : ℕ) : (n:ℝ)=(cube n)^3 :=
  (rpow_inv_natCast_pow (Nat.cast_nonneg n) (by decide : (3:ℕ)≠0)).symm

/-- The two all-time bootstrap tests become automatic at fixed positive
confidence and fixed training data. -/
theorem tolerance_tendsto {p : ℝ} (hp : 0<p) (C R α S : ℝ) :
    Tendsto (fun n : ℕ => (tolerance n (cube n) p C R α S:ℝ)) atTop (𝓝 0) := by
  have N := tendsto_natCast_atTop_atTop (R:=ℝ)
  have uc : Tendsto cube atTop atTop := (tendsto_rpow_atTop (by norm_num : 0<(3:ℝ)⁻¹)).comp N
  have g : Tendsto (fun n : ℕ => log n/cube n) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : 0<(3:ℝ)⁻¹)).tendsto_div_nhds_zero.comp N
  have h : Tendsto (fun n : ℕ => log (4*n/p)/(cube n)) atTop (𝓝 0) := by
    have c := (uc.inv_tendsto_atTop.const_mul (log (4/p))).add g
    simp only [mul_zero,zero_add] at c
    apply c.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have np : 0<(n:ℝ) := by exact_mod_cast hn
    change log (4/p)*(cube n)⁻¹+log n/cube n = _
    rw [show 4*(n:ℝ)/p = (4/p)*n by ring,log_mul (by positivity) np.ne']
    ring
  have t1 := N.inv_tendsto_atTop.const_mul (R^2)
  have t2 := h.const_mul (2*(1-α)^2*(C+R^2))
  have t := ((t1.add t2).const_mul (2*S)).sqrt
  simp only [mul_zero,add_zero,sqrt_zero] at t
  apply t.congr
  intro n
  dsimp [tolerance]; congr 1; ring

/-- Fixed-confidence normalization for the squared-budget rate:
sqrt(log n / cube(n)) = n^(-1/6)*sqrt(log n) at positive n. -/
def scale (n : ℕ) := sqrt (log n/cube n)

theorem tolerance_rate {p C S : ℝ} (hp : 0<p) (hC : 0≤C) (hS : 0≤S) (R α : ℝ) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop, (tolerance n (cube n) p C R α S : ℝ) ≤ L*scale n := by
  let L := sqrt (2*S*(R^2+2*(|log (4/p)|+1)*(1-α)^2*(C+R^2)))
  refine ⟨L,sqrt_nonneg _,?_⟩
  have g : Tendsto (fun n : ℕ => log n) atTop atTop := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 1,g.eventually_ge_atTop 1] with n hn logn
  have n1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have np := zero_lt_one.trans_le n1
  have cp : 0<cube n := rpow_pos_of_pos np _
  have cn : cube n ≤ n := by
    simpa [cube] using rpow_le_rpow_of_exponent_le n1 (by norm_num : (3:ℝ)⁻¹ ≤ 1)
  have r : 1/(n:ℝ) ≤ log n/cube n := (div_le_div_of_nonneg_left zero_le_one cp cn).trans
    (div_le_div_of_nonneg_right logn cp.le)
  have logb : log (4*n/p) ≤ (|log (4/p)|+1)*log n := by
    rw [show 4*(n:ℝ)/p=(4/p)*n by ring,log_mul (by positivity) np.ne']
    nlinarith [le_abs_self (log (4/p)),mul_nonneg (abs_nonneg (log (4/p))) (sub_nonneg.mpr logn)]
  have root : 0≤2*S*(R^2+2*(|log (4/p)|+1)*(1-α)^2*(C+R^2)) := by positivity
  change sqrt _ ≤ L*sqrt (log n/cube n)
  dsimp [L]; rw [← sqrt_mul root]
  apply sqrt_le_sqrt
  have t1 := mul_le_mul_of_nonneg_left r (sq_nonneg R)
  have t2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right logb (show 0≤2*(1-α)^2*(C+R^2) by positivity)) cp.le
  rw [mul_assoc (2*S)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hS)
  convert add_le_add t1 t2 using 1 <;> ring


theorem endpoint_mono {F : Params n d → Space k} {J : Params n d → Params n d →L[ℝ] Space k}
    {A : Params n d →L[ℝ] Space k} {h a b : ℝ} (hit : Endpoint F J A h a) (ab : a≤b) : Endpoint F J A h b := by
  obtain ⟨K,gram,D,lim,fit,err⟩ := hit
  exact ⟨K,gram,D,lim,fit,err.trans ab⟩

/-- The all-width Oₚ endpoint statement. At every desired confidence, the
entire run converges to interpolation and the error in the squared movement
is at most one fixed constant times sqrt(log n / n^(1/3)) for all sufficiently
large widths, with the empirical reciprocal-Gram learning rate. -/
theorem joint_movement_in_probability (hk : 0<k) (α ell : ℝ) (hα : 0<α) (h1 : α≤1) (hl : 0<ell)
    (b : Fin k → ℝ) (bp : ∀ j, 0<b j) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) (y : Space k)
    (frame : ∀ v : Space k, ell*‖v‖^2 ≤ ‖∑ j, (v j*b j) • x j‖^2)
    (s : ∀ n, Params n d → Fin k → Fin n → ℝ) (gs : ∀ n z, gate α b x z (s n z))
    (η : ℝ) (hη : 0<η) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      let F := fun z => residual (leaky α) b x y z
      let J := fun z v => matrixOp (rows (leaky α) b x (z+v) (s n (z+v)))
      let A := fun z => matrixOp (rows (leaky α) b x z (s n z))
      (stdGaussian (Params n d)).real {z |
        ¬JointEndpoint (F z) (J z) (A z) (‖A z‖^2)⁻¹ (L*scale n) (L*scale n)} ≤ η := by
  let S := ∑ j, (b j)^2
  let p := min (η/4) 1
  let ε := p/4
  let l := ell*α^2*(ε^2/2)
  let X := 2*S*gaussianFourth+2*‖y‖^2
  let U := sqrt (2*S/p+1)
  let V := sqrt (X/p+1)
  let R := 4*(U+1)*V/l
  let C := 4*(k:ℝ)/p
  let δ := fun n => (tolerance n (cube n) p C R α S:ℝ)
  have Sp : 0≤S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have pp : 0<p := lt_min (by positivity) zero_lt_one
  have p1 : p≤1 := min_le_right _ _
  have η4 : 4*p≤η := by have := min_le_left (η/4) (1:ℝ);dsimp [p];linarith
  have ep : 0<ε := by dsimp [ε]; positivity
  have lp : 0<l := by dsimp [l]; positivity
  have cp : 0≤C := by dsimp [C]; positivity
  have f4 : 0≤gaussianFourth := integral_nonneg fun x => by positivity
  have xp : 0≤X := by dsimp [X]; positivity
  have up : 0<U := by dsimp [U];positivity
  have vp : 0<V := by dsimp [V];positivity
  have solve (a : ℝ) (ap : 0≤a) : a / (sqrt (a/p+1))^2 ≤ p := by
    rw [sq_sqrt (by positivity)]; apply (div_le_iff₀ (by positivity)).mpr
    field_simp; nlinarith [mul_nonneg pp.le pp.le]
  have cuts : p+4*ε+2*S/U^2+X/V^2 ≤ η := by
    have u := solve (2*S) (by positivity)
    have v := solve X xp
    dsimp only [U,V,ε];linarith only [u,v,η4]
  obtain ⟨M,M0,mr⟩ := tolerance_rate pp cp Sp R α
  have lim : Tendsto δ atTop (𝓝 0) := tolerance_tendsto pp C R α S
  have gl : Tendsto (fun n => (2*U+δ n)*δ n) atTop (𝓝 0) := by
    simpa using (lim.const_add (2*U)).mul lim
  let c := R/sqrt l+4*V/l
  have r0 : 0≤R := by dsimp [R]; positivity
  have c0 : 0≤c := by dsimp [c]; positivity
  let B := 2*(V/sqrt l)*c+c^2
  have b0 : 0≤B := by dsimp [B]; positivity
  refine ⟨(B+c)*M,mul_nonneg (add_nonneg b0 c0) M0,?_⟩
  filter_upwards [eventually_ge_atTop 1,mr,lim.eventually_lt_const zero_lt_one,
    gl.eventually_lt_const (show 0<l/4 by positivity)] with n hn hm hd hs
  intro F J A
  have dn : 0≤δ n := (tolerance n (cube n) p C R α S).2
  have cap : 4*(U+δ n)*V/l ≤ R := by dsimp [R];gcongr
  have full := gaussian_joint_endpoint hn hk α ell (cube n) p ε U V R hα h1 hl
    (rpow_pos_of_pos (by exact_mod_cast hn : 0<(n:ℝ)) _) (cube_width n) pp p1 ep up vp b bp x hx y frame
    (s n) (gs n) hs.le cap
  apply (measureReal_mono ?_).trans (full.trans cuts)
  intro z hz small
  obtain ⟨K,gram,D,limit,fit,ve,be⟩ := small
  have spos : 0≤scale n := sqrt_nonneg _
  have mc := mul_nonneg M0 spos
  apply hz ⟨K,gram,D,limit,fit,ve.trans ?_,be.trans ?_⟩
  · change δ n*c≤(B+c)*M*scale n
    nlinarith only [mul_le_mul_of_nonneg_right hm c0,mul_nonneg b0 mc]
  change 2*(V/sqrt l)*(δ n*c)+(δ n*c)^2 ≤ (B+c)*M*scale n
  have dsq := mul_le_mul_of_nonneg_left hd.le dn
  have rate : B*(δ n) ≤ B*(M*scale n) := mul_le_mul_of_nonneg_left hm b0
  apply le_trans (b := B*δ n) _ (rate.trans (by nlinarith only [mul_nonneg c0 mc]))
  dsimp only [B]
  nlinarith only [mul_le_mul_of_nonneg_right dsq (sq_nonneg c)]

theorem movement_in_probability (hk : 0<k) (α ell : ℝ) (hα : 0<α) (h1 : α≤1) (hl : 0<ell)
    (b : Fin k → ℝ) (bp : ∀ j, 0<b j) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) (y : Space k)
    (frame : ∀ v : Space k, ell*‖v‖^2 ≤ ‖∑ j, (v j*b j) • x j‖^2)
    (s : ∀ n, Params n d → Fin k → Fin n → ℝ) (gs : ∀ n z, gate α b x z (s n z))
    (η : ℝ) (hη : 0<η) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      let F := fun z => residual (leaky α) b x y z
      let J := fun z v => matrixOp (rows (leaky α) b x (z+v) (s n (z+v)))
      let A := fun z => matrixOp (rows (leaky α) b x z (s n z))
      (stdGaussian (Params n d)).real {z |
        ¬Endpoint (F z) (J z) (A z) (‖A z‖^2)⁻¹ (L*scale n)} ≤ η := by
  obtain ⟨L,hL,good⟩ := joint_movement_in_probability hk α ell hα h1 hl b bp x hx y frame s gs η hη
  refine ⟨L,hL,good.mono (fun n bound => ?_)⟩
  apply (measureReal_mono ?_).trans bound
  intro z hz joint
  exact hz joint.squared

end TwoLayerLimit
