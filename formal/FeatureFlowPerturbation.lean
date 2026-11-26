module

public import FeatureFlow
import all FeatureFlow
public import CircleFlowTracking
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Two trainable matrix factors with the Euclidean operator norm. The
population vector field acts on both unrestricted factors simultaneously.
All comparisons below use the maximum of their operator norm distances. -/

@[expose] public section
noncomputable section

open Set Metric Real Filter Topology
open scoped NNReal Matrix Matrix.Norms.L2Operator
namespace FeatureFlowPerturbation

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Factors := Mat × Mat

def prediction (z : Factors) : Mat := z.1*z.2

def field (S : Mat) (z : Factors) : Factors :=
  ((S-prediction z)*star z.2, star z.1*(S-prediction z))

def IsFlow (S : Mat) (z : ℝ → Factors) (T : ℝ) :=
  ∀ t ∈ Icc 0 T, HasDerivAt z (field S (z t)) t

private theorem norm_mul_sub (a b c d : Mat) :
    ‖a*b - c*d‖ ≤ ‖a-c‖*‖b‖ + ‖c‖*‖b-d‖ := by
  rw [show a*b-c*d = (a-c)*b+c*(b-d) by noncomm_ring]
  exact (norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))

theorem prediction_bound {x y : Factors} {R : ℝ} (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
    ‖prediction x - prediction y‖ ≤ (2*R)*‖x-y‖ := by
  have h₁ : ‖x.1-y.1‖ ≤ ‖x-y‖ := norm_fst_le (x-y)
  have h₂ : ‖x.2-y.2‖ ≤ ‖x-y‖ := norm_snd_le (x-y)
  calc
    _ ≤ ‖x.1-y.1‖*‖x.2‖ + ‖y.1‖*‖x.2-y.2‖ := norm_mul_sub ..
    _ ≤ ‖x-y‖*R + R*‖x-y‖ := add_le_add
      (mul_le_mul h₁ ((norm_snd_le _).trans hx) (norm_nonneg _) (norm_nonneg _))
      (mul_le_mul ((norm_fst_le _).trans hy) h₂ (norm_nonneg _) ((norm_nonneg _).trans hy))
    _ = _ := by ring

def constant (S : Mat) (R : ℝ≥0) := ‖S‖₊ + 3*R^2

theorem field_lipschitz (S : Mat) (R : ℝ≥0) :
    LipschitzOnWith (constant S R) (field S) {z : Factors | ‖z‖ ≤ R} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let g (z : Factors) := S-prediction z
  have gx (z : Factors) (hz : ‖z‖ ≤ R) : ‖g z‖ ≤ ‖S‖+R^2 := by
    apply (norm_sub_le ..).trans
    apply add_le_add (le_refl _)
    exact (norm_mul_le ..).trans <| (mul_le_mul ((norm_fst_le _).trans hz)
      ((norm_snd_le _).trans hz) (norm_nonneg _) R.2).trans_eq (sq _).symm
  have dg : ‖g x-g y‖ ≤ (2*R)*‖x-y‖ := by
    rw [show g x-g y = prediction y - prediction x by dsimp [g]; abel, norm_sub_rev]
    exact prediction_bound hx hy
  have da : ‖star x.1-star y.1‖ ≤ ‖x-y‖ := by
    rw [← star_sub,norm_star]; exact norm_fst_le (x-y)
  have dw : ‖star x.2-star y.2‖ ≤ ‖x-y‖ := by
    rw [← star_sub,norm_star]; exact norm_snd_le (x-y)
  rw [dist_eq_norm,dist_eq_norm]
  change max ‖g x * star x.2 - g y * star y.2‖ ‖star x.1 * g x - star y.1 * g y‖ ≤ _
  apply max_le
  · calc
      _ ≤ ‖g x-g y‖*‖star x.2‖ + ‖g y‖*‖star x.2-star y.2‖ := norm_mul_sub ..
      _ ≤ (2*R*‖x-y‖)*R + (‖S‖+R^2)*‖x-y‖ := by
        rw [norm_star]
        gcongr <;> first | exact (norm_snd_le _).trans hx | exact gx y hy
      _ = _ := by simp only [constant,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,
          NNReal.coe_pow,coe_nnnorm]; ring
  · calc
      _ ≤ ‖star x.1-star y.1‖*‖g x‖ + ‖star y.1‖*‖g x-g y‖ := norm_mul_sub ..
      _ ≤ ‖x-y‖*(‖S‖+R^2) + R*(2*R*‖x-y‖) := by
        rw [norm_star]
        gcongr <;> first | exact (norm_fst_le _).trans hy | exact gx x hx
      _ = _ := by simp only [constant,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,
          NNReal.coe_pow,coe_nnnorm]; ring

/-- On any common existence interval with a one-unit reference margin, the
actual perturbed factors remain in the tube and obey the exponential bound.
The network products have distance at most twice the radius times that bound. -/
theorem independent_factor_stability (S : Mat) {z ref : ℝ → Factors} {H : ℝ} (_hH : 0 ≤ H)
    (flow : IsFlow S z H) (aligned : IsFlow S ref H) (R : ℝ≥0)
    (ref_margin : ∀ t ∈ Icc 0 H, ‖ref t‖+1 ≤ R)
    (small : dist (z 0) (ref 0) * exp (constant S R * H) < 1) :
    ∀ t ∈ Icc 0 H,
      dist (z t) (ref t) ≤ dist (z 0) (ref 0) * exp (constant S R * t) ∧
      ‖prediction (z t)-prediction (ref t)‖ ≤
        2*R*(dist (z 0) (ref 0) * exp (constant S R * t)) := by
  let d := fun t => dist (z t) (ref t)
  have hz : ContinuousOn z (Icc 0 H) := fun t ht => (flow t ht).continuousAt.continuousWithinAt
  have hr : ContinuousOn ref (Icc 0 H) := fun t ht => (aligned t ht).continuousAt.continuousWithinAt
  have mem (s : ℝ) (hs : s ∈ Icc 0 H) (hd : d s < 1) : ‖z s‖ ≤ R := by
    have h := norm_sub_norm_le (z s) (ref s)
    have hm := ref_margin s hs
    change dist _ _ < 1 at hd
    rw [dist_eq_norm] at hd
    linarith
  have on_prefix (t : ℝ) (ht : t ∈ Icc 0 H) (hd : ∀ s ∈ Ico 0 t, d s < 1) :
      d t ≤ d 0 * exp (constant S R * t) := by
    have sub : Icc 0 t ⊆ Icc 0 H := Icc_subset_Icc_right ht.2
    have bound := dist_le_of_trajectories_ODE_of_mem (v := fun _ => field S)
      (s := fun _ => {w : Factors | ‖w‖ ≤ R}) (fun _ _ => field_lipschitz S R)
      (hz.mono sub) (fun s hs => (flow s (sub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => mem s (sub (Ico_subset_Icc_self hs)) (hd s hs))
      (hr.mono sub) (fun s hs => (aligned s (sub (Ico_subset_Icc_self hs))).hasDerivWithinAt)
      (fun s hs => by
        change ‖ref s‖ ≤ R
        linarith [ref_margin s (sub (Ico_subset_Icc_self hs))])
      (le_rfl : dist (z 0) (ref 0) ≤ _) t (show t ∈ Icc 0 t from ⟨ht.1,le_rfl⟩)
    simpa [d] using bound
  have continuous_dist : ContinuousOn d (Icc 0 H) := by
    change ContinuousOn (fun t => dist (z t) (ref t)) _
    fun_prop
  have inside := CircleFlowTracking.no_first_exit continuous_dist (ρ := 1) (fun t ht hpre =>
    (on_prefix t ht hpre).trans_lt (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2
        (constant S R).2)) dist_nonneg) small))
  intro t ht
  have b := on_prefix t ht (fun s hs => inside s ⟨hs.1,hs.2.le.trans ht.2⟩)
  have refB : ‖ref t‖ ≤ R := by linarith [ref_margin t ht]
  refine ⟨b,(prediction_bound (mem t ht (inside t ht)) refB).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [d, dist_eq_norm] using b

private theorem first_deriv {z : ℝ → Factors} {v : Factors} {t : ℝ} (h : HasDerivAt z v t) :
    HasDerivAt (fun u => (z u).1) v.1 t :=
  (ContinuousLinearMap.fst ℝ Mat Mat).hasFDerivAt.comp_hasDerivAt t h

private theorem second_deriv {z : ℝ → Factors} {v : Factors} {t : ℝ} (h : HasDerivAt z v t) :
    HasDerivAt (fun u => (z u).2) v.2 t :=
  (ContinuousLinearMap.snd ℝ Mat Mat).hasFDerivAt.comp_hasDerivAt t h

private def flipFactors (z : Factors) : Factors := (star z.2,star z.1)

private theorem flipped_flow {S : Mat} (hS : star S = S) {z : ℝ → Factors} {H : ℝ}
    (hf : IsFlow S z H) : IsFlow S (fun t => flipFactors (z t)) H := by
  intro t ht
  have h := ((second_deriv (hf t ht)).star).prodMk ((first_deriv (hf t ht)).star)
  simpa only [field, prediction, flipFactors, star_mul, star_sub, hS, star_star] using h

/-- A transpose-paired initialization remains paired for the actual coupled
matrix ODE. This follows from uniqueness of the trajectories, using their
operator-norm bound on the finite time interval. -/
theorem balanced_factors {S : Mat} (hS : star S = S) {z : ℝ → Factors} {H : ℝ} (hH : 0 ≤ H)
    (hf : IsFlow S z H) (initial : (z 0).2 = star (z 0).1) :
    ∀ t ∈ Icc 0 H, (z t).2 = star (z t).1 := by
  have hz : ContinuousOn z (Icc 0 H) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := isCompact_Icc.bddAbove_image hz.norm
  have M (t : ℝ) (ht : t ∈ Icc 0 H) : ‖z t‖+1 ≤ (R.toNNReal+1:ℝ≥0) := by
    rw [NNReal.coe_add,NNReal.coe_one]
    exact add_le_add_left ((hR ⟨t,ht,rfl⟩).trans (Real.le_coe_toNNReal R)) _
  have init : flipFactors (z 0) = z 0 := by
    apply Prod.ext <;> simp [flipFactors, initial]
  have compare := independent_factor_stability S hH (flipped_flow hS hf) hf
    (R.toNNReal+1) M (by simp [init])
  intro t ht
  have heq : flipFactors (z t) = z t :=
    dist_le_zero.mp (by simpa only [init, dist_self, zero_mul] using (compare t ht).1)
  exact (congrArg Prod.snd heq).symm

/-- Product coordinates of a balanced actual factor flow solve the Riccati
equation. This includes off-diagonal components for rotated initialization. -/
theorem balanced_product_deriv {S : Mat} (hS : star S = S) {z : ℝ → Factors} {H : ℝ} (hH : 0 ≤ H)
    (hf : IsFlow S z H) (initial : (z 0).2 = star (z 0).1) (t : ℝ) (ht : t ∈ Icc 0 H) :
    let B := prediction (z t)
    HasDerivAt (fun u => prediction (z u)) (S*B+B*S-(B*B+B*B)) t := by
  have bal := balanced_factors hS hH hf initial t ht
  have h := (first_deriv (hf t ht)).mul (second_deriv (hf t ht))
  change HasDerivAt _ _ t
  convert h using 1 <;> try rfl
  dsimp [field,prediction]
  rw [bal,star_star]
  noncomm_ring

private theorem matrix_hasDerivAt {f : ℝ → Mat} {v : Mat} {t : ℝ}
    (h : ∀ i j, HasDerivAt (fun u => f u i j) (v i j) t) : HasDerivAt f v t := by
  let e : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] Mat := Matrix.ofLinearEquiv ℝ |>.toContinuousLinearEquiv
  have h' : HasDerivAt (fun u i j => f u i j) (fun i j => v i j) t :=
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr (h i)
  exact e.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h'

/-- The prescribed precision matrix on both diagonal and off-diagonal entries. -/
def precision (s : Fin 2 → ℝ) (D : Mat) (t : ℝ) : Mat :=
  Matrix.of fun i j => (if i = j then 1/s i else 0) +
    (D i j - (if i = j then 1/s i else 0))*exp (-(s i+s j)*t)

theorem precision_deriv (s : Fin 2 → ℝ) (hs : ∀ i, s i ≠ 0) (D : Mat) (t : ℝ) :
    let S := Matrix.diagonal s
    let P := precision s D t
    HasDerivAt (precision s D) (1+1-(P*S+S*P)) t := by
  apply matrix_hasDerivAt
  intro i j
  have h := FeatureFlow.precision_entry_ode (s i) (s j) (if i=j then 1/s i else 0) (D i j) t
  convert h using 1 <;> try rfl
  simp only [Matrix.add_apply, Matrix.sub_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    precision, Matrix.of_apply,Matrix.one_apply]
  split_ifs with hij
  · subst j
    field_simp [hs i]
    ring
  · ring

/-- The stated precision is the inverse of the product of the actual
balanced factors on every finite interval. The product identity is propagated
by a linear homogeneous differential equation from its value at zero. -/
theorem precision_mul_product {s : Fin 2 → ℝ} (hs : ∀ i, s i ≠ 0) {z : ℝ → Factors} {H : ℝ}
    (hH : 0 ≤ H) (hf : IsFlow (Matrix.diagonal s) z H)
    (initial : (z 0).2 = star (z 0).1) (D : Mat) (inv : D * prediction (z 0) = 1) :
    ∀ t ∈ Icc 0 H, precision s D t * prediction (z t) = 1 := by
  let S := Matrix.diagonal s
  have hS : star S = S := by
    ext i j
    by_cases hij : i=j <;> simp [S, Matrix.star_apply, hij, Ne.symm]
  let B := fun t => prediction (z t)
  let P := precision s D
  let E := fun t => P t * B t - 1
  let V := fun t => E t * S - S * E t - (E t * B t + E t * B t)
  have dB (t : ℝ) (ht : t ∈ Icc 0 H) := balanced_product_deriv hS hH hf initial t ht
  have dE (t : ℝ) (ht : t ∈ Icc 0 H) : HasDerivAt E (V t) t := by
    have h := ((precision_deriv s hs D t).mul (dB t ht)).sub_const (1:Mat)
    convert h using 1
    dsimp [V,E,S,B,P]
    noncomm_ring
  have Bcont : ContinuousOn B (Icc 0 H) := fun t ht => (dB t ht).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := isCompact_Icc.bddAbove_image Bcont.norm
  have zer := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := E) (f' := V) (K := 2*‖S‖+2*R)
    (fun t ht => (dE t ht).continuousAt.continuousWithinAt)
    (fun t ht => (dE t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by
      have p0 : P 0 = D := by ext i j; simp [P, precision]
      simp [E,B,p0,inv])
    (fun t ht => by
      have hr : ‖B t‖ ≤ R := hR ⟨t,Ico_subset_Icc_self ht,rfl⟩
      calc
        ‖V t‖ ≤ (‖E t * S‖+‖S * E t‖) + (‖E t * B t‖+‖E t * B t‖) :=
          (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) (norm_add_le ..))
        _ ≤ (‖E t‖*‖S‖+‖S‖*‖E t‖)+(‖E t‖*R+‖E t‖*R) := by
          gcongr <;> first | apply norm_mul_le | exact (norm_mul_le ..).trans (by gcongr)
        _ = _ := by ring)
  intro t ht
  exact sub_eq_zero.mp (zer t ht)

private theorem entry_le_norm (M : Mat) (i j : Fin 2) : |M i j| ≤ ‖M‖ := by
  let T := Matrix.toEuclideanCLM (𝕜 := ℝ) M
  let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (Pi.single j (1:ℝ))
  calc
    _ = ‖(T x) i‖ := by simp [T,x,Matrix.mulVec_single]
    _ ≤ ‖T x‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
    _ = _ := by simp [T,x,Matrix.l2_opNorm_toEuclideanCLM]

/-- The first nonnegative time when the directional response reaches q*s. -/
def firstTime (b : ℝ → ℝ) (s q : ℝ) := sInf {t | 0 ≤ t ∧ q*s ≤ b t}

/-- A tube about a strictly increasing reference locates the first crossing,
even for perturbed directional responses that need not themselves be monotone. -/
theorem firstTime_bracket {b r : ℝ → ℝ} {s q e lo hi H : ℝ}
    (hlo : 0 ≤ lo) (hlh : lo ≤ hi) (hhi : hi ≤ H) (hs : StrictMono r)
    (rlo : r lo = q*s-e) (rhi : r hi = q*s+e)
    (close : ∀ t ∈ Icc 0 H, |b t-r t| ≤ e) :
    lo ≤ firstTime b s q ∧ firstTime b s q ≤ hi := by
  let K : Set ℝ := {t | 0 ≤ t ∧ q*s ≤ b t}
  have hit : hi ∈ K := by
    refine ⟨hlo.trans hlh,?_⟩
    have h := (abs_le.mp (close hi ⟨hlo.trans hlh,hhi⟩)).1
    linarith
  have lower (x : ℝ) (hx : x ∈ K) : lo ≤ x := by
    by_contra! h
    have bnd := (abs_le.mp (close x ⟨hx.1,h.le.trans (hlh.trans hhi)⟩)).2
    linarith [hs h,hx.2]
  exact ⟨le_csInf ⟨hi,hit⟩ lower,csInf_le ⟨lo,lower⟩ hit⟩

def alignedTime (s k q : ℝ) := log (k*q/(1-q))/(2*s)

theorem alignedTime_exact {s k q : ℝ} (hs : 0 < s) (hk : 0 < k) (hq : 0 < q) (hq' : q < 1) :
    FeatureFlow.aligned s k (alignedTime s k q) = q*s := by
  have hpos : 0 < k*q/(1-q) := by positivity
  have hex : -2*s*alignedTime s k q = -log (k*q/(1-q)) := by
    unfold alignedTime
    field_simp
  rw [FeatureFlow.aligned, hex,Real.exp_neg, Real.exp_log hpos]
  field_simp
  ring

theorem aligned_strictMono {s k : ℝ} (hs : 0 < s) (hk : 0 < k) : StrictMono (FeatureFlow.aligned s k) := by
  intro t u h
  unfold FeatureFlow.aligned
  apply div_lt_div_of_pos_left hs (by positivity)
  have h' : -2*s*u < -2*s*t := by nlinarith [mul_lt_mul_of_pos_left h hs]
  exact add_lt_add_right (mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr h') hk) _

/-- Directional first crossing of the unrestricted perturbed factor flow.
The two endpoints are exact aligned first times, with threshold perturbation
equal to the uniform operator norm error divided by the teacher strength. -/
theorem independent_factor_crossing {S : Mat} {z ref : ℝ → Factors} {H s k q e : ℝ}
    (hH : 0 ≤ H) (flow : IsFlow S z H) (aligned : IsFlow S ref H) (R : ℝ≥0)
    (ref_margin : ∀ t ∈ Icc 0 H, ‖ref t‖+1 ≤ R)
    (small : dist (z 0) (ref 0) * exp (constant S R * H) < 1)
    (error : 2*R*(dist (z 0) (ref 0) * exp (constant S R * H)) ≤ e)
    (i : Fin 2) (hs : 0 < s) (hk : 0 < k)
    (diag : ∀ t ∈ Icc 0 H, prediction (ref t) i i = FeatureFlow.aligned s k t)
    (qlo : 0 < q-e/s) (qlo' : q-e/s < 1) (qhi : 0 < q+e/s) (qhi' : q+e/s < 1)
    (hlo : 0 ≤ alignedTime s k (q-e/s))
    (hlh : alignedTime s k (q-e/s) ≤ alignedTime s k (q+e/s))
    (hhi : alignedTime s k (q+e/s) ≤ H) :
    alignedTime s k (q-e/s) ≤ firstTime (fun t => prediction (z t) i i) s q ∧
      firstTime (fun t => prediction (z t) i i) s q ≤ alignedTime s k (q+e/s) := by
  apply firstTime_bracket (e := e) hlo hlh hhi (aligned_strictMono hs hk)
  · rw [alignedTime_exact hs hk qlo qlo']
    field_simp
  · rw [alignedTime_exact hs hk qhi qhi']
    field_simp
  intro t ht
  rw [←diag t ht]
  apply (entry_le_norm (prediction (z t)-prediction (ref t)) i i).trans
  apply (independent_factor_stability S hH flow aligned R ref_margin small t ht).2.trans
  apply le_trans _ error
  gcongr
  exact ht.2

private theorem pair_sum (f : Fin 2 → ℝ) {i j : Fin 2} (hij : i ≠ j) :
    ∑ k, f k = f i + f j := by
  fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_two, add_comm]

private theorem schur_of_inverse {P B : Mat} (hinv : P*B = 1) {i j : Fin 2} (hij : i ≠ j)
    (hp : P j j ≠ 0) : (P i i - P i j * P j i / P j j) * B i i = 1 := by
  have a := congrArg (fun M : Mat => M i i) hinv
  have b := congrArg (fun M : Mat => M j i) hinv
  change (P*B) i i = (1:Mat) i i at a
  change (P*B) j i = (1:Mat) j i at b
  simp [Matrix.mul_apply, pair_sum _ hij] at a
  simp [Matrix.mul_apply, pair_sum _ hij, hij.symm] at b
  field_simp
  linear_combination P j j*a-P i j*b

/-- An observable crossing of the actual two-factor ODE satisfies the
reciprocal formula used by the signed rotated crossing windows. -/
theorem reciprocalMode_at_crossing {s : Fin 2 → ℝ} (hs : ∀ i, 0 < s i)
    {z : ℝ → Factors} {H : ℝ} (hH : 0 ≤ H) (hf : IsFlow (Matrix.diagonal s) z H)
    (balanced : (z 0).2 = star (z 0).1) (D : Mat) (inv : D*prediction (z 0)=1)
    {i j : Fin 2} (hij : i ≠ j) {a b w q t : ℝ} (ht : t ∈ Icc 0 H)
    (dii : D i i = FeatureFlow.initialPrecision a b w)
    (djj : D j j = FeatureFlow.initialPrecision b a w)
    (dij : D i j * D j i = FeatureFlow.offDiagonalSq a b w)
    (dj : 0 < D j j) (hc : prediction (z t) i i = q*s i) :
    FeatureFlow.reciprocalMode (s i) (s j) a b w t = 1/(q*s i) := by
  let P := precision s D t
  let u := exp (-2*s i*t)
  let v := exp (-2*s j*t)
  have eqdiag (k : Fin 2) : P k k = (1-exp (-2*s k*t))/s k+exp (-2*s k*t)*D k k := by
    simp [P,precision]
    ring
  have eoff : P i j*P j i = u*v*(D i j*D j i) := by
    simp only [P,precision,Matrix.of_apply,hij,hij.symm,↓reduceIte,sub_zero,zero_add,u,v]
    rw [show D i j*exp (-(s i+s j)*t)*(D j i*exp (-(s j+s i)*t)) =
        D i j*D j i*(exp (-(s i+s j)*t)*exp (-(s j+s i)*t)) by ring,
      ← exp_add, ←exp_add, show -(s i+s j)*t+ -(s j+s i)*t = -2*s i*t+ -2*s j*t by ring]
    ring
  have vle : v ≤ 1 := exp_le_one_iff.mpr (by nlinarith [mul_nonneg (hs j).le ht.1])
  have hp : 0 < P j j := by
    rw [eqdiag]
    exact add_pos_of_nonneg_of_pos (div_nonneg (sub_nonneg.mpr vle) (hs j).le) (mul_pos (exp_pos _) dj)
  have h := schur_of_inverse (precision_mul_product (fun k => (hs k).ne') hH hf balanced D inv t ht) hij hp.ne'
  change (P i i - P i j*P j i/P j j)*prediction (z t) i i=1 at h
  rw [hc] at h
  have hn : q*s i ≠ 0 := by intro hz; simp [hz] at h
  apply (eq_div_iff hn).mpr
  rw [←h, eoff, eqdiag, eqdiag, dii, djj, dij]
  unfold FeatureFlow.reciprocalMode
  dsimp [u,v]
  ring

/-- Counterclockwise rotation of the two initial singular directions. -/
def rotation (θ : ℝ) : Mat := !![cos θ, -sin θ; sin θ, cos θ]

def rotatedFactor (θ : ℝ) (p : Fin 2 → ℝ) : Mat :=
  rotation θ * Matrix.diagonal (fun i => sqrt (p i))

def rotatedMatrix (θ : ℝ) (p : Fin 2 → ℝ) : Mat :=
  rotation θ * Matrix.diagonal p * star (rotation θ)

def initialInverse (θ : ℝ) (p : Fin 2 → ℝ) : Mat := rotatedMatrix θ (fun i => 1/p i)

private theorem rotation_orthogonal (θ : ℝ) :
    star (rotation θ) * rotation θ = 1 ∧ rotation θ * star (rotation θ) = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem diag_star (p : Fin 2 → ℝ) : star (Matrix.diagonal p : Mat) = Matrix.diagonal p := by
  ext i j
  by_cases h : i=j <;> simp [Matrix.star_apply,h,Ne.symm]

theorem rotatedFactor_product (p : Fin 2 → ℝ) (hp : ∀ k, 0 ≤ p k) (θ : ℝ) :
    rotatedFactor θ p * star (rotatedFactor θ p) = rotatedMatrix θ p := by
  let D : Mat := Matrix.diagonal fun k => sqrt (p k)
  have hDD : D*D=Matrix.diagonal p := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact Real.mul_self_sqrt (hp k)
  change (rotation θ * D)*star (rotation θ*D) = _
  rw [star_mul,diag_star, ←mul_assoc, mul_assoc (rotation θ), hDD]
  rfl

theorem initialInverse_mul (p : Fin 2 → ℝ) (hp : ∀ k, p k ≠ 0) (θ : ℝ) :
    initialInverse θ p * rotatedMatrix θ p = 1 := by
  have dh : Matrix.diagonal (fun k => 1/p k) * Matrix.diagonal p = (1:Mat) := by
    rw [Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
    congr 1
    funext k
    simp [hp]
  let Q := rotation θ
  obtain ⟨orth,inv⟩ := rotation_orthogonal θ
  change (Q*Matrix.diagonal (fun k => 1/p k)*star Q)*(Q*Matrix.diagonal p*star Q)=1
  calc
    _ = Q*(Matrix.diagonal (fun k => 1/p k)*(star Q*Q)*Matrix.diagonal p)*star Q := by noncomm_ring
    _ = 1 := by rw [show star Q*Q=1 from orth,mul_one,dh,mul_one]; exact inv

private theorem rot_diag (p : Fin 2 → ℝ) (θ : ℝ) {i j : Fin 2} (hij : i≠j) :
    rotatedMatrix θ p i i = FeatureFlow.diagonal (p i) (p j) (sin θ^2) := by
  have hcos : cos θ^2=1-sin θ^2 := by linarith [sin_sq_add_cos_sq θ]
  fin_cases i <;> fin_cases j <;> simp_all [rotatedMatrix,rotation,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.vecMul_diagonal,Matrix.star_apply,FeatureFlow.diagonal] <;>
    first | linear_combination (p 0)*hcos | linear_combination (p 1)*hcos

private theorem rot_off (p : Fin 2 → ℝ) (θ : ℝ) {i j : Fin 2} (hij : i≠j) :
    rotatedMatrix θ p i j*rotatedMatrix θ p j i = (p i-p j)^2*sin θ^2*(1-sin θ^2) := by
  have hcos : cos θ^2=1-sin θ^2 := by linarith [sin_sq_add_cos_sq θ]
  fin_cases i <;> fin_cases j <;> simp_all [rotatedMatrix,rotation,Matrix.mul_apply,
    Fin.sum_univ_two,Matrix.vecMul_diagonal,Matrix.star_apply]
  all_goals rw [←hcos]; ring

/-- Both directional threshold windows for an unrestricted matrix factor
flow with the planar rotation and the prescribed positive initial singular
values. The premise observes only a crossing of the trained network. -/
theorem rotated_factor_crossing {s p : Fin 2 → ℝ} (hs : ∀ k, 0 < s k) (hp : ∀ k, 0 < p k)
    (θ : ℝ) {z : ℝ → Factors} {H : ℝ} (hH : 0 ≤ H) (hf : IsFlow (Matrix.diagonal s) z H)
    (initA : (z 0).1=rotatedFactor θ p) (balanced : (z 0).2=star (z 0).1)
    {i j : Fin 2} (hij : i ≠ j) {q t : ℝ} (hq : 0 < q) (hq' : q < 1)
    (ht : t ∈ Icc 0 H) (hstart : prediction (z 0) i i < q*s i)
    (hc : prediction (z t) i i=q*s i) :
    log ((1 / FeatureFlow.diagonal (p i) (p j) (sin θ^2) - 1/s i)/(1/(q*s i)-1/s i))/(2*s i) ≤ t ∧
    t ≤ log ((FeatureFlow.initialPrecision (p i) (p j) (sin θ^2) - 1/s i)/(1/(q*s i)-1/s i))/(2*s i) := by
  have init : prediction (z 0)=rotatedMatrix θ p := by
    rw [prediction,balanced,initA,rotatedFactor_product p (fun k => (hp k).le)]
  have wlo := sq_nonneg (sin θ)
  have whi : sin θ^2 ≤ 1 := by linarith [sin_sq_add_cos_sq θ,sq_nonneg (cos θ)]
  have inv : initialInverse θ p*prediction (z 0)=1 := by
    rw [init,initialInverse_mul p (fun k => (hp k).ne')]
  have dii := rot_diag (fun k => 1/p k) θ hij
  have djj := rot_diag (fun k => 1/p k) θ hij.symm
  have off := rot_off (fun k => 1/p k) θ hij
  apply FeatureFlow.rotated_crossing_window (hs i) (hs j) (hp i) (hp j) hq hq' wlo whi ht.1
  · rwa [init,rot_diag p θ hij] at hstart
  apply reciprocalMode_at_crossing hs hH hf balanced _ inv hij ht dii djj off _ hc
  rw [show initialInverse θ p j j=_ from djj]
  exact FeatureFlow.diagonal_pos (one_div_pos.mpr (hp j)) (one_div_pos.mpr (hp i)) wlo whi

/-- The exact aligned matrix factors at every real time, for any positive
teacher strengths and nonnegative common initial odds. -/
def alignedFactors (s : Fin 2 → ℝ) (k t : ℝ) : Factors :=
  let A : Mat := Matrix.diagonal fun i => sqrt (FeatureFlow.aligned (s i) k t)
  (A,A)

private theorem aligned_pos {s k : ℝ} (hs : 0 < s) (hk : 0 ≤ k) (t : ℝ) :
    0 < FeatureFlow.aligned s k t := by unfold FeatureFlow.aligned; positivity

theorem aligned_prediction (s : Fin 2 → ℝ) (hs : ∀ i, 0<s i) {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    prediction (alignedFactors s k t)=Matrix.diagonal (fun i => FeatureFlow.aligned (s i) k t) := by
  rw [prediction,alignedFactors, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.mul_self_sqrt (aligned_pos (hs i) hk t).le

theorem aligned_factors_flow (s : Fin 2 → ℝ) (hs : ∀ i, 0 < s i) {k : ℝ} (hk : 0 ≤ k) (H : ℝ) :
    IsFlow (Matrix.diagonal s) (alignedFactors s k) H := by
  intro t _
  let b (u : ℝ) (i : Fin 2) := FeatureFlow.aligned (s i) k u
  let a (u : ℝ) (i : Fin 2) := sqrt (b u i)
  let V : Mat := Matrix.diagonal (fun i => (s i-b t i)*a t i)
  have da (i : Fin 2) : HasDerivAt (fun u => a u i) ((s i-b t i)*a t i) t := by
    have pos := aligned_pos (hs i) hk t
    have h := (FeatureFlow.aligned_ode (s i) k t hk).sqrt pos.ne'
    convert h using 1
    change (s i-b t i)*sqrt (b t i) = 2*b t i*(s i-b t i)/(2*sqrt (b t i))
    apply (eq_div_iff (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr pos).ne')).mpr
    linear_combination (2*(s i-b t i))*Real.sq_sqrt pos.le
  have dA : HasDerivAt (fun u => (Matrix.diagonal (a u):Mat)) V t := by
    apply matrix_hasDerivAt
    intro i j
    by_cases h : i=j
    · subst j
      simpa [V] using da i
    · simpa [V,Matrix.diagonal_apply,h] using hasDerivAt_const (𝕜:=ℝ) t (0:ℝ)
  have idV : field (Matrix.diagonal s) (alignedFactors s k t) = (V,V) := by
    rw [field,aligned_prediction s hs hk]
    simp only [alignedFactors,diag_star]
    apply Prod.ext <;> ext i j <;> by_cases h : i=j <;>
      simp [V,h,a,b,mul_comm]
  rw [idV]
  exact dA.prodMk dA

theorem aligned_factors_bound (s : Fin 2 → ℝ) {smax : ℝ} (hs : ∀ i, 0 < s i)
    (cap : ∀ i, s i ≤ smax) {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    ‖alignedFactors s k t‖ ≤ sqrt smax := by
  change max ‖(Matrix.diagonal fun i => sqrt (FeatureFlow.aligned (s i) k t):Mat)‖ _ ≤ _
  simp only [alignedFactors,max_self, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]
  apply sqrt_le_sqrt
  apply le_trans _ (cap i)
  unfold FeatureFlow.aligned
  apply div_le_self (hs i).le
  linarith [mul_nonneg hk (exp_pos (-2*s i*t)).le]

/-- The reference in the independent-perturbation theorem is the actual
explicit aligned solution. The only trajectory premise concerns the perturbed
network and allows completely independent changes to its two factors. -/
theorem perturbation_from_alignment (s : Fin 2 → ℝ) {smax : ℝ} (hs : ∀ i, 0 < s i)
    (cap : ∀ i, s i ≤ smax) {k : ℝ} (hk : 0 < k) {z : ℝ → Factors} {H q e : ℝ}
    (hH : 0 ≤ H) (flow : IsFlow (Matrix.diagonal s) z H) (i : Fin 2)
    (R : ℝ≥0) (radius : sqrt smax + 1 ≤ R)
    (small : dist (z 0) (alignedFactors s k 0)*exp (constant (Matrix.diagonal s) R*H) < 1)
    (error : 2*R*(dist (z 0) (alignedFactors s k 0)*exp (constant (Matrix.diagonal s) R*H)) ≤ e)
    (qlo : 0 < q-e/s i) (qlo' : q-e/s i < 1) (qhi : 0 < q+e/s i) (qhi' : q+e/s i < 1)
    (hlo : 0 ≤ alignedTime (s i) k (q-e/s i))
    (hlh : alignedTime (s i) k (q-e/s i) ≤ alignedTime (s i) k (q+e/s i))
    (hhi : alignedTime (s i) k (q+e/s i) ≤ H) :
    alignedTime (s i) k (q-e/s i) ≤ firstTime (fun t => prediction (z t) i i) (s i) q ∧
    firstTime (fun t => prediction (z t) i i) (s i) q ≤ alignedTime (s i) k (q+e/s i) := by
  apply independent_factor_crossing hH flow (aligned_factors_flow s hs hk.le H) R _ small error i
    (hs i) hk _ qlo qlo' qhi qhi' hlo hlh hhi
  · intro t _
    linarith [aligned_factors_bound s hs cap hk.le t]
  · intro t _
    simp [aligned_prediction s hs hk.le]


private theorem norm_field (S : Mat) (D : ℝ≥0) {x : Factors} (hx : ‖x‖ ≤ D) :
    ‖field S x‖ ≤ constant S D * D := by
  have zero : field S 0 = 0 := by simp [field,prediction]
  have b := (field_lipschitz S D).dist_le_mul x hx 0 (by simp)
  rw [zero,dist_zero_right,dist_zero_right] at b
  exact b.trans (mul_le_mul_of_nonneg_left hx (constant S D).2)

private def cut (R : ℝ≥0) (x : Factors) := max 0 (min 1 ((R:ℝ)+1-‖x‖))

private theorem cut_lipschitz (R : ℝ≥0) : LipschitzWith 1 (cut R) := by
  have d : LipschitzWith 1 (fun x : Factors => (R:ℝ)+1-‖x‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq,abs_sub_comm,dist_eq_norm] using abs_norm_sub_norm_le x y
  exact (d.const_min 1).const_max 0

private def cutoffField (S : Mat) (R : ℝ≥0) (x : Factors) := cut R x • field S x

private theorem cutoff_eq {S : Mat} {R : ℝ≥0} {x : Factors} (h : ‖x‖ ≤ R) :
    cutoffField S R x = field S x := by
  simp [cutoffField,cut, min_eq_left (show (1:ℝ) ≤ R+1-‖x‖ by linarith)]

private theorem cutoff_bounded (S : Mat) (R : ℝ≥0) (x : Factors) :
    ‖cutoffField S R x‖ ≤ (constant S (R+1) * (R+1) : ℝ≥0) := by
  by_cases hx : ‖x‖ ≤ (R:ℝ)+1
  · have one : |cut R x| ≤ 1 := by rw [abs_of_nonneg (le_max_left ..)]; exact max_le zero_le_one (min_le_left ..)
    change ‖cut R x • field S x‖ ≤ _
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) one).trans (norm_field _ _ (by simpa using hx))
  · simp [cutoffField,cut,max_eq_left (show min 1 ((R:ℝ)+1-‖x‖) ≤ 0 by
      exact (min_le_right ..).trans (by linarith))]
    positivity

private theorem cutoff_lipschitz (S : Mat) (R D : ℝ≥0) :
    LipschitzOnWith (constant S D + constant S D * D) (cutoffField S R)
      {x : Factors | ‖x‖ ≤ D} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have dc := (cut_lipschitz R).dist_le_mul x y
  rw [Real.dist_eq,NNReal.coe_one,one_mul] at dc
  have df := (field_lipschitz S D).dist_le_mul x hx y hy
  rw [dist_eq_norm] at df
  have one : |cut R x| ≤ 1 := by
    rw [abs_of_nonneg (le_max_left ..)]
    exact max_le zero_le_one (min_le_left ..)
  rw [dist_eq_norm]
  change ‖cut R x • field S x - cut R y • field S y‖ ≤ _
  rw [show cut R x • field S x - cut R y • field S y =
      cut R x • (field S x - field S y) + (cut R x - cut R y) • field S y by
    rw [smul_sub,sub_smul]; abel]
  apply (norm_add_le ..).trans
  calc
    _ = |cut R x| * ‖field S x-field S y‖ + |cut R x-cut R y| * ‖field S y‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ 1*(constant S D * dist x y)+dist x y*(constant S D * D) := by
      exact add_le_add (mul_le_mul one df (norm_nonneg _) zero_le_one)
        (mul_le_mul dc (norm_field S D hy) (norm_nonneg _) dist_nonneg)
    _ = _ := by push_cast; ring

/-- Picard's theorem applied to a compactly truncated locally Lipschitz
matrix vector field on an interval whose interior contains the full horizon. -/
private theorem clipped_flow_exists (S : Mat) (R : ℝ≥0) (x : Factors) (H : ℝ) (hH : 0 ≤ H) :
    ∃ z : ℝ → Factors, z 0=x ∧ ∀ t ∈ Icc 0 H, HasDerivAt z (cutoffField S R (z t)) t := by
  let L := constant S (R+1)*(R+1)
  let a : ℝ≥0 := L*(H.toNNReal+1)
  let D : ℝ≥0 := ‖x‖₊+a
  let t₀ : Icc (-1:ℝ) (H+1) := ⟨0,by constructor <;> linarith⟩
  have hf : IsPicardLindelof (fun _ => cutoffField S R) t₀ x a 0 L
      (constant S D + constant S D * D) := by
    constructor
    · intro _ _
      apply (cutoff_lipschitz S R D).mono
      intro y hy
      change ‖y‖ ≤ (D:ℝ)
      have b := norm_sub_norm_le y x
      change dist y x ≤ (a:ℝ) at hy
      rw [dist_eq_norm] at hy
      dsimp [D]
      linarith
    · exact fun _ _ => continuousOn_const
    · exact fun _ _ y _ => cutoff_bounded S R y
    · dsimp [t₀,a]
      simp [max_eq_left hH, max_eq_left (show (1:ℝ) ≤ H+1 by linarith)]
  obtain ⟨z,start,hz⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨z,start,fun t ht => ?_⟩
  have a' : -1<t := by linarith [ht.1]
  have b' : t<H+1 := by linarith [ht.2]
  exact (hz t ⟨a'.le,b'.le⟩).hasDerivAt (Icc_mem_nhds a' b')

private def entries : (Fin 2 → Fin 2 → ℝ) ≃L[ℝ] Mat :=
  Matrix.ofLinearEquiv ℝ |>.toContinuousLinearEquiv

private theorem deriv_entry {f : ℝ → Mat} {v : Mat} {t : ℝ} (hf : HasDerivAt f v t) (i j : Fin 2) :
    HasDerivAt (fun u => f u i j) (v i j) t := by
  have h := entries.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
  have pi : HasDerivAt (fun u i j => f u i j) (fun i j => v i j) t := h
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp pi i) j

private def mass (x : Factors) := ∑ i, ∑ j, (x.1 i j^2+x.2 i j^2)
private def teacherMass (S : Mat) := ∑ i, ∑ j, S i j^2
private def power (x v : Factors) := ∑ i, ∑ j, (2*x.1 i j*v.1 i j+2*x.2 i j*v.2 i j)

private theorem mass_deriv {z : ℝ → Factors} {v : Factors} {t : ℝ} (hz : HasDerivAt z v t) :
    HasDerivAt (fun u => mass (z u)) (power (z t) v) t := by
  unfold mass power
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have h := ((deriv_entry (first_deriv hz) i j).pow 2).add ((deriv_entry (second_deriv hz) i j).pow 2)
  simpa [Pi.add_def,Pi.pow_def] using h

private theorem power_bound (S : Mat) (x : Factors) : power x (field S x) ≤ teacherMass S := by
  have h : power x (field S x) = ∑ i, ∑ j,
      4*prediction x i j*(S i j-prediction x i j) := by
    simp [power,field,prediction,Fin.sum_univ_two,Matrix.mul_apply, Matrix.star_apply]
    ring
  rw [h]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  nlinarith [sq_nonneg (S i j-2*prediction x i j)]

private theorem cutoff_power_bound (S : Mat) (R : ℝ≥0) (x : Factors) :
    power x (cutoffField S R x) ≤ teacherMass S := by
  have h : power x (cutoffField S R x) = cut R x*power x (field S x) := by
    simp [power, cutoffField,Fin.sum_univ_two]
    ring
  rw [h]
  exact (mul_le_mul_of_nonneg_left (power_bound S x) (le_max_left ..)).trans
    (mul_le_of_le_one_left (by unfold teacherMass; positivity) (max_le zero_le_one (min_le_left ..)))

private theorem norm_le_mass (x : Factors) :
    ‖x‖ ≤ ‖entries.toContinuousLinearMap‖*(mass x+1) := by
  have nonneg (i j : Fin 2) : 0 ≤ x.1 i j^2+x.2 i j^2 := by positivity
  have part (i j : Fin 2) : x.1 i j^2+x.2 i j^2 ≤ mass x :=
    (Finset.single_le_sum (fun k _ => nonneg i k) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => nonneg k l)) (Finset.mem_univ i))
  have all : 0 ≤ mass x+1 := by unfold mass; positivity
  have b (M : Mat) (h : ∀ i j, |M i j| ≤ mass x+1) : ‖M‖ ≤ ‖entries.toContinuousLinearMap‖*(mass x+1) := by
    have hj : ‖(fun i j => M i j : Fin 2 → Fin 2 → ℝ)‖ ≤ mass x+1 :=
      (pi_norm_le_iff_of_nonneg all).mpr (fun i => (pi_norm_le_iff_of_nonneg all).mpr (h i))
    exact (entries.toContinuousLinearMap.le_opNorm (fun i j => M i j)).trans
      (mul_le_mul_of_nonneg_left hj (norm_nonneg _))
  apply max_le <;> apply b <;> intro i j <;> apply abs_le.mpr <;>
    constructor <;> nlinarith [part i j,sq_nonneg (x.1 i j-1/2),sq_nonneg (x.1 i j+1/2),
      sq_nonneg (x.2 i j-1/2),sq_nonneg (x.2 i j+1/2),sq_nonneg (x.2 i j),sq_nonneg (x.1 i j)]

/-- Every pair of independently chosen initial matrices admits an actual
factor flow through every prescribed finite training horizon. The Frobenius
square of the factors grows at speed at most the teacher's Frobenius square. -/
theorem exists_factor_flow (S : Mat) (x : Factors) (H : ℝ) (hH : 0 ≤ H) :
    ∃ z : ℝ → Factors, z 0=x ∧ IsFlow S z H := by
  let R := (‖entries.toContinuousLinearMap‖*(mass x+H*teacherMass S+1)).toNNReal
  obtain ⟨z,z0,dz⟩ := clipped_flow_exists S R x H hH
  have en (t : ℝ) (ht : t ∈ Icc 0 H) : mass (z t) ≤ mass x + t*teacherMass S := by
    have deriv (u : ℝ) (hu : u ∈ Icc 0 t) :=
      mass_deriv (dz u ⟨hu.1,hu.2.trans ht.2⟩)
    have fder (u : ℝ) (hu : u ∈ Icc 0 t) : HasDerivAt
        (fun v => v*teacherMass S-mass (z v)) (teacherMass S-power (z u) (cutoffField S R (z u))) u := by
      simpa [Pi.sub_def] using ((hasDerivAt_id u).mul_const (teacherMass S)).sub (deriv u hu)
    have mono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun u hu => (fder u hu).continuousAt.continuousWithinAt)
      (fun u hu => (fder u (interior_subset hu)).hasDerivWithinAt)
      (fun u _ => sub_nonneg.mpr (cutoff_power_bound S R (z u)))
    have b := mono (show 0 ∈ Icc 0 t from ⟨le_rfl,ht.1⟩) ⟨ht.1,le_rfl⟩ ht.1
    simp [z0] at b
    linarith
  refine ⟨z,z0,fun t ht => ?_⟩
  have hm : mass (z t)+1 ≤ mass x+H*teacherMass S+1 := by
    linarith [en t ht,mul_le_mul_of_nonneg_right ht.2 (show 0 ≤ teacherMass S by unfold teacherMass; positivity)]
  have hR : ‖z t‖ ≤ (R:ℝ) := (norm_le_mass (z t)).trans
    ((mul_le_mul_of_nonneg_left hm (norm_nonneg entries.toContinuousLinearMap)).trans (Real.le_coe_toNNReal _))
  rw [←cutoff_eq (S:=S) hR]
  exact dz t ht

private theorem flow_unique (S : Mat) {z w : ℝ → Factors} {H : ℝ} (hH : 0 ≤ H)
    (hz : IsFlow S z H) (hw : IsFlow S w H) (init : z 0=w 0) :
    Set.EqOn z w (Icc 0 H) := by
  have hc : ContinuousOn w (Icc 0 H) := fun t ht => (hw t ht).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := isCompact_Icc.bddAbove_image hc.norm
  have r (t : ℝ) (ht : t ∈ Icc 0 H) : ‖w t‖+1 ≤ (A.toNNReal+1:ℝ≥0) := by
    rw [NNReal.coe_add,NNReal.coe_one]
    exact add_le_add_left ((hA ⟨t,ht,rfl⟩).trans (Real.le_coe_toNNReal A)) _
  have b := independent_factor_stability S hH hz hw _ r (by simp [init])
  intro t ht
  exact dist_le_zero.mp (by simpa [init] using (b t ht).1)

/-- One global forward trajectory from every initial factor pair. Solutions
on overlapping compact intervals agree by uniqueness of the actual ODE. -/
theorem exists_global_factor_flow (S : Mat) (x : Factors) :
    ∃ z : ℝ → Factors, z 0=x ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt z (field S (z t)) t := by
  choose z start sol using fun n : ℕ => exists_factor_flow S x ((n:ℝ)+1) (by positivity)
  let Z := fun t : ℝ => if t ≤ 0 then z 0 t else z ⌈t⌉₊ t
  have agree (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 ((n:ℝ)+1)) : Z t=z n t := by
    by_cases heq : t≤0
    · obtain rfl := le_antisymm heq ht.1
      simp [Z,start]
    · simp only [Z,heq,↓reduceIte]
      apply flow_unique S ht.1 (z:=z ⌈t⌉₊) (w:=z n) _ _ ((start _).trans (start _).symm) ⟨ht.1,le_rfl⟩
      · exact fun u hu => sol _ u ⟨hu.1,hu.2.trans ((Nat.le_ceil t).trans (by linarith))⟩
      · exact fun u hu => sol _ u ⟨hu.1,hu.2.trans ht.2⟩
  refine ⟨Z,by simp [Z,start],fun t ht => ?_⟩
  by_cases ht0 : t=0
  · subst t
    have eq : Z =ᶠ[nhds (0:ℝ)] z 0 := by
      filter_upwards [gt_mem_nhds (show (0:ℝ)<1 by norm_num)] with u hu
      by_cases neg : u≤0
      · simp [Z,neg]
      · exact agree 0 u ⟨le_of_not_ge neg,by simpa using hu.le⟩
    simpa [Z,start] using (sol 0 0 (by norm_num)).congr_of_eventuallyEq eq
  · choose n hn using exists_nat_gt t
    have hp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hn' : t < (n:ℝ)+1 := by linarith
    have eq : Z =ᶠ[nhds t] z n := by
      filter_upwards [Ioo_mem_nhds hp hn'] with u hu using agree n u (Ioo_subset_Icc_self hu)
    rw [eq.eq_of_nhds]
    exact (sol n t ⟨ht,hn'.le⟩).congr_of_eventuallyEq eq

private theorem precision_limit (s : Fin 2 → ℝ) (hs : ∀ i, 0<s i) (D : Mat) (i j : Fin 2) :
    Filter.Tendsto (fun t => precision s D t i j) Filter.atTop
      (nhds (if i=j then 1/s i else 0)) := by
  have a : -(s i+s j)<0 := by linarith [hs i,hs j]
  have e := Real.tendsto_exp_atBot.comp ((Filter.tendsto_id (x:=Filter.atTop (α:=ℝ))).const_mul_atTop_of_neg a)
  simpa [precision,Function.comp_def] using
    (tendsto_const_nhds (f:=Filter.atTop) (x:=if i=j then 1/s i else 0)).add
      (e.const_mul (D i j-(if i=j then 1/s i else 0)))

/-- The trained product converges to the teacher along both diagonal modes
for every global balanced initialization with invertible product. -/
theorem balanced_mode_limit {s : Fin 2 → ℝ} (hs : ∀ i, 0<s i) {z : ℝ → Factors}
    (flow : ∀ t, 0≤t → HasDerivAt z (field (Matrix.diagonal s) (z t)) t)
    (balanced : (z 0).2=star (z 0).1) (D : Mat) (inv : D*prediction (z 0)=1)
    {i j : Fin 2} (hij : i≠j) :
    Filter.Tendsto (fun t => prediction (z t) i i) Filter.atTop (nhds (s i)) := by
  let P := precision s D
  have hdiag (l : Fin 2) : Filter.Tendsto (fun t => P t l l) Filter.atTop (nhds (1/s l)) := by
    simpa [P] using precision_limit s hs D l l
  have p1 : Filter.Tendsto (fun t => P t i j) Filter.atTop (nhds 0) := by
    simpa [P,hij] using precision_limit s hs D i j
  have p2 : Filter.Tendsto (fun t => P t j i) Filter.atTop (nhds 0) := by
    simpa [P,hij.symm] using precision_limit s hs D j i
  let d := fun t => P t i i - P t i j*P t j i/P t j j
  have td : Filter.Tendsto d Filter.atTop (nhds (1/s i)) := by
    simpa [d] using (hdiag i).sub ((p1.mul p2).div (hdiag j) (one_div_ne_zero (hs j).ne'))
  have inverse : Filter.Tendsto (fun t => (d t)⁻¹) Filter.atTop (nhds (s i)) := by
    simpa using td.inv₀ (one_div_ne_zero (hs i).ne')
  apply inverse.congr'
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ),
    (hdiag j).eventually_ne (one_div_ne_zero (hs j).ne')] with t ht hn
  have a := precision_mul_product (fun k => (hs k).ne') ht (fun u hu => flow u hu.1) balanced D inv t ⟨ht,le_rfl⟩
  have b : d t*prediction (z t) i i=1 := schur_of_inverse a hij hn
  exact inv_eq_of_mul_eq_one_right b

private theorem firstTime_crosses {b : ℝ → ℝ} {s q : ℝ} (hs : 0<s) (hq : q<1)
    (hb : ContinuousOn b (Ici 0)) (start : b 0<q*s)
    (lim : Filter.Tendsto b Filter.atTop (nhds s)) :
    0 ≤ firstTime b s q ∧ b (firstTime b s q)=q*s := by
  let K : Set ℝ := {t | 0≤t ∧ q*s≤b t}
  have hq' : q*s<s := by nlinarith
  obtain ⟨u, _,hu⟩ := Filter.Eventually.exists ((Filter.eventually_ge_atTop (0:ℝ)).and
    (lim.eventually_const_lt hq'))
  have ne : K.Nonempty := ⟨u,‹0≤u›,hu.le⟩
  have closed : IsClosed K := hb.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Ici
  have ymin : sInf K ∈ K := closed.csInf_mem ne ⟨0,fun v hv => hv.1⟩
  refine ⟨ymin.1,le_antisymm ?_ ymin.2⟩
  by_contra! higher
  have con := hb.mono (show Icc 0 (sInf K) ⊆ Ici 0 from fun v hv => hv.1)
  obtain ⟨v, hv, eq⟩ := intermediate_value_Ioo ymin.1 con (show q*s ∈ Ioo (b 0) (b (sInf K)) from ⟨start,higher⟩)
  exact (not_le_of_gt hv.2) (csInf_le ⟨0,fun x hx => hx.1⟩ (show v∈K from ⟨hv.1.le,eq.ge⟩))

/-- Every positive-strength rotated matrix orbit reaches its threshold,
and the first attainment satisfies the same crossing window as every later
attainment, without a monotonicity assumption on the rotated response. -/
theorem rotated_first_crossing {s p : Fin 2 → ℝ} (hs : ∀ k, 0<s k) (hp : ∀ k, 0<p k)
    (θ : ℝ) {z : ℝ → Factors}
    (flow : ∀ t, 0≤t → HasDerivAt z (field (Matrix.diagonal s) (z t)) t)
    (initA : (z 0).1=rotatedFactor θ p) (balanced : (z 0).2=star (z 0).1)
    {i j : Fin 2} (hij : i≠j) {q : ℝ} (hq : 0<q) (hq' : q<1)
    (start : prediction (z 0) i i<q*s i) :
    let T := firstTime (fun t => prediction (z t) i i) (s i) q
    prediction (z T) i i=q*s i ∧
    log ((1/FeatureFlow.diagonal (p i) (p j) (sin θ^2)-1/s i)/(1/(q*s i)-1/s i))/(2*s i) ≤ T ∧
    T ≤ log ((FeatureFlow.initialPrecision (p i) (p j) (sin θ^2)-1/s i)/(1/(q*s i)-1/s i))/(2*s i) := by
  let T := firstTime (fun t => prediction (z t) i i) (s i) q
  have inv : initialInverse θ p*prediction (z 0)=1 := by
    rw [prediction,balanced,initA,rotatedFactor_product p (fun k => (hp k).le),
      initialInverse_mul p (fun k => (hp k).ne')]
  have con : ContinuousOn (fun t => prediction (z t) i i) (Ici 0) := by
    intro t ht
    exact (deriv_entry ((first_deriv (flow t ht)).mul (second_deriv (flow t ht))) i i).continuousAt.continuousWithinAt
  obtain ⟨hT,hit⟩ := firstTime_crosses (hs i) hq' con start (balanced_mode_limit hs flow balanced _ inv hij)
  refine ⟨hit,?_⟩
  exact rotated_factor_crossing hs hp θ hT (fun t ht => flow t ht.1) initA balanced hij hq hq'
    ⟨hT,le_rfl⟩ start hit

private theorem alignedTime_deriv {s k u : ℝ} (hs : 0<s) (hk : 0<k) (hu : 0<u) (hu' : u<1) :
    HasDerivAt (alignedTime s k) (1/(2*s*u*(1-u))) u := by
  have h := ((((hasDerivAt_id u).const_mul k).div
    ((hasDerivAt_id u).const_sub 1) (sub_ne_zero.mpr hu'.ne')).log
      (ne_of_gt (div_pos (mul_pos hk hu) (sub_pos.mpr hu')))).div_const (2*s)
  convert h using 1 <;> try rfl
  dsimp
  field_simp
  ring

/-- The quantitative displacement bound for the true first hitting time
whenever the proven interval is centered at the aligned threshold. -/
theorem threshold_displacement {s k q ρ e T : ℝ} (hs : 0<s) (hk : 0<k)
    (he : 0≤e) (hρ : e/s≤ρ) (hl : 0<q-ρ) (hu : q+ρ<1)
    (window : alignedTime s k (q-e/s) ≤ T ∧ T ≤ alignedTime s k (q+e/s)) :
    |T-alignedTime s k q| ≤ e/(2*s^2*(q-ρ)*(1-q-ρ)) := by
  let D := 2*s*(q-ρ)*(1-q-ρ)
  have hden : 0 < 1-q-ρ := by linarith
  have dpos : 0<D := mul_pos (mul_pos (mul_pos (by norm_num) hs) hl) hden
  have ep : 0≤e/s := div_nonneg he hs.le
  have rho : 0≤ρ := ep.trans hρ
  have c (u : ℝ) (u' : u ∈ Icc (q-ρ) (q+ρ)) :
      ‖1/(2*s*u*(1-u))‖ ≤ 1/D := by
    have u0 := hl.trans_le u'.1
    have u1 := u'.2.trans_lt hu
    rw [Real.norm_eq_abs,abs_of_pos (by positivity)]
    apply one_div_le_one_div_of_le dpos
    exact mul_le_mul (mul_le_mul_of_nonneg_left u'.1 (by positivity))
      (by linarith [u'.2]) hden.le (by positivity)
  have lip (v : ℝ) (hv : v∈Icc (q-ρ) (q+ρ)) :
      |alignedTime s k v-alignedTime s k q| ≤ (1/D)*|v-q| := by
    change ‖alignedTime s k v-alignedTime s k q‖ ≤ (1/D)*‖v-q‖
    apply (convex_Icc (q-ρ) (q+ρ)).norm_image_sub_le_of_norm_hasDerivWithin_le (f:=alignedTime s k) (x:=q) (y:=v)
    · intro u h
      exact (alignedTime_deriv hs hk (hl.trans_le h.1) (h.2.trans_lt hu)).hasDerivWithinAt
    · exact c
    · constructor <;> linarith
    · exact hv
  have l := lip (q-e/s) ⟨by linarith,by linarith⟩
  have r := lip (q+e/s) ⟨by linarith,by linarith⟩
  rw [show q-e/s-q= -(e/s) by ring,abs_neg,abs_of_nonneg ep] at l
  rw [add_sub_cancel_left,abs_of_nonneg ep] at r
  rw [show e/(2*s^2*(q-ρ)*(1-q-ρ))=(1/D)*(e/s) by unfold D; field_simp]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp l).1,window.1],by linarith [(abs_le.mp r).2,window.2]⟩

private theorem ratio_aligned {s α q : ℝ} (hs : 0<s) (ha : 0<α) (hq : 0<q) (hq' : q<1) :
    (1/(α*s)-1/s)/(1/(q*s)-1/s) = (1/α-1)*q/(1-q) := by
  have h : 0<1/(q*s)-1/s := sub_pos.mpr (one_div_lt_one_div_of_lt (mul_pos hq hs) (by nlinarith))
  field_simp

private theorem alignedTime_shift {s α q c : ℝ} (hs : 0<s) (ha : 0<α) (ha' : α<1) (hq : 0<q)
    (hq' : q<1) (hc : 0<c) :
    log (((1/(α*s)-1/s)*c)/(1/(q*s)-1/s))/(2*s) =
      alignedTime s (1/α-1) q + log c/(2*s) := by
  rw [show ((1/(α*s)-1/s)*c)/(1/(q*s)-1/s) = ((1/(α*s)-1/s)/(1/(q*s)-1/s))*c by ring,
    ratio_aligned hs ha hq hq',Real.log_mul _ hc.ne',alignedTime,add_div]
  exact (div_pos (mul_pos (sub_pos.mpr (one_lt_one_div ha ha')) hq) (sub_pos.mpr hq')).ne'

/-- The faster teacher direction can only be delayed by rotation. The
delay is at most the displayed positive log shift, with the exact angular
factor. The theorem applies in particular at the first crossing. -/
theorem fast_signed_window {s r α q w t : ℝ} (hs : 0<s) (hr : 0<r) (hrs : r≤s)
    (ha : 0<α) (ha' : α<1) (hq : 0<q) (hq' : q<1) (hw : 0≤w) (hw' : w≤1)
    (window : log ((1/FeatureFlow.diagonal (α*s) (α*r) w-1/s)/(1/(q*s)-1/s))/(2*s) ≤ t ∧
      t ≤ log ((FeatureFlow.initialPrecision (α*s) (α*r) w-1/s)/(1/(q*s)-1/s))/(2*s)) :
    alignedTime s (1/α-1) q ≤ t ∧
      t ≤ alignedTime s (1/α-1) q + log (1+(s-r)*w/((1-α)*r))/(2*s) := by
  have bp := FeatureFlow.diagonal_pos (mul_pos ha hs) (mul_pos ha hr) hw hw'
  have ble : FeatureFlow.diagonal (α*s) (α*r) w ≤ α*s := by
    unfold FeatureFlow.diagonal
    nlinarith [mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hrs)) hw]
  have den : 0 < 1/(q*s)-1/s := sub_pos.mpr (one_div_lt_one_div_of_lt (mul_pos hq hs) (by nlinarith))
  have init : 0 < 1/(α*s)-1/s := sub_pos.mpr (one_div_lt_one_div_of_lt (mul_pos ha hs) (by nlinarith))
  constructor
  · apply le_trans _ window.1
    rw [alignedTime,←ratio_aligned hs ha hq hq']
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply log_le_log (div_pos init den)
    apply div_le_div_of_nonneg_right _ den.le
    exact sub_le_sub_right (one_div_le_one_div_of_le bp ble) _
  · rw [←alignedTime_shift hs ha ha' hq hq'
      (show 0 < 1+(s-r)*w/((1-α)*r) by positivity),
      ←FeatureFlow.fast_coefficient s r α w hs hr ha ha']
    exact window.2

/-- The slower teacher direction can only be advanced. Its negative log
shift uses the true larger starting response of the rotated slow mode. -/
theorem slow_signed_window {s r α q w t : ℝ} (hs : 0<s) (hr : 0<r) (hrs : r≤s)
    (ha : 0<α) (ha' : α<1) (hq : 0<q) (hq' : q<1) (hw : 0≤w) (hw' : w≤1)
    (start : FeatureFlow.diagonal (α*r) (α*s) w < q*r)
    (window : log ((1/FeatureFlow.diagonal (α*r) (α*s) w-1/r)/(1/(q*r)-1/r))/(2*r) ≤ t ∧
      t ≤ log ((FeatureFlow.initialPrecision (α*r) (α*s) w-1/r)/(1/(q*r)-1/r))/(2*r)) :
    alignedTime r (1/α-1) q + log (1-(s-r)*w/((1-α)*(r+(s-r)*w)))/(2*r) ≤ t ∧
    t ≤ alignedTime r (1/α-1) q := by
  have bp := FeatureFlow.diagonal_pos (mul_pos ha hr) (mul_pos ha hs) hw hw'
  have bl : 0 < 1/FeatureFlow.diagonal (α*r) (α*s) w-1/r :=
    sub_pos.mpr (one_div_lt_one_div_of_lt bp (start.trans (by nlinarith)))
  have base : 0<1/(α*r)-1/r := sub_pos.mpr (one_div_lt_one_div_of_lt (mul_pos ha hr) (by nlinarith))
  have slow := FeatureFlow.slow_coefficient s r α w hs hr ha ha' hw hw'
  have hc := (mul_pos_iff_of_pos_left base).mp (slow ▸ bl)
  have du : FeatureFlow.initialPrecision (α*r) (α*s) w ≤ 1/(α*r) := by
    have order := one_div_le_one_div_of_le (mul_pos ha hr) (mul_le_mul_of_nonneg_left hrs ha.le)
    unfold FeatureFlow.initialPrecision FeatureFlow.diagonal
    nlinarith [mul_le_mul_of_nonneg_left order hw]
  have dl : 0 < FeatureFlow.initialPrecision (α*r) (α*s) w-1/r := by
    have d : 0 ≤ FeatureFlow.offDiagonalSq (α*r) (α*s) w := by
      unfold FeatureFlow.offDiagonalSq
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hw) (sub_nonneg.mpr hw')
    have o := FeatureFlow.diagonal_pos (one_div_pos.mpr (mul_pos ha hs)) (one_div_pos.mpr (mul_pos ha hr)) hw hw'
    change 0 < FeatureFlow.initialPrecision (α*s) (α*r) w at o
    have sch := FeatureFlow.rotation_schur (mul_pos ha hr) (mul_pos ha hs) hw hw'
    linarith [div_nonneg d o.le]
  have den : 0 < 1/(q*r)-1/r := sub_pos.mpr (one_div_lt_one_div_of_lt (mul_pos hq hr) (by nlinarith))
  constructor
  · rw [←alignedTime_shift hr ha ha' hq hq' hc,←slow]
    exact window.1
  · apply window.2.trans
    rw [alignedTime,←ratio_aligned hr ha hq hq']
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact log_le_log (div_pos dl den) (div_le_div_of_nonneg_right (sub_le_sub_right du _) den.le)

private theorem time_mono {s k a b : ℝ} (hs : 0<s) (hk : 0<k)
    (ha : 0<a) (ha' : a<1) (hb : 0<b) (hb' : b<1) (h : a≤b) :
    alignedTime s k a≤alignedTime s k b := by
  apply (aligned_strictMono hs hk).le_iff_le.mp
  rw [alignedTime_exact hs hk ha ha',alignedTime_exact hs hk hb hb']
  exact mul_le_mul_of_nonneg_right h hs.le

private theorem time_start {s α q : ℝ} (hs : 0<s) (ha : 0<α) (ha' : α<1)
    (hle : α≤q) (hq : q<1) : 0≤alignedTime s (1/α-1) q := by
  have b0 : FeatureFlow.aligned s (1/α-1) 0 = α*s := by
    simp [FeatureFlow.aligned]; ring
  have hk : 0<1/α-1 := sub_pos.mpr (one_lt_one_div ha ha')
  apply (aligned_strictMono hs hk).le_iff_le.mp
  rw [b0,alignedTime_exact hs hk (ha.trans_le hle) hq]
  exact mul_le_mul_of_nonneg_right hle hs.le

/-- With the paper's common finite horizon, one pair of actual unrestricted
factor trajectories realizes both first-time windows and the two quantitative
displacement estimates simultaneously, for an arbitrary perturbed seed. -/
theorem independent_initial_conditions {s : Fin 2 → ℝ} {smin smax α q ρ e : ℝ}
    (hmin : 0<smin) (range : ∀ i, smin≤s i ∧ s i≤smax)
    (ha : 0<α) (margin : α<q-ρ) (hq : q+ρ<1) (hρ : 0≤ρ) (he : 0≤e)
    (cap : e≤smin*ρ) (x : Factors) (R : ℝ≥0) (radius : sqrt smax+1≤R)
    (small : dist x (alignedFactors s (1/α-1) 0)*
      exp (constant (Matrix.diagonal s) R*alignedTime smin (1/α-1) (q+ρ)) < 1)
    (error : 2*R*(dist x (alignedFactors s (1/α-1) 0)*
      exp (constant (Matrix.diagonal s) R*alignedTime smin (1/α-1) (q+ρ))) ≤ e) :
    ∃ z : ℝ → Factors, z 0=x ∧ (∀ t, 0≤t → HasDerivAt z (field (Matrix.diagonal s) (z t)) t) ∧
      ∀ i, let T := firstTime (fun t => prediction (z t) i i) (s i) q
        alignedTime (s i) (1/α-1) (q-e/s i) ≤ T ∧ T ≤ alignedTime (s i) (1/α-1) (q+e/s i) ∧
        |T-alignedTime (s i) (1/α-1) q| ≤ e/(2*s i^2*(q-ρ)*(1-q-ρ)) := by
  obtain ⟨z,init,hz⟩ := exists_global_factor_flow (Matrix.diagonal s) x
  have ha' : α<1 := by linarith
  have hk : 0<1/α-1 := sub_pos.mpr (one_lt_one_div ha ha')
  have hs (i : Fin 2) := hmin.trans_le (range i).1
  have Q : α≤q+ρ := by linarith
  have H := time_start hmin ha ha' Q hq
  refine ⟨z,init,hz,fun i => ?_⟩
  have er : e/s i ≤ ρ := (div_le_iff₀ (hs i)).mpr (cap.trans <| by nlinarith [mul_le_mul_of_nonneg_right (range i).1 hρ])
  have e₀ : 0≤e/s i := div_nonneg he (hs i).le
  have lo : α≤q-e/s i := by linarith
  have l₁ : q-e/s i<1 := by linarith
  have hi : 0<q+e/s i := by linarith
  have h₁ : q+e/s i<1 := by linarith
  have w := perturbation_from_alignment s hs (fun j => (range j).2) hk H (fun t ht => hz t ht.1) i R radius
    (init ▸ small) (init ▸ error) (ha.trans_le lo) l₁ hi h₁ (time_start (hs i) ha ha' lo l₁)
    (time_mono (hs i) hk (ha.trans_le lo) l₁ hi h₁ (by linarith)) (show _≤_ from le_trans
      (time_mono (hs i) hk hi h₁ (ha.trans_le Q) hq (by linarith)) (by
        unfold alignedTime at H ⊢
        exact div_le_div_of_nonneg_left ((le_div_iff₀ (by positivity)).mp H |> (by simpa using ·))
          (by positivity) (by linarith [(range i).1])))
  exact ⟨w.1,w.2,threshold_displacement (hs i) hk he er (ha.trans margin) hq w⟩

/-- Both signed windows for the same actual globally trained factor pair
at the prescribed rotation, with their first thresholds attained. -/
theorem rotated_signed_first_times {s r α q θ : ℝ} (hr : 0<r) (hrs : r≤s)
    (ha : 0<α) (ha' : α<1) (hq : 0<q) (hq' : q<1)
    (start : α*(r+(s-r)*sin θ^2)<q*r) (haq : α<q) :
    let S : Fin 2 → ℝ := ![s,r]
    let p : Fin 2 → ℝ := fun i => α*S i
    let A := rotatedFactor θ p
    ∃ z : ℝ → Factors, z 0=(A,star A) ∧ (∀ t, 0≤t → HasDerivAt z (field (Matrix.diagonal S) (z t)) t) ∧
      let T (i : Fin 2) := firstTime (fun t => prediction (z t) i i) (S i) q
      prediction (z (T 0)) 0 0=q*s ∧ prediction (z (T 1)) 1 1=q*r ∧
      (alignedTime s (1/α-1) q ≤ T 0 ∧ T 0 ≤ alignedTime s (1/α-1) q+
        log (1+(s-r)*sin θ^2/((1-α)*r))/(2*s)) ∧
      alignedTime r (1/α-1) q+log (1-(s-r)*sin θ^2/((1-α)*(r+(s-r)*sin θ^2)))/(2*r) ≤ T 1 ∧
        T 1 ≤ alignedTime r (1/α-1) q := by
  let S : Fin 2 → ℝ := ![s,r]
  let p : Fin 2 → ℝ := fun i => α*S i
  let A := rotatedFactor θ p
  obtain ⟨z,hz,flow⟩ := exists_global_factor_flow (Matrix.diagonal S) (A,star A)
  have rate (i : Fin 2) : 0<S i := by fin_cases i <;> simp [S] <;> linarith
  have prodpos (i : Fin 2) : 0<p i := mul_pos ha (rate i)
  have bal : (z 0).2=star (z 0).1 := by rw [hz]
  have ia : (z 0).1=A := by rw [hz]
  have init : prediction (z 0)=rotatedMatrix θ p := by
    rw [prediction,bal,ia,rotatedFactor_product _ (fun i => (prodpos i).le)]
  have hw := sq_nonneg (sin θ)
  have hw' : sin θ^2≤1 := by linarith [sin_sq_add_cos_sq θ,sq_nonneg (cos θ)]
  have lower : FeatureFlow.diagonal (α*r) (α*s) (sin θ^2)<q*r := by
    unfold FeatureFlow.diagonal; linarith only [start]
  have st0 : prediction (z 0) 0 0<q*S 0 := by
    rw [init,rot_diag p θ (j:=1) (by decide : (0:Fin 2)≠1)]
    change FeatureFlow.diagonal (α*s) (α*r) (sin θ^2)<q*s
    unfold FeatureFlow.diagonal
    nlinarith [mul_nonneg (mul_nonneg ha.le (sub_nonneg.mpr hrs)) hw,mul_lt_mul_of_pos_right haq (hr.trans_le hrs)]
  have st1 : prediction (z 0) 1 1<q*S 1 := by
    rw [init,rot_diag p θ (j:=0) (by decide : (1:Fin 2)≠0)]
    exact lower
  have fast := rotated_first_crossing rate prodpos θ flow ia bal (by decide : (0:Fin 2)≠1) hq hq' st0
  have slow := rotated_first_crossing rate prodpos θ flow ia bal (by decide : (1:Fin 2)≠0) hq hq' st1
  exact ⟨z,hz,flow,fast.1,slow.1,fast_signed_window (hr.trans_le hrs) hr hrs ha ha' hq hq' hw hw' fast.2,
    slow_signed_window (hr.trans_le hrs) hr hrs ha ha' hq hq' hw hw' lower slow.2⟩

end FeatureFlowPerturbation
