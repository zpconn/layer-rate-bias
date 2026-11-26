module

public import TwoLayerBudget
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

/-! Packed Euclidean parameters, actual Jacobian matrices, and exact forward chords. -/
@[expose] public section
noncomputable section
namespace TwoLayerNetwork
open TwoLayerBudget NonlinearBudget Set
open scoped InnerProductSpace InnerProduct NNReal
variable {n d k : ℕ}
abbrev Params (n d : ℕ) := EuclideanSpace ℝ (Fin n × Fin (d+1))
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def readout (z : Params n d) (i : Fin n) := z (i,0)
def hidden (z : Params n d) (i : Fin n) : Space d := WithLp.toLp 2 (fun j => z (i,j.succ))

theorem radius_identity (z v : Params n d) :
    ∑ i, ((readout z i-readout v i)^2+‖hidden z i-hidden v i‖^2) = ‖z-v‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  rfl

def rawRow (φ : ℝ → ℝ) (b : ℝ) (x : Space d) (a : Fin n → ℝ) (w : Fin n → Space d)
    (s : Fin n → ℝ) : Params n d := WithLp.toLp 2 fun p =>
  Fin.cases (φ (b*inner ℝ (w p.1) x)) (fun j => (b*(a p.1*s p.1))*x j) p.2

theorem row_identity (φ : ℝ → ℝ) (b : ℝ) (x : Space d) (a₀ a : Fin n → ℝ)
    (w₀ w : Fin n → Space d) (s₀ s : Fin n → ℝ) :
    ‖rawRow φ b x a w s - rawRow φ b x a₀ w₀ s₀‖^2 = rowDiff φ b x a₀ a w₀ w s₀ s := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  unfold rowDiff
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ,EuclideanSpace.real_norm_sq_eq]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro j _
  change (b*(a i*s i)*x j-b*(a₀ i*s₀ i)*x j)^2 = (b*(a i*s i-a₀ i*s₀ i)*x j)^2
  ring

def matrixOp (r : Fin k → Params n d) : Params n d →L[ℝ] Space k :=
  (Matrix.toEuclideanLin (fun j p => r j p / Real.sqrt n)).toContinuousLinearMap

theorem matrix_apply (r : Fin k → Params n d) (v : Params n d) (j : Fin k) :
    matrixOp r v j = inner ℝ (r j) v / Real.sqrt n := by
  change (∑ p, r j p / Real.sqrt n * v p) = _
  rw [PiLp.inner_apply,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  change _ = v p * r j p / Real.sqrt n
  ring

theorem frobenius (r r₀ : Fin k → Params n d) (δ : ℝ≥0)
    (mass : ∑ j, ‖r j-r₀ j‖^2 ≤ n*(δ:ℝ)^2) :
    ‖matrixOp r - matrixOp r₀‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ δ.2
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg δ.2 (norm_nonneg v))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have each (j : Fin k) : (((matrixOp r - matrixOp r₀) v) j)^2 ≤
      ‖r j-r₀ j‖^2 * ‖v‖^2 / n := by
    change (matrixOp r v j - matrixOp r₀ v j)^2 ≤ _
    rw [matrix_apply,matrix_apply,← sub_div,← inner_sub_left,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    simpa only [sq_abs,mul_pow] using pow_le_pow_left₀
      (abs_nonneg _) (abs_real_inner_le_norm (r j-r₀ j) v) 2
  apply (Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)).trans
  rw [← Finset.sum_div,← Finset.sum_mul]
  by_cases hn : n = 0
  · simp [hn,sq_nonneg]
  · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn : 0<(n:ℝ))).mpr
    calc _ ≤ (n:ℝ)*(δ:ℝ)^2*‖v‖^2 := mul_le_mul_of_nonneg_right mass (sq_nonneg ‖v‖)
         _ = ((δ:ℝ)*‖v‖)^2*(n:ℝ) := by ring

def residual (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (z₀ v : Params n d) : Space k := WithLp.toLp 2 fun j =>
  pred φ (b j) (x j) (readout (z₀+v)) (hidden (z₀+v)) - y j

def rows (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z : Params n d)
    (s : Fin k → Fin n → ℝ) (j : Fin k) : Params n d :=
  rawRow φ (b j) (x j) (readout z) (hidden z) (s j)

def gate (α : ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z : Params n d)
    (s : Fin k → Fin n → ℝ) := ∀ j i, Slope α (b j*inner ℝ (hidden z i) (x j)) (s j i)

/-- The numerical Jacobian drift of the full matrix follows from the scalar
row estimates for the actual whitened network and an initial margin count. -/
theorem leaky_matrix {α M R ε : ℝ} (δ : ℝ≥0) (α0 : 0 ≤ α) (α1 : α ≤ 1)
    (M0 : 0 ≤ M) (εpos : 0 < ε) (b : Fin k → ℝ) (bp : ∀ j, 0 < b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖ ≤ 1)
    (z₀ z : Params n d) (s₀ s : Fin k → Fin n → ℝ)
    (g₀ : gate α b x z₀ s₀) (g : gate α b x z s)
    (cap : ∀ i, |readout z₀ i| ≤ M) (rad : ‖z-z₀‖ ≤ R)
    (e : ∑ j, 2*(b j)^2*(R^2+M^2*(1-α)^2*
      (((Finset.univ.filter (fun i => |inner ℝ (hidden z₀ i) (x j)| ≤ ε)).card:ℝ)+R^2/ε^2))
      ≤ n*(δ:ℝ)^2) :
    ‖matrixOp (rows (leaky α) b x z s) - matrixOp (rows (leaky α) b x z₀ s₀)‖ ≤ δ := by
  apply frobenius
  apply (Finset.sum_le_sum (s := Finset.univ) (fun j _ => ?_)).trans e
  rw [rows,rows,row_identity]
  exact leaky_row α (b j) M R ε α0 α1 (bp j) M0 εpos (x j) (hx j)
    _ _ _ _ _ _ (g₀ j) (g j) cap (by rw [radius_identity];exact pow_le_pow_left₀ (norm_nonneg _) rad 2)


def rightSlope (α z v : ℝ) : ℝ := if 0 < z then 1 else if z < 0 then α else if 0 ≤ v then 1 else α

theorem right_admissible {α : ℝ} (h : α ≤ 1) (z v : ℝ) : Slope α z (rightSlope α z v) := by
  unfold Slope rightSlope
  split_ifs <;> grind

private theorem leaky_nonpos (α u : ℝ) (hu : u ≤ 0) : leaky α u = α*u := by
  rcases hu.eq_or_lt with rfl|hn
  · simp [leaky]
  · simp [leaky,not_le.mpr hn]

/-- At a kink the right derivative picks the sign of the preactivation's
direction of travel. In particular, a constantly zero preactivation costs zero. -/
theorem leaky_affine_right (α p v t : ℝ) :
    HasDerivWithinAt (fun u : ℝ => leaky α (p+u*v))
      (rightSlope α (p+t*v) v * v) (Ici t) t := by
  have h : HasDerivAt (fun u : ℝ => p+u*v) v t := by
    simpa using ((hasDerivAt_id t).mul_const v).const_add p
  rcases lt_trichotomy 0 (p+t*v) with pos|zero|neg
  · simp only [rightSlope,ite_eq_left pos,one_mul]
    apply (h.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [h.continuousAt.eventually (Ioi_mem_nhds pos)] with u hu
    exact ite_eq_left (le_of_lt hu)
  · have eq : p+t*v=0 := zero.symm
    by_cases hp : 0 ≤ v
    · simp only [rightSlope,eq,lt_self_iff_false,ite_false,ite_eq_left hp,one_mul]
      apply h.hasDerivWithinAt.congr_of_mem _ (by simp)
      intro u hu
      exact ite_eq_left (by nlinarith [mul_nonneg (sub_nonneg.mpr (mem_Ici.mp hu)) hp])
    · simp only [rightSlope,eq,lt_self_iff_false,ite_false,hp]
      apply (h.const_mul α).hasDerivWithinAt.congr_of_mem _ (by simp)
      intro u hu
      have cost := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (mem_Ici.mp hu)) (le_of_not_ge hp)
      exact leaky_nonpos α _ (by nlinarith only [cost,eq])
  · simp only [rightSlope,ite_eq_right (not_lt.mpr neg.le),ite_eq_left neg]
    apply ((h.const_mul α).congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards [h.continuousAt.eventually (Iio_mem_nhds neg)] with u hu
    exact leaky_nonpos α _ (le_of_lt hu)


def pre (b : ℝ) (x : Space d) (z : Params n d) (i : Fin n) := b*inner ℝ (hidden z i) x

theorem hidden_add (z v : Params n d) (i : Fin n) : hidden (z+v) i = hidden z i + hidden v i := rfl

theorem hidden_smul (t : ℝ) (z : Params n d) (i : Fin n) : hidden (t • z) i = t • hidden z i := rfl

theorem pre_line (b : ℝ) (x : Space d) (z v : Params n d) (i : Fin n) (t : ℝ) :
    pre b x (z+t • v) i = pre b x z i + t*pre b x v i := by
  simp [pre,hidden_add,hidden_smul,inner_add_left,real_inner_smul_left]; ring

theorem network_action (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d)
    (z v : Params n d) (s : Fin k → Fin n → ℝ) (j : Fin k) :
    matrixOp (rows φ b x z s) v j =
      (∑ i, (readout v i*φ (pre (b j) (x j) z i)
        +readout z i*s j i*pre (b j) (x j) v i))/Real.sqrt n := by
  rw [matrix_apply,PiLp.inner_apply,Fintype.sum_prod_type]
  apply congrArg (· / Real.sqrt n)
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  apply congrArg₂ (·+·) rfl
  rw [pre,PiLp.inner_apply,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  change v (i,l.succ)*(b j*(readout z i*s j i)*x j l) =
    readout z i*s j i*(b j*(x j l*v (i,l.succ)))
  ring

def dg (α : ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z v : Params n d)
    (j : Fin k) (i : Fin n) := rightSlope α (pre (b j) (x j) z i) (pre (b j) (x j) v i)

theorem network_along {φ : ℝ → ℝ} (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (z₀ z v : Params n d) (t : ℝ) (s : Fin k → Fin n → ℝ)
    (scalar : ∀ j i, HasDerivWithinAt (fun u : ℝ => φ (pre (b j) (x j) (z₀+(z+u • v)) i))
      (s j i*pre (b j) (x j) v i) (Ici t) t) :
    HasDerivWithinAt (fun u : ℝ => residual φ b x y z₀ (z+u • v))
      (matrixOp (rows φ b x (z₀+(z+t • v)) s) v) (Ici t) t := by
  let w := z₀+(z+t • v)
  let X := fun u : ℝ => z₀+(z+u • v)
  have coord (j : Fin k) : HasDerivWithinAt
      (fun u : ℝ => residual φ b x y z₀ (z+u • v) j)
      (matrixOp (rows φ b x w s) v j) (Ici t) t := by
    rw [network_action]
    apply HasDerivWithinAt.sub_const
    apply HasDerivWithinAt.div_const
    apply HasDerivWithinAt.fun_sum
    intro i _
    have ar : HasDerivAt (fun u : ℝ => readout (X u) i) (readout v i) t := by
      change HasDerivAt (fun u : ℝ => z₀ (i,0)+(z (i,0)+u*v (i,0))) (v (i,0)) t
      simpa using (((hasDerivAt_id t).mul_const (v (i,0))).const_add (z (i,0))).const_add (z₀ (i,0))
    convert ar.hasDerivWithinAt.mul (scalar j i) using 1
    · rfl
    · dsimp [w,X]; ring
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm.toContinuousLinearMap
  exact L.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_pi.mpr coord)

theorem network_right (α : ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (y : Space k)
    (z₀ z v : Params n d) (t : ℝ) :
    let w := z₀+(z+t • v)
    let s := dg α b x w v
    HasDerivWithinAt (fun u : ℝ => residual (leaky α) b x y z₀ (z+u • v))
      (matrixOp (rows (leaky α) b x w s) v) (Ici t) t := by
  intro w s
  apply network_along
  intro j i
  let p := pre (b j) (x j) (z₀+z) i
  let d := pre (b j) (x j) v i
  have ps (u : ℝ) : pre (b j) (x j) (z₀+(z+u • v)) i = p+u*d := by
    simpa only [p,d,add_assoc] using pre_line (b j) (x j) (z₀+z) v i u
  have ph := leaky_affine_right α p d t
  simp_rw [← ps] at ph
  exact ph

theorem residual_continuous {φ : ℝ → ℝ} (hc : Continuous φ) (b : Fin k → ℝ)
    (x : Fin k → Space d) (y : Space k) (z₀ : Params n d) : Continuous (residual φ b x y z₀) := by
  unfold residual pred readout hidden
  fun_prop

/-- Every right derivative of the true forward path in a ball can be
bounded using an admissible matrix at the point on the path. -/
theorem chord_secant {F : Params n d → Space k} {A : Params n d →L[ℝ] Space k}
    {δ : ℝ≥0} {R : ℝ} (cont : Continuous F)
    (right : ∀ z v : Params n d, ∀ t : ℝ, ‖z+t • v‖ ≤ R →
      ∃ J : Params n d →L[ℝ] Space k, ‖J-A‖ ≤ δ ∧
      HasDerivWithinAt (fun u : ℝ => F (z+u • v)) (J v) (Ici t) t) :
    ApproximatesLinearOn F A (Metric.closedBall 0 R) δ := by
  intro z hz w hw
  let v := z-w
  let f := fun t : ℝ => F (w+t • v)-t • A v
  have hc : Continuous f := by dsimp [f]; fun_prop
  have localJ (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) := right w v t
    (mem_closedBall_zero_iff.mp ((convex_closedBall (0 : Params n d) R).add_smul_sub_mem hw hz
      ⟨ht.1,ht.2.le⟩))
  let J := fun t : ℝ => if ht : t ∈ Ico (0:ℝ) 1 then (localJ t ht).choose else A
  have hh (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) : ‖J t-A‖ ≤ δ ∧
      HasDerivWithinAt (fun u : ℝ => F (w+u • v)) (J t v) (Ici t) t := by
    simp only [J,dite_eq_left ht]
    exact (localJ t ht).choose_spec
  have der (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1) :
      HasDerivWithinAt f ((J t-A) v) (Ici t) t := by
    convert (hh t ht).2.sub ((hasDerivAt_id t).smul_const (A v)).hasDerivWithinAt using 1
    · rfl
    · simp
  have fin := norm_image_sub_le_of_norm_deriv_right_le_segment hc.continuousOn der
    (fun t ht => ((J t-A).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hh t ht).1 (norm_nonneg v)))
    1 (right_mem_Icc.mpr zero_le_one)
  simpa [f,v,sub_right_comm (F z) (A z-A w) (F w)] using fin

/-- Actual ordinary full-batch GD, from the initialized network. Arbitrary
admissible slopes are allowed in backpropagation, including at zero. -/
theorem leaky_ball {α M R ε h q : ℝ} (δ : ℝ≥0) (α0 : 0 ≤ α) (α1 : α ≤ 1)
    (M0 : 0 ≤ M) (εpos : 0 < ε) (b : Fin k → ℝ) (bp : ∀ j, 0 < b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖ ≤ 1) (y : Space k)
    (z₀ : Params n d) (s : Params n d → Fin k → Fin n → ℝ)
    (g : ∀ z, gate α b x z (s z)) (cap : ∀ i, |readout z₀ i| ≤ M)
    (e : ∑ j, 2*(b j)^2*(R^2+M^2*(1-α)^2*
      (((Finset.univ.filter (fun i => |inner ℝ (hidden z₀ i) (x j)| ≤ ε)).card:ℝ)+R^2/ε^2))
      ≤ n*(δ:ℝ)^2) (hp : 0<h) (q0 : 0≤q) (q1 : q<1) :
    let F := residual (leaky α) b x y z₀
    let J := fun u => matrixOp (rows (leaky α) b x (z₀+u) (s (z₀+u)))
    let A := matrixOp (rows (leaky α) b x z₀ (s z₀))
    ‖linearStep A h‖ + h*(2*‖A‖+δ)*δ ≤ q →
    h*(‖A‖+δ)*‖F 0‖/(1-q) ≤ R → BallControl F J A h R q δ := by
  intro F J A spectrum size
  have close (z : Params n d) (s' : Fin k → Fin n → ℝ) (hs : gate α b x z s')
      (hr : ‖z-z₀‖ ≤ R) := leaky_matrix δ α0 α1 M0 εpos b bp x hx z₀ z (s z₀) s' (g z₀) hs cap hr e
  have lip : LipschitzWith 1 (leaky α) := LipschitzWith.of_dist_le_mul fun a b => by
    simpa [Real.dist_eq] using leaky_lipschitz α a b α0 α1
  have hc := residual_continuous lip.continuous b x y z₀
  refine ⟨hc,hp,q0,q1,chord_secant hc ?_,?_,spectrum,size⟩
  · intro z v t ht
    let w := z₀+(z+t • v)
    let a := dg α b x w v
    refine ⟨matrixOp (rows (leaky α) b x w a),close w a (fun j i => right_admissible α1 _ _) ?_,
      network_right α b x y z₀ z v t⟩
    simpa [w] using ht
  · intro z hz
    exact close _ _ (g _) (by simpa using hz)


def smoothSlopes (g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (z : Params n d)
    (j : Fin k) (i : Fin n) := g (pre (b j) (x j) z i)

/-- Deterministic smooth-network certificate. All uniform analytic estimates
are discharged by global scalar activation constants and the initialization. -/
theorem smooth_ball {M R h q L₁ L₂ : ℝ} (δ : ℝ≥0) (φ g : ℝ → ℝ)
    (diff : ∀ u, HasDerivAt φ (g u) u) (l₁ : 0 ≤ L₁) (l₂ : 0 ≤ L₂) (M0 : 0 ≤ M)
    (glip : ∀ u v, |g u-g v| ≤ L₂*|u-v|) (gb : ∀ u, |g u| ≤ L₁)
    (b : Fin k → ℝ) (bp : ∀ j, 0 ≤ b j) (x : Fin k → Space d) (hx : ∀ j, ‖x j‖ ≤ 1)
    (y : Space k) (z₀ : Params n d) (cap : ∀ i, |readout z₀ i| ≤ M)
    (e : ∑ j, 2*(b j)^2*R^2*(L₁^2+M^2*L₂^2*(b j)^2) ≤ n*(δ:ℝ)^2)
    (hp : 0<h) (q0 : 0≤q) (q1 : q<1) :
    let F := residual φ b x y z₀
    let J := fun u => matrixOp (rows φ b x (z₀+u) (smoothSlopes g b x (z₀+u)))
    let A := matrixOp (rows φ b x z₀ (smoothSlopes g b x z₀))
    ‖linearStep A h‖ + h*(2*‖A‖+δ)*δ ≤ q →
    h*(‖A‖+δ)*‖F 0‖/(1-q) ≤ R → BallControl F J A h R q δ := by
  intro F J A spectrum size
  have lip (u v : ℝ) : |φ u-φ v| ≤ L₁*|u-v| := by
    have H := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x _ => (diff x).hasDerivWithinAt) (fun x _ => gb x) (Set.mem_univ v) (Set.mem_univ u)
    exact H
  have close (u : Params n d) (hr : ‖u‖ ≤ R) : ‖J u-A‖ ≤ δ := by
    apply frobenius
    apply (Finset.sum_le_sum (s := Finset.univ) (fun j _ => ?_)).trans e
    rw [rows,rows,row_identity]
    apply smooth_row φ g (b j) L₁ L₂ M R (bp j) l₁ l₂ M0 lip glip gb (x j) (hx j) _ _ _ _ cap
    rw [radius_identity,add_sub_cancel_left]
    exact pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hc := residual_continuous (continuous_iff_continuousAt.mpr fun u => (diff u).continuousAt) b x y z₀
  refine ⟨hc,hp,q0,q1,chord_secant hc ?_,close,spectrum,size⟩
  intro z v t ht
  refine ⟨J (z+t • v),close _ ht,network_along b x y z₀ z v t _ ?_⟩
  intro j i
  let p := pre (b j) (x j) (z₀+z) i
  let d := pre (b j) (x j) v i
  have ps (u : ℝ) : pre (b j) (x j) (z₀+(z+u • v)) i = p+u*d := by
    simpa only [p,d,add_assoc] using pre_line (b j) (x j) (z₀+z) v i u
  change HasDerivWithinAt _ (g (pre (b j) (x j) (z₀+(z+t • v)) i)*d) _ _
  simp_rw [ps]
  exact ((diff _).comp t (by simpa using ((hasDerivAt_id t).mul_const d).const_add p)).hasDerivWithinAt


theorem transpose_apply (r : Fin k → Params n d) (u : Space k) (p : Fin n × Fin (d+1)) :
    (((matrixOp r)†) u) p = (∑ j, u j*r j p)/Real.sqrt n := by
  let ep : Params n d := EuclideanSpace.single p 1
  have h := (matrixOp r).adjoint_inner_left ep u
  simp only [ep,EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul] at h
  rw [PiLp.inner_apply] at h
  simp only [matrix_apply,EuclideanSpace.inner_single_right,starRingEnd_apply,
    star_trivial,one_mul,Real.inner_apply] at h
  apply h.trans
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The actual two-layer Gram lower bound from the manuscript. A lower frame
bound for the input matrix, the squared initial readout average, and α>0
suffice. The readout-parameter contribution is positive and can be discarded. -/
theorem leaky_gram_lower (α ell : ℝ) (hα : 0≤α) (he : 0≤ell)
    (b : Fin k → ℝ) (x : Fin k → Space d)
    (frame : ∀ y : Space k, ell*‖y‖^2 ≤ ‖∑ j, (y j*b j) • x j‖^2)
    (z : Params n d) (s : Fin k → Fin n → ℝ) (gate' : gate α b x z s) (u : Space k) :
    ell*α^2*((∑ i, (readout z i)^2)/n)*‖u‖^2 ≤ ‖((matrixOp (rows (leaky α) b x z s))†) u‖^2 := by
  let T := matrixOp (rows (leaky α) b x z s)
  let v := (T†) u
  let w : Fin n → Space k := fun i => WithLp.toLp 2 (fun j => u j*s j i)
  have lw (i : Fin n) : α^2*‖u‖^2 ≤ ‖w i‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    change α^2*(u j)^2 ≤ (u j*s j i)^2
    rw [mul_pow,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hα (gate' j i).1 2) (sq_nonneg _)
  have block (i : Fin n) : hidden v i =
      ((readout z i)/Real.sqrt n) • (∑ j, (w i j*b j) • x j) := by
    ext l
    change ((T†) u) (i,l.succ) = _
    rw [show T = _ from rfl,transpose_apply,Finset.sum_div]
    have proj (f : Fin k → Space d) : (∑ j, f j) l = ∑ j, f j l :=
      map_sum (EuclideanSpace.proj l : Space d →L[ℝ] ℝ) f Finset.univ
    simp only [PiLp.smul_apply,proj,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    change u j*(b j*(readout z i*s j i)*x j l)/Real.sqrt n =
      readout z i/Real.sqrt n*((u j*s j i*b j)*x j l)
    ring
  have one (i : Fin n) : (readout z i)^2/n*(ell*(α^2*‖u‖^2)) ≤ ‖hidden v i‖^2 := by
    rw [block,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (lw i) he).trans (frame (w i))) (by positivity)
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => one i)
  rw [← Finset.sum_mul,← Finset.sum_div] at total
  have decomp := radius_identity v 0
  simp only [show readout (0 : Params n d) = 0 from rfl,
    show hidden (0 : Params n d) = 0 from rfl,Pi.zero_apply,sub_zero,Finset.sum_add_distrib] at decomp
  have pos := Finset.sum_nonneg (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => sq_nonneg (readout v i))
  change _ ≤ ‖v‖^2
  linarith only [total,decomp,pos]

end TwoLayerNetwork
