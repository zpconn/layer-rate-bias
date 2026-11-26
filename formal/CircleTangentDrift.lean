module

public import CircleFlowPath
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Deriv.Prod
import all CircleFlowPath
import Mathlib.Tactic

/-! Movement of the finite ReLU Jacobian under a relative per-neuron tube.
Cartesian coordinates and the admissible gates are those of the actual
weighted trajectory in `CircleFlowPath`. The two arguments of an entry can
even be evaluated at different points of the same tube. -/
public section
noncomputable section
namespace CircleTangentDrift
open CircleFlowPath Real MeasureTheory Set
variable {m N : ℕ}

def length (z : State m) (j : Fin m) := sqrt (∑ k : Fin 3, z (j,k)^2)
def Tube (ρ : ℝ) (z₀ z : State m) := ∀ j, length (z-z₀) j ≤ ρ*length z₀ j
def UnitInput (x : ℝ × ℝ) := x.1^2 + x.2^2 ≤ 1
def dot (x y : ℝ × ℝ) := x.1*y.1+x.2*y.2

def marginFlag (z₀ : State m) (ρ : ℝ) (x : ℝ × ℝ) (j : Fin m) : ℝ :=
  if |pre z₀ j x| ≤ ρ*length z₀ j then 1 else 0

def meanEnergy (z : State m) := (∑ j, length z j^2) / m
def marginMass (z : State m) (ρ : ℝ) (x : ℝ × ℝ) :=
  (∑ j, length z j^2 * marginFlag z ρ x j) / m

/-- Entry of `J(z) Dτ J(v)ᵀ`, including both width normalizations. -/
def entry (τ : ℝ) (z v : State m) (x y : ℝ × ℝ) (s t : Fin m → ℝ) :=
  let c := 1/sqrt m
  pair (row c z x s) (fun p => rate τ p * row c v y t p)

def atom (τ : ℝ) (z v : State m) (x y : ℝ × ℝ) (s t : Fin m → ℝ) (j : Fin m) :=
  max (pre z j x) 0 * max (pre v j y) 0 +
  τ*(z (j,0)*v (j,0))*(s j*t j)*(dot x y)

theorem entry_sum (hm : 0 < m) (τ : ℝ) (z v : State m) (x y : ℝ × ℝ) (s t : Fin m → ℝ) :
    entry τ z v x y s t = (∑ j, atom τ z v x y s t j) / m := by
  have h : (0:ℝ) < m := by exact_mod_cast hm
  simp only [entry, pair, Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp [Fin.sum_univ_three, row, rate, atom, dot]
  field_simp [ne_of_gt h, (sqrt_pos.mpr h).ne']
  rw [sq_sqrt h.le]
  ring

theorem length_sq (z : State m) (j : Fin m) :
    length z j ^ 2 = z (j,0)^2+z (j,1)^2+z (j,2)^2 := by
  rw [length, sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), Fin.sum_univ_three]

theorem readout_bound (z : State m) (j : Fin m) : |z (j,0)| ≤ length z j := by
  apply (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ length z j from sqrt_nonneg _)).mp
  rw [sq_abs, length_sq]
  nlinarith [sq_nonneg (z (j,1)), sq_nonneg (z (j,2))]

theorem pre_bound (z : State m) (j : Fin m) (x : ℝ × ℝ) (hx : UnitInput x) :
    |pre z j x| ≤ length z j := by
  apply (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ length z j from sqrt_nonneg _)).mp
  rw [sq_abs, length_sq, pre]
  change x.1^2+x.2^2 ≤ 1 at hx
  nlinarith [sq_nonneg (x.1*z (j,2)-x.2*z (j,1)), sq_nonneg (z (j,0)),
    mul_nonneg (sub_nonneg.mpr hx) (add_nonneg (sq_nonneg (z (j,1))) (sq_nonneg (z (j,2))))]

private theorem pre_motion (z₀ z : State m) (x : ℝ × ℝ) (j : Fin m) (hx : UnitInput x)
    {ρ : ℝ} (tube : Tube ρ z₀ z) : |pre z j x-pre z₀ j x| ≤ ρ*length z₀ j := by
  have id : pre (z-z₀) j x = pre z j x - pre z₀ j x := by simp [pre]; ring
  rw [← id]
  exact (pre_bound _ _ _ hx).trans (tube j)

private theorem dot_bound {x y : ℝ × ℝ} (hx : UnitInput x) (hy : UnitInput y) :
    |dot x y| ≤ 1 := by
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  rw [sq_abs, dot]
  unfold UnitInput at hx hy
  nlinarith [sq_nonneg (x.1*y.2-x.2*y.1),
    mul_le_mul hx hy (add_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one]

/-- Every change of a compatible gate, including intermediate slopes at a
kink, is charged to its initial weighted near-margin event. -/
theorem gate_motion {z₀ z : State m} {x : ℝ × ℝ} {j : Fin m} {g₀ g ρ : ℝ}
    (hx : UnitInput x) (tube : Tube ρ z₀ z)
    (a₀ : Admissible (pre z₀ j x) g₀) (a : Admissible (pre z j x) g) :
    |g-g₀| ≤ marginFlag z₀ ρ x j := by
  unfold marginFlag
  split_ifs with near
  · exact abs_le.mpr ⟨by linarith [a.1,a₀.2.1], by linarith [a.2.1,a₀.1]⟩
  · have move := abs_le.mp (pre_motion z₀ z x j hx tube)
    have pos := (abs_nonneg _).trans (pre_motion z₀ z x j hx tube)
    rcases le_or_gt 0 (pre z₀ j x) with h | h
    · rw [abs_of_nonneg h] at near
      simp [a.2.2.1 (by linarith), a₀.2.2.1 (by linarith)]
    · rw [abs_of_neg h] at near
      simp [a.2.2.2 (by linarith), a₀.2.2.2 h]

private theorem relu_motion (a b : ℝ) : |max a 0-max b 0| ≤ |a-b| := by
  rcases le_total 0 a with ha|ha <;> rcases le_total 0 b with hb|hb <;>
    simp [ha, hb] <;> grind [abs_le]

private theorem product_motion {a b a₀ b₀ L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (ha : |a-a₀| ≤ ρ*L) (hb : |b-b₀| ≤ ρ*L) (ha₀ : |a₀| ≤ L) (hb₀ : |b₀| ≤ L) :
    |a*b-a₀*b₀| ≤ (2*ρ+ρ^2)*L^2 := by
  have bcap := (abs_sub_le b b₀ 0).trans (add_le_add hb (by simpa using hb₀))
  rw [sub_zero] at bcap
  rw [show a*b-a₀*b₀ = (a-a₀)*b+a₀*(b-b₀) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have prod₁ := mul_le_mul ha bcap (abs_nonneg b) (mul_nonneg hρ hL)
  have prod₂ := mul_le_mul ha₀ hb (abs_nonneg _) hL
  linarith

private theorem gate_product {a b a₀ b₀ u v : ℝ}
    (ha : |a-a₀| ≤ u) (hb : |b-b₀| ≤ v)
    (hb1 : |b| ≤ 1) (ha1 : |a₀| ≤ 1) : |a*b-a₀*b₀| ≤ u+v := by
  rw [show a*b-a₀*b₀=(a-a₀)*b+a₀*(b-b₀) by ring]
  apply (abs_add_le _ _).trans
  simp only [abs_mul]
  have h1 := mul_le_mul ha hb1 (abs_nonneg _) ((abs_nonneg _).trans ha)
  have h2 := mul_le_mul ha1 hb (abs_nonneg _) zero_le_one
  linarith

/-- Displacement costs one product error per parameter block and one
initial-margin indicator per gate. No changes are counted on the basis of
the final signs or a selected derivative convention at zero. -/
theorem readout_atom_drift {τ C ρ : ℝ} {z₀ z v : State m} {x y : ℝ × ℝ}
    {s t s₀ t₀ : Fin m → ℝ} (j : Fin m)
    (hC : 1 ≤ C) (hτ : |τ| ≤ C) (hρ : 0 ≤ ρ) (hx : UnitInput x) (hy : UnitInput y)
    (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v)
    (sx : Admissible (pre z j x) (s j)) (sy : Admissible (pre v j y) (t j))
    (sx₀ : Admissible (pre z₀ j x) (s₀ j)) (sy₀ : Admissible (pre z₀ j y) (t₀ j)) :
    |atom τ z v x y s t j - atom τ z₀ z₀ x y s₀ t₀ j| ≤
      C*((4*ρ+2*ρ^2)*length z₀ j^2 + z₀ (j,0)^2*marginFlag z₀ ρ x j +
          z₀ (j,0)^2*marginFlag z₀ ρ y j) := by
  let L := length z₀ j
  let b := (2*ρ+ρ^2)*L^2
  have hL : 0 ≤ L := sqrt_nonneg _
  have bpos : 0 ≤ b := by dsimp [b]; positivity
  have fm {w : State m} {u : ℝ × ℝ} (hw : Tube ρ z₀ w) (hu : UnitInput u) :
      |max (pre w j u) 0-max (pre z₀ j u) 0| ≤ ρ*L :=
    (relu_motion _ _).trans (pre_motion _ _ _ _ hu hw)
  have fb (u : ℝ × ℝ) (hu : UnitInput u) : |max (pre z₀ j u) 0| ≤ L := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le ((le_abs_self _).trans (pre_bound _ _ _ hu)) hL
  have feature := product_motion hL hρ (fm tz hx) (fm tv hy) (fb x hx) (fb y hy)
  have wm (w : State m) (hw : Tube ρ z₀ w) : |w (j,0)-z₀ (j,0)| ≤ ρ*L :=
    (readout_bound (w-z₀) j).trans (hw j)
  have weights := product_motion hL hρ (wm z tz) (wm v tv) (readout_bound z₀ j) (readout_bound z₀ j)
  have gates := gate_product (gate_motion hx tz sx₀ sx) (gate_motion hy tv sy₀ sy)
    (by rw [abs_of_nonneg sy.1]; exact sy.2.1) (by rw [abs_of_nonneg sx₀.1]; exact sx₀.2.1)
  have active : |s j*t j| ≤ 1 := by
    rw [abs_mul,abs_of_nonneg sx.1,abs_of_nonneg sy.1]
    exact (mul_le_mul sx.2.1 sy.2.1 sy.1 zero_le_one).trans_eq (by ring)
  let h := z (j,0)*v (j,0)*(s j*t j)-z₀ (j,0)*z₀ (j,0)*(s₀ j*t₀ j)
  have hidden : |h| ≤ b + z₀ (j,0)^2*(marginFlag z₀ ρ x j + marginFlag z₀ ρ y j) := by
    change |z (j,0)*v (j,0)*(s j*t j)-z₀ (j,0)*z₀ (j,0)*(s₀ j*t₀ j)| ≤ _
    rw [show z (j,0)*v (j,0)*(s j*t j)-z₀ (j,0)*z₀ (j,0)*(s₀ j*t₀ j) =
      (z (j,0)*v (j,0)-z₀ (j,0)*z₀ (j,0))*(s j*t j)+
        (z₀ (j,0)*z₀ (j,0))*(s j*t j-s₀ j*t₀ j) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul (z₀ (j,0)*z₀ (j,0))]
    have hw : |z (j,0)*v (j,0)-z₀ (j,0)*z₀ (j,0)| * |s j*t j| ≤ b :=
      (mul_le_mul weights active (abs_nonneg _) bpos).trans_eq (mul_one _)
    exact add_le_add hw (by simpa [← sq,abs_of_nonneg (sq_nonneg (z₀ (j,0)))] using
      mul_le_mul_of_nonneg_left gates (sq_nonneg (z₀ (j,0))))
  let F := max (pre z j x) 0 * max (pre v j y) 0 -
        max (pre z₀ j x) 0 * max (pre z₀ j y) 0
  have ident : atom τ z v x y s t j - atom τ z₀ z₀ x y s₀ t₀ j =
      F+τ*h*dot x y := by dsimp [atom,F,h]; ring
  have hh := mul_le_mul hτ hidden (abs_nonneg _) (by linarith : 0 ≤ C)
  have hidden' := mul_le_mul hh (dot_bound hx hy) (abs_nonneg _)
    ((mul_nonneg (abs_nonneg τ) (abs_nonneg h)).trans hh)
  rw [ident]
  apply (abs_add_le _ _).trans
  change |F| + |τ*h*dot x y| ≤ _
  rw [abs_mul,abs_mul]
  have feature' : |F| ≤ C*b := feature.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hC) bpos])
  apply (add_le_add feature' hidden').trans_eq
  dsimp [b,L]
  ring

/-- The coarser length-weighted estimate follows by bounding the initial readout
by its full neuron length. -/
theorem atom_drift {τ C ρ : ℝ} {z₀ z v : State m} {x y : ℝ × ℝ}
    {s t s₀ t₀ : Fin m → ℝ} (j : Fin m)
    (hC : 1 ≤ C) (hτ : |τ| ≤ C) (hρ : 0 ≤ ρ) (hx : UnitInput x) (hy : UnitInput y)
    (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v)
    (sx : Admissible (pre z j x) (s j)) (sy : Admissible (pre v j y) (t j))
    (sx₀ : Admissible (pre z₀ j x) (s₀ j)) (sy₀ : Admissible (pre z₀ j y) (t₀ j)) :
    |atom τ z v x y s t j - atom τ z₀ z₀ x y s₀ t₀ j| ≤
      C*((4*ρ+2*ρ^2)*length z₀ j^2 + length z₀ j^2*marginFlag z₀ ρ x j +
          length z₀ j^2*marginFlag z₀ ρ y j) := by
  have a₀ := pow_le_pow_left₀ (abs_nonneg _) (readout_bound z₀ j) 2
  rw [sq_abs] at a₀
  have pos (w) : 0 ≤ marginFlag z₀ ρ w j := by unfold marginFlag; split <;> norm_num
  exact (readout_atom_drift j hC hτ hρ hx hy tz tv sx sy sx₀ sy₀).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right a₀ (pos x)))
        (mul_le_mul_of_nonneg_right a₀ (pos y))) (by linarith))

/-- Finite average of the Jacobian products with their actual width scaling. -/
theorem entry_drift {τ C ρ : ℝ} {z₀ z v : State m} {x y : ℝ × ℝ}
    {s t s₀ t₀ : Fin m → ℝ} (hm : 0 < m) (hC : 1 ≤ C) (hτ : |τ| ≤ C) (hρ : 0 ≤ ρ)
    (hx : UnitInput x) (hy : UnitInput y) (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v)
    (sx : ∀ j, Admissible (pre z j x) (s j)) (sy : ∀ j, Admissible (pre v j y) (t j))
    (sx₀ : ∀ j, Admissible (pre z₀ j x) (s₀ j)) (sy₀ : ∀ j, Admissible (pre z₀ j y) (t₀ j)) :
    |entry τ z v x y s t - entry τ z₀ z₀ x y s₀ t₀| ≤
      C*((4*ρ+2*ρ^2)*meanEnergy z₀ + marginMass z₀ ρ x + marginMass z₀ ρ y) := by
  rw [entry_sum hm,entry_sum hm, ← sub_div, ← Finset.sum_sub_distrib,abs_div,abs_of_nonneg (show 0 ≤ (m:ℝ) from Nat.cast_nonneg m)]
  apply (div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (fun j _ => atom_drift j hC hτ hρ hx hy tz tv (sx j) (sy j) (sx₀ j) (sy₀ j)))) (Nat.cast_nonneg m)).trans_eq
  simp only [meanEnergy, marginMass, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

/-- A normalized scalar row on the RMS grid, represented on Euclidean
coordinates r/√N. Dividing its coefficients by √N makes its value the
average of the original row against the unscaled residual. -/
def rowOp (h : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  innerSL ℝ (WithLp.toLp 2 (fun i => h i / sqrt N) : EuclideanSpace ℝ (Fin N))

def gramOp (A : Matrix (Fin N) (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (fun i j => A i j / N)

theorem rowOp_apply (h : Fin N → ℝ) (r : EuclideanSpace ℝ (Fin N)) :
    rowOp h r = (∑ i, h i * r i) / sqrt N := by
  rw [rowOp, innerSL_apply_apply, PiLp.inner_apply,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change r i * (h i / sqrt N) = _
  ring

theorem rowOp_norm {h : Fin N → ℝ} {e : ℝ} (hn : 0 < N) (he : 0 ≤ e)
    (entries : ∀ i, |h i| ≤ e) : ‖rowOp h‖ ≤ e := by
  let w : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => h i / sqrt N)
  have hc : (0:ℝ) < N := by exact_mod_cast hn
  have hs : ‖w‖ ≤ e := by
    apply (sq_le_sq₀ (norm_nonneg _) he).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ = (∑ i, (h i)^2) / N := by
        simp only [w, div_pow, sq_sqrt hc.le, Finset.sum_div]
      _ ≤ (∑ _i : Fin N, e^2) / N := by
        apply div_le_div_of_nonneg_right _ hc.le
        apply Finset.sum_le_sum
        intro i _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (entries i) 2
      _ = _ := by simp; field_simp
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro r
  exact (abs_real_inner_le_norm w r).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))

theorem gramOp_apply (A : Matrix (Fin N) (Fin N) ℝ) (r : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    gramOp A r i = (∑ j, A i j * r j) / N := by
  change (∑ j, (A i j / N)*r j) = _
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- An entrywise radius e costs at most e in normalized grid operator
norm. In particular there is no factor N after the gradient normalization. -/
theorem gramOp_norm {A : Matrix (Fin N) (Fin N) ℝ} {e : ℝ} (hn : 0 < N) (he : 0 ≤ e)
    (entries : ∀ i j, |A i j| ≤ e) : ‖gramOp A‖ ≤ e := by
  have hc : (0:ℝ) < N := by exact_mod_cast hn
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro r
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg he (norm_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have each (i : Fin N) : (gramOp A r i)^2 ≤ (e*‖r‖)^2/N := by
    have h := ((rowOp (A i)).le_opNorm r).trans
      (mul_le_mul_of_nonneg_right (rowOp_norm hn he (entries i)) (norm_nonneg r))
    rw [Real.norm_eq_abs, rowOp_apply] at h
    have hh := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs,div_pow,sq_sqrt hc.le] at hh
    rw [gramOp_apply, div_pow, sq]
    convert div_le_div_of_nonneg_right hh hc.le using 1
    ring
  calc
    _ ≤ ∑ _i : Fin N, (e*‖r‖)^2/N := Finset.sum_le_sum (fun i _ => each i)
    _ = _ := by simp; field_simp

/-- Both learning rates obey this single budget when the initial entry is
within 2u of its population expectation. -/
theorem two_rate_budget {ρ u E M₁ M₂ a a₀ aPop : ℝ} (hρ : 0 ≤ ρ) (small : ρ ≤ 1)
    (energy : E ≤ 4) (margin₁ : M₁ ≤ 3*ρ+u) (margin₂ : M₂ ≤ 3*ρ+u)
    (move : |a-a₀| ≤ 2*((4*ρ+2*ρ^2)*E+M₁+M₂)) (init : |a₀-aPop| ≤ 2*u) :
    |a-aPop| ≤ 2*(30*ρ+3*u) := by
  apply (abs_sub_le _ a₀ _).trans
  have hh := mul_le_mul_of_nonneg_left energy (show 0 ≤ 4*ρ+2*ρ^2 by positivity)
  nlinarith [mul_nonneg hρ (sub_nonneg.mpr small)]

def actualGate (a : ℝ) : ℝ := if 0 < a then 1 else 0

theorem actualGate_admissible (a : ℝ) : Admissible a (actualGate a) := by
  unfold Admissible actualGate
  split_ifs <;> grind

def phase (u : ℝ) : ℝ × ℝ := (cos (2*π*u),sin (2*π*u))

theorem phase_unit (u : ℝ) : UnitInput (phase u) := (cos_sq_add_sin_sq _).le

theorem grid_unit (i : Fin N) : UnitInput (circleInput N i) := by
  have h := CircleEscape.grid_norm N i
  change (CircleEscape.gridPoint N i).re^2+(CircleEscape.gridPoint N i).im^2 ≤ 1
  have iden : (CircleEscape.gridPoint N i).re^2+(CircleEscape.gridPoint N i).im^2 =
      ‖CircleEscape.gridPoint N i‖^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  rw [iden,h]
  norm_num

/-- Integration over one turn is a probability measure. -/
def angularLaw : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure angularLaw := ⟨by simp [angularLaw, Real.volume_Ioc]⟩

def angleEntry (τ : ℝ) (z v : State m) (y : ℝ × ℝ) (t : Fin m → ℝ) (u : ℝ) :=
  entry τ z v (phase u) y (fun j => actualGate (pre z j (phase u))) t

def meanEntry (τ : ℝ) (z v : State m) (y : ℝ × ℝ) (t : Fin m → ℝ) :=
  ∫ u, angleEntry τ z v y t u ∂angularLaw

def angularMargin (z : State m) (ρ : ℝ) := ∫ u, marginMass z ρ (phase u) ∂angularLaw

private theorem pre_phase_cont (z : State m) (j : Fin m) : Continuous (fun u => pre z j (phase u)) := by
  unfold pre phase
  fun_prop

private theorem gate_meas (z : State m) (j : Fin m) :
    Measurable (fun u => actualGate (pre z j (phase u))) := by
  unfold actualGate
  exact Measurable.ite (measurableSet_lt measurable_const (pre_phase_cont z j).measurable)
    measurable_const measurable_const

private theorem atom_integrable (τ : ℝ) (z v : State m) (y : ℝ × ℝ) (t : Fin m → ℝ) (j : Fin m) :
    Integrable (fun u => atom τ z v (phase u) y (fun j => actualGate (pre z j (phase u))) t j) angularLaw := by
  let a := |max (pre v j y) 0|
  let b := |τ*(z (j,0)*v (j,0))| * |t j| * (|y.1|+|y.2|)
  have meas : Measurable (fun u => atom τ z v (phase u) y
      (fun j => actualGate (pre z j (phase u))) t j) := by
    have h₁ := (pre_phase_cont z j).measurable
    have h₂ := gate_meas z j
    unfold atom dot phase at *
    fun_prop
  apply (integrable_const (length z j*a+b)).mono' meas.aestronglyMeasurable
  filter_upwards with u
  have feat : |max (pre z j (phase u)) 0| ≤ length z j := by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (pre_bound _ _ _ (phase_unit u))) (sqrt_nonneg _)
  have gate : |actualGate (pre z j (phase u))| ≤ 1 := by unfold actualGate; split <;> norm_num
  have angle : |dot (phase u) y| ≤ |y.1|+|y.2| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (abs_cos_le_one _))
      (mul_le_of_le_one_left (abs_nonneg _) (abs_sin_le_one _))
  rw [Real.norm_eq_abs, atom]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_mul (τ*_),abs_mul (actualGate _)]
  apply add_le_add (mul_le_mul_of_nonneg_right feat (abs_nonneg _))
  dsimp [b]
  have gated : |actualGate (pre z j (phase u))| * |t j| ≤ |t j| :=
    mul_le_of_le_one_left (abs_nonneg _) gate
  exact mul_le_mul (mul_le_mul_of_nonneg_left gated (abs_nonneg _)) angle (abs_nonneg _) (by positivity)

theorem angleEntry_integrable (hm : 0 < m) (τ : ℝ) (z v : State m) (y : ℝ × ℝ) (t : Fin m → ℝ) :
    Integrable (angleEntry τ z v y t) angularLaw := by
  change Integrable (fun u => entry τ z v (phase u) y (fun j => actualGate (pre z j (phase u))) t) angularLaw
  simp_rw [entry_sum hm]
  exact (integrable_finsetSum _ (fun j _ => atom_integrable τ z v y t j)).div_const _

theorem margin_integrable (z : State m) (ρ : ℝ) :
    Integrable (fun u => marginMass z ρ (phase u)) angularLaw := by
  apply Integrable.div_const
  apply integrable_finsetSum
  intro j _
  unfold marginFlag
  have h : MeasurableSet {u : ℝ | |pre z j (phase u)| ≤ ρ*length z j} :=
    measurableSet_le (pre_phase_cont z j).abs.measurable measurable_const
  have small : Integrable (fun u => if |pre z j (phase u)| ≤ ρ*length z j then (1:ℝ) else 0)
      angularLaw := by
    convert ((integrable_const (1:ℝ)).indicator (μ := angularLaw) h) using 1
    ext u
    by_cases hu : |pre z j (phase u)| ≤ ρ*length z j <;> simp [Set.indicator,hu]
  exact small.const_mul _

/-- For the true one-turn population row, the near-kink charge at its first
argument is the angular mean of the *initial* weighted margin counts. -/
theorem angular_entry_drift {τ C ρ : ℝ} {z₀ z v : State m} {y : ℝ × ℝ}
    {t t₀ : Fin m → ℝ} (hm : 0 < m) (hC : 1 ≤ C) (hτ : |τ| ≤ C) (hρ : 0 ≤ ρ)
    (hy : UnitInput y) (tz : Tube ρ z₀ z) (tv : Tube ρ z₀ v)
    (sy : ∀ j, Admissible (pre v j y) (t j)) (sy₀ : ∀ j, Admissible (pre z₀ j y) (t₀ j)) :
    |meanEntry τ z v y t - meanEntry τ z₀ z₀ y t₀| ≤
      C*((4*ρ+2*ρ^2)*meanEnergy z₀ + angularMargin z₀ ρ + marginMass z₀ ρ y) := by
  let base := (4*ρ+2*ρ^2)*meanEnergy z₀
  let last := marginMass z₀ ρ y
  have marg := margin_integrable z₀ ρ
  have comb := (((integrable_const base).add marg).add (integrable_const last)).const_mul C
  rw [meanEntry,meanEntry,← integral_sub (angleEntry_integrable hm _ _ _ _ _)
    (angleEntry_integrable hm _ _ _ _ _)]
  apply (abs_integral_le_integral_abs).trans
  calc
    _ ≤ ∫ u, C*(base+marginMass z₀ ρ (phase u)+last) ∂angularLaw := by
      apply integral_mono (((angleEntry_integrable hm _ _ _ _ _).sub
        (angleEntry_integrable hm _ _ _ _ _)).abs) comb
      intro u
      exact entry_drift hm hC hτ hρ (phase_unit u) hy tz tv
        (fun _ => actualGate_admissible _) sy (fun _ => actualGate_admissible _) sy₀
    _ = _ := by
      have bm : Integrable (fun u => base+marginMass z₀ ρ (phase u)) angularLaw := (integrable_const base).add marg
      rw [integral_const_mul,integral_add bm (integrable_const last),
        integral_add (integrable_const base) marg]
      simp [base,last,angularMargin]

def gridGram (τ : ℝ) (z : State m) (g : Fin N → Fin m → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => entry τ z z (circleInput N i) (circleInput N j) (g i) (g j)

def populationRow (τ : ℝ) (z : State m) (g : Fin N → Fin m → ℝ) : Fin N → ℝ :=
  fun i => meanEntry τ z z (circleInput N i) (g i)

def gridGates (z : State m) (g : Fin N → Fin m → ℝ) :=
  ∀ i j, Admissible (pre z j (circleInput N i)) (g i j)

theorem gramOp_sub (A B : Matrix (Fin N) (Fin N) ℝ) : gramOp (A-B) = gramOp A-gramOp B := by
  ext r i
  change gramOp (A-B) r i = gramOp A r i - gramOp B r i
  simp only [gramOp_apply,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,sub_div]

theorem rowOp_sub (a b : Fin N → ℝ) : rowOp (a-b) = rowOp a-rowOp b := by
  ext r
  change rowOp (a-b) r = rowOp a r-rowOp b r
  simp only [rowOp_apply,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib,sub_div]

/-- Both unnormalized tangent tables give the corresponding normalized
operator estimates with the tracking proof's explicit error budget. -/
theorem actual_operator_drift {τ ρ u : ℝ} {z₀ z : State m} {g₀ g : Fin N → Fin m → ℝ}
    (K : Matrix (Fin N) (Fin N) ℝ) (kQ : Fin N → ℝ) (hn : 0 < N) (hm : 0 < m)
    (hτ : |τ| ≤ 2) (hρ : 0 ≤ ρ) (small : ρ ≤ 1) (hu : 0 ≤ u)
    (tz : Tube ρ z₀ z) (ad : gridGates z g) (ad₀ : gridGates z₀ g₀)
    (energy : meanEnergy z₀ ≤ 4)
    (margin : ∀ i : Fin N, marginMass z₀ ρ (circleInput N i) ≤ 3*ρ+u)
    (angular : angularMargin z₀ ρ ≤ 3*ρ+u)
    (initK : ∀ i j, |gridGram τ z₀ g₀ i j-K i j| ≤ 2*u)
    (initQ : ∀ i, |populationRow τ z₀ g₀ i-kQ i| ≤ 2*u) :
    ‖gramOp (gridGram τ z g)-gramOp K‖ ≤ 2*(30*ρ+3*u) ∧
      ‖rowOp (populationRow τ z g)-rowOp kQ‖ ≤ 2*(30*ρ+3*u) := by
  rw [← gramOp_sub,← rowOp_sub]
  constructor
  · apply gramOp_norm hn (by positivity)
    intro i j
    exact two_rate_budget hρ small energy (margin i) (margin j)
      (entry_drift hm (by norm_num) hτ hρ (grid_unit i) (grid_unit j) tz tz (ad i) (ad j)
        (ad₀ i) (ad₀ j)) (initK i j)
  · apply rowOp_norm hn (by positivity)
    intro i
    exact two_rate_budget hρ small energy angular (margin i)
      (angular_entry_drift hm (by norm_num) hτ hρ (grid_unit i) tz tz (ad i) (ad₀ i)) (initQ i)

/-- The actual coordinate velocity contracted with a test Jacobian equals
the negative normalized tangent row acting on the grid residual. -/
theorem velocity_contraction (τ : ℝ) (z : State m) (x : ℝ × ℝ) (s : Fin m → ℝ)
    (X : Fin N → ℝ × ℝ) (g : Fin N → Fin m → ℝ) (r : Fin N → ℝ) :
    pair (row (1/sqrt m) z x s)
      (velocity τ (fun i => row (1/sqrt m) z (X i) (g i)) r) =
    -(∑ i, entry τ z z x (X i) s (g i)*r i)/N := by
  simp only [entry, pair, velocity, gradient, Finset.mul_sum, Finset.sum_mul,
    div_eq_mul_inv, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- Vector-field identification for the actual finite-width paired experiment,
in grid coordinates and at a.e. physical time through grid kinks. -/
theorem ae_grid_ode {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T → ∃ g : Fin N → Fin m → ℝ,
      gridGates (z t) g ∧ ∀ i, HasDerivAt
        (fun s => residual (circleInput N) (circleLabel N) (1/sqrt m) (z s) i)
        (-(∑ j, gridGram τ (z t) g i j *
          residual (circleInput N) (circleLabel N) (1/sqrt m) (z t) j)/N) t := by
  filter_upwards [ae_residual_eq F] with t ht hm
  obtain ⟨g,ad,hvel,der⟩ := ht hm
  refine ⟨g,ad,fun i => ?_⟩
  have h := der i
  rw [hvel,velocity_contraction] at h
  exact h


/-- Isometric coordinates for an unscaled physical residual with the RMS norm. -/
def rmsCoordinates (a : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => a i / sqrt N)

theorem rmsCoordinates_norm_sq (a : Fin N → ℝ) :
    ‖rmsCoordinates a‖^2 = (∑ i, a i^2)/N := by
  simp only [EuclideanSpace.real_norm_sq_eq,rmsCoordinates,div_pow,sq_sqrt (Nat.cast_nonneg N),
    Finset.sum_div]

theorem rowOp_rms (a h : Fin N → ℝ) : rowOp h (rmsCoordinates a) = (∑ i, h i*a i)/N := by
  rw [rowOp_apply]
  change (∑ i, h i*(a i/sqrt N))/sqrt N = _
  simp only [← mul_div_assoc, ← Finset.sum_div, div_div, ← sq, sq_sqrt (Nat.cast_nonneg N)]

private theorem rms_deriv {r : ℝ → Fin N → ℝ} {s : ℝ} {v : Fin N → ℝ}
    (dr : ∀ i, HasDerivAt (fun t => r t i) (v i) s) :
    HasDerivAt (fun t => rmsCoordinates (r t)) (rmsCoordinates v) s := by
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℝ)).symm
  have h : HasDerivAt (fun t i => r t i/sqrt N) (fun i => v i/sqrt N) s :=
    hasDerivAt_pi.mpr (fun i => (dr i).div_const _)
  exact E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s h

/-- The Hilbert-space differential equation used by nonlinear tracking,
derived for the actual network residual in RMS-isometric coordinates. -/
theorem ae_grid_hilbert_ode {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    let r := fun s => rmsCoordinates (residual (circleInput N) (circleLabel N) (1/sqrt m) (z s))
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T → ∃ g : Fin N → Fin m → ℝ,
      gridGates (z t) g ∧ HasDerivAt r (-(gramOp (gridGram τ (z t) g) (r t))) t := by
  intro r
  filter_upwards [ae_grid_ode F] with t ht hm
  obtain ⟨g,ad,dr⟩ := ht hm
  refine ⟨g,ad,(rms_deriv dr).congr_deriv ?_⟩
  ext i
  change (-(∑ j, _ * _)/N)/sqrt N = -(gramOp _ (r t) i)
  rw [gramOp_apply]
  dsimp [r,rmsCoordinates]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  ring


/-- The actual zero-at-kink Jacobian of the common initial state. -/
def startGates (z : State m) (i : Fin N) (j : Fin m) :=
  actualGate (pre z j (circleInput N i))

theorem startGates_admissible (z : State m) : gridGates (N := N) z (startGates z) :=
  fun _ _ => actualGate_admissible _

/-- Deterministic kernel- and margin-control events, expressed on the original
network coordinates at time zero. The initial residual is treated separately. -/
structure GoodInit (τ ρ u : ℝ) (K : Matrix (Fin N) (Fin N) ℝ) (kQ : Fin N → ℝ)
    (z₀ : State m) : Prop where
  energy : meanEnergy z₀ ≤ 4
  gridMargin : ∀ i : Fin N, marginMass z₀ ρ (circleInput N i) ≤ 3*ρ+u
  angular : angularMargin z₀ ρ ≤ 3*ρ+u
  gram : ∀ i j, |gridGram τ z₀ (startGates z₀) i j-K i j| ≤ 2*u
  mean : ∀ i, |populationRow τ z₀ (startGates z₀) i-kQ i| ≤ 2*u

theorem GoodInit.track_ops {τ ρ u : ℝ} {z₀ z : State m} {K : Matrix (Fin N) (Fin N) ℝ}
    {kQ : Fin N → ℝ} (G : GoodInit τ ρ u K kQ z₀) {g : Fin N → Fin m → ℝ}
    (hn : 0 < N) (hm : 0 < m) (hτ : |τ| ≤ 2) (hρ : 0 ≤ ρ) (small : ρ ≤ 1)
    (hu : 0 ≤ u) (tz : Tube ρ z₀ z) (ad : gridGates z g) :
    ‖gramOp (gridGram τ z g)-gramOp K‖ ≤ 2*(30*ρ+3*u) ∧
      ‖rowOp (populationRow τ z g)-rowOp kQ‖ ≤ 2*(30*ρ+3*u) :=
  actual_operator_drift K kQ hn hm hτ hρ small hu tz ad (startGates_admissible _) G.energy
    G.gridMargin G.angular G.gram G.mean

end CircleTangentDrift
