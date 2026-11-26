module

public import CircleGrowth
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-! Real-arithmetic escape for simultaneous full-batch GD. The constants
`c=1/√m` and `k=η/(N√m)` incorporate the output and gradient normalizations.
The finite design hypothesis is existence of a sample with positive projection
at least `‖w‖/2` for each hidden vector. -/

public section
noncomputable section
namespace CircleEscape
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {N m : ℕ}

/-- Both sets of parameters in a two-layer bias-free ReLU network. -/
structure Net (V : Type*) (m : ℕ) where
  a : Fin m → ℝ
  w : Fin m → V

def feature (w x : V) : ℝ := max (inner ℝ w x) 0

def output (c : ℝ) (n : Net V m) (x : V) : ℝ :=
  c * ∑ j, n.a j * feature (n.w j) x

/-- The gate selects derivative zero when the preactivation is exactly zero. -/
def gate (w x : V) : ℝ := if 0 < inner ℝ w x then 1 else 0

theorem gate_projection (w x : V) :
    gate w x * inner ℝ w x = feature w x := by
  unfold gate feature
  split_ifs with h
  · rw [one_mul, max_eq_left h.le]
  · rw [zero_mul, max_eq_right (le_of_not_gt h)]

/-- Both gradient blocks are evaluated at the same parameter vector. -/
def step (x : Fin N → V) (y : Fin N → ℝ) (c k : ℝ) (n : Net V m) : Net V m :=
  let r := fun i => output c n (x i) - y i
  { a := fun j => n.a j - k * ∑ i, r i * feature (n.w j) (x i)
    w := fun j => n.w j - (k * n.a j) • ∑ i, (r i * gate (n.w j) (x i)) • x i }

/-- The signed size of every readout and the radius of every hidden weight. -/
def Cone (n : Net V m) (σ s : ℝ) : Prop :=
  ∀ j, s ≤ σ * n.a j ∧ s ≤ ‖n.w j‖

private theorem activation_sum (x : Fin N → V) (w : V)
    (cover : ∃ i, ‖w‖/2 ≤ feature w (x i)) :
    ‖w‖^2 / 4 ≤ ∑ i, feature w (x i)^2 := by
  obtain ⟨i, hi⟩ := cover
  have hs := pow_le_pow_left₀ (show 0 ≤ ‖w‖/2 by positivity) hi 2
  apply le_trans _ (Finset.single_le_sum (fun i _ => sq_nonneg (feature w (x i)))
    (Finset.mem_univ i))
  linarith

/-- Lower bound on a single signed readout gradient, from the actual finite sum.
The signed output includes only nonnegative contributions on the cone. -/
theorem signed_gradient (x : Fin N → V) (y : Fin N → ℝ) (n : Net V m) (c σ : ℝ)
    (hc : 0 ≤ c) (hu : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, σ*y i ≤ 2)
    (pos : ∀ j, 0 ≤ σ*n.a j) (cover : ∀ w, ∃ i, ‖w‖/2 ≤ feature w (x i))
    (j : Fin m) :
    c*(σ*n.a j)*‖n.w j‖^2/4 - 2*N*‖n.w j‖ ≤
      ∑ i, σ*(output c n (x i)-y i)*feature (n.w j) (x i) := by
  let w := n.w j
  let h := fun i => feature w (x i)
  have hn i : 0 ≤ h i := le_max_right _ _
  have hb i : h i ≤ ‖w‖ := by
    apply max_le _ (norm_nonneg _)
    have hi := mul_le_mul_of_nonneg_left (hu i) (norm_nonneg w)
    simpa using (real_inner_le_norm w (x i)).trans hi
  have single (i : Fin N) : c*(σ*n.a j)*h i ≤ σ * output c n (x i) := by
    have hsum := Finset.single_le_sum (fun j _ => mul_nonneg (pos j)
      (le_max_right (inner ℝ (n.w j) (x i)) 0)) (Finset.mem_univ j)
    calc
      _ = c*((σ*n.a j)*feature (n.w j) (x i)) := by dsimp [h,w]; ring
      _ ≤ c * ∑ l, ((σ*n.a l)*feature (n.w l) (x i)) :=
        mul_le_mul_of_nonneg_left hsum hc
      _ = _ := by simp only [output, mul_assoc, ← Finset.mul_sum]; ring
  have row (i : Fin N) : c*(σ*n.a j)*(h i)^2-2*‖w‖ ≤
      σ*(output c n (x i)-y i)*h i := by
    have hyh := mul_le_mul_of_nonneg_right (hy i) (hn i)
    have hh := mul_le_mul_of_nonneg_right (single i) (hn i)
    nlinarith [hb i]
  calc
    _ ≤ c*(σ*n.a j)*(∑ i, (h i)^2) - 2*N*‖w‖ := by
      have hh := mul_le_mul_of_nonneg_left (activation_sum x w (cover w))
        (mul_nonneg hc (pos j))
      linarith
    _ = ∑ i, (c*(σ*n.a j)*(h i)^2-2*‖w‖) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => row i

/-- Projecting the hidden-weight update recovers exactly the readout-gradient
sum. This holds pointwise at kinks as well. -/
theorem hidden_projection (x : Fin N → V) (y : Fin N → ℝ) (c k : ℝ)
    (n : Net V m) (j : Fin m) :
    inner ℝ (n.w j) ((step x y c k n).w j) = ‖n.w j‖^2 -
      (k*n.a j) * ∑ i, (output c n (x i)-y i)*feature (n.w j) (x i) := by
  simp only [step, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_smul_right,
    inner_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, gate_projection]

/-- A large, aligned-sign state sends every readout to the opposite sign in
one actual GD step. All signed readout magnitudes and hidden radii grow at
least cubically. The hypotheses on c,k,L are explicit scalar checks. -/
theorem step_cone (x : Fin N → V) (y : Fin N → ℝ) (c k L σ s : ℝ) (n : Net V m)
    (hc : 0 < c) (hk : 0 < k) (hL : 0 < L) (hu : ∀ i, ‖x i‖ ≤ 1)
    (cover : ∀ w, ∃ i, ‖w‖/2 ≤ feature w (x i)) (hy : ∀ i, σ*y i ≤ 2)
    (unitSign : σ^2 = 1) (large : 2*L ≤ s) (state : Cone n σ s)
    (scale : k*c*L^2 = 16) (noise : 16*N ≤ c*(2*L)^2) :
    Cone (step x y c k n) (-σ) (s^3/L^2) := by
  intro j
  let W := ‖n.w j‖
  let A := σ*n.a j
  let D := k*∑ i, σ*(output c n (x i)-y i)*feature (n.w j) (x i)
  let grad := ∑ i, (output c n (x i)-y i)*feature (n.w j) (x i)
  have hA : s ≤ A := (state j).1
  have hW : s ≤ W := (state j).2
  have hW0 : 0 ≤ W := norm_nonneg _
  have hs0 : 0 ≤ s := by linarith
  have key := signed_gradient x y n c σ hc.le hu hy
    (fun i => hs0.trans (state i).1) cover j
  have dk : k*(c*A*W^2/4 - 2*N*W) ≤ D := mul_le_mul_of_nonneg_left key hk.le
  have hsize : 16*(N:ℝ) ≤ c*(A*W) := by
    apply noise.trans
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [sq]
    exact mul_le_mul (large.trans hA) (large.trans hW) (by linarith) (hs0.trans hA)
  have prod := mul_le_mul_of_nonneg_right hsize hW0
  have hlow : k*(c*A*W^2/8) ≤ D := by
    apply le_trans _ dk
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  have hD : 2*A*W^2 ≤ D*L^2 := by
    have hg := mul_le_mul_of_nonneg_right hlow (sq_nonneg L)
    calc
      _ = (k*c*L^2) * A*W^2/8 := by rw [scale]; ring
      _ ≤ _ := by linarith
  have hsplit : D = k*σ*grad := by
    dsimp [D,grad]
    simp only [mul_assoc, ← Finset.mul_sum]
  have hiden := hidden_projection x y c k n j
  have hproject : A*D-W^2 ≤ W*‖(step x y c k n).w j‖ := by
    calc
      _ = -inner ℝ (n.w j) ((step x y c k n).w j) := by
        rw [hiden, hsplit]
        dsimp [A,grad,W]
        linear_combination (n.a j*k*(∑ i, (output c n (x i)-y i)*feature (n.w j) (x i))) * unitSign
      _ ≤ _ := by simpa using real_inner_le_norm (-(n.w j)) ((step x y c k n).w j)
  obtain ⟨ha, hw⟩ := CircleGrowth.cone_step A W L s D _ hL large hA hW hD hproject
  refine ⟨ha.trans_eq ?_, hw⟩
  rw [hsplit]
  dsimp [A,grad,step]
  ring

/-- Exact recurrence for the cubic lower bound. -/
def radiusFloor (L : ℝ) (t : ℕ) : ℝ := L * 2^(3^t)

private theorem floor_large (L : ℝ) (hL : 0 ≤ L) (t : ℕ) : 2*L ≤ radiusFloor L t := by
  dsimp [radiusFloor]
  rw [mul_comm 2 L]
  apply mul_le_mul_of_nonneg_left _ hL
  calc
    (2:ℝ) = 2^1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (pow_pos (by decide : 0 < (3:ℕ)) _))

private theorem floor_step (L : ℝ) (hL : 0 < L) (t : ℕ) :
    (radiusFloor L t)^3/L^2 = radiusFloor L (t+1) := by
  dsimp [radiusFloor]
  rw [pow_succ 3, pow_mul, mul_pow]
  field_simp

/-- Negative readout signs are covered by sign symmetry of the box; the labels
remain fixed in every update. -/
theorem escape (x : Fin N → V) (y : Fin N → ℝ) (c k L : ℝ)
    (hc : 0 < c) (hk : 0 < k) (hL : 0 < L) (hu : ∀ i, ‖x i‖ ≤ 1)
    (cover : ∀ w, ∃ i, ‖w‖/2 ≤ feature w (x i)) (hy : ∀ i, |y i| ≤ 2)
    (scale : k*c*L^2 = 16) (noise : 16*N ≤ c*(2*L)^2)
    (n : ℕ → Net V m) (update : ∀ t, n (t+1) = step x y c k (n t))
    (σ : ℝ) (sign : |σ| = 1) (start : Cone (n 0) σ (2*L)) (t : ℕ) :
    Cone (n t) ((-1)^t*σ) (radiusFloor L t) := by
  induction t with
  | zero => simpa [radiusFloor, mul_comm] using start
  | succ t ih =>
    let v := (-1:ℝ)^t * σ
    have hv : |v| = 1 := by simp [v, abs_mul, abs_pow, sign]
    have hv2 : v^2 = 1 := by rw [← sq_abs, hv]; norm_num
    have hlabel i : v*y i ≤ 2 := by
      apply (le_abs_self _).trans
      simpa [abs_mul, hv] using hy i
    have h := step_cone x y c k L v (radiusFloor L t) (n t) hc hk hL hu cover
      hlabel hv2 (floor_large L hL.le t) ih scale noise
    rw [floor_step L hL t] at h
    rw [update, pow_succ]
    simpa only [v, mul_neg_one, neg_mul] using h

/-- The exact integrated mean is the sum of readout times hidden radius,
scaled by `c/π`. -/
def populationMean (c : ℝ) (n : Net V m) : ℝ :=
  (c/Real.pi) * ∑ j, n.a j * ‖n.w j‖

omit [InnerProductSpace ℝ V] in
theorem signed_mean (c σ s : ℝ) (n : Net V m) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : Cone n σ s) : (c/Real.pi)*m*s^2 ≤ σ*populationMean c n := by
  have hsum : ∑ _j : Fin m, s^2 ≤ ∑ j, (σ*n.a j)*‖n.w j‖ :=
    Finset.sum_le_sum (fun j _ => by
      rw [sq]; exact mul_le_mul (h j).1 (h j).2 hs (hs.trans (h j).1))
  have smaller := mul_le_mul_of_nonneg_left hsum (div_nonneg hc Real.pi_pos.le)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    populationMean, mul_assoc, ← Finset.mul_sum, mul_left_comm σ (c/Real.pi)] using smaller

/-- Canonical equally spaced grid, using the complex plane as a real inner product space. -/
def gridPoint (N : ℕ) (i : Fin N) : ℂ :=
  let θ := (2*Real.pi/N) * (i:ℕ)
  ⟨Real.cos θ, Real.sin θ⟩

theorem grid_norm (N : ℕ) (i : Fin N) : ‖gridPoint N i‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [gridPoint, ← sq, Real.cos_sq_add_sin_sq, Real.sqrt_one]

/-- Round in angular units and reduce the grid index modulo the period. -/
theorem grid_coverage (N : ℕ) (hN : 3 ≤ N) (w : ℂ) :
    ∃ i, ‖w‖/2 ≤ feature w (gridPoint N i) := by
  let d := 2*Real.pi/N
  have npos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have dp : 0 < d := by dsimp [d]; positivity
  let t := w.arg / d
  let j := round t
  have np : (0:ℤ) < N := by omega
  have rem0 := Int.emod_nonneg j np.ne'
  let i : Fin N := ⟨(j % (N:ℤ)).toNat,
    (Int.toNat_lt rem0).mpr (Int.emod_lt_of_pos _ np)⟩
  let q := j / (N:ℤ)
  have hi : ((i:ℕ):ℤ) = j % (N:ℤ) := Int.toNat_of_nonneg rem0
  have jint : (i:ℕ)+(N:ℤ)*q = j := by rw [hi]; exact Int.emod_add_mul_ediv _ _
  have jreal : ((i:ℕ):ℝ)+(N:ℝ)*q = j := by exact_mod_cast jint
  have period : w.arg - d*(i:ℕ) = (w.arg-d*j) + q*(2*Real.pi) := by
    rw [← jreal]
    dsimp [d]
    field_simp
    ring
  have near : |w.arg - d*j| ≤ Real.pi/3 := by
    calc
      _ = |d| * |t-j| := by rw [← abs_mul]; congr 1; dsimp [t]; field_simp
      _ ≤ d*(1/2) := by
        rw [abs_of_pos dp]; exact mul_le_mul_of_nonneg_left (abs_sub_round t) dp.le
      _ ≤ _ := by
        dsimp [d]
        rw [div_mul_eq_mul_div, div_le_iff₀ npos]
        nlinarith [mul_le_mul_of_nonneg_left h3 Real.pi_pos.le]
  have coslow := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) near
  rw [Real.cos_abs, Real.cos_pi_div_three] at coslow
  refine ⟨i, le_trans ?_ (le_max_left _ _)⟩
  change ‖w‖ / 2 ≤ inner ℝ w (gridPoint N i)
  have ginner : inner ℝ w (gridPoint N i) = ‖w‖*Real.cos (w.arg-d*(i:ℕ)) := by
    rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im, Real.cos_sub]
    rw [mul_add, ← mul_assoc, Complex.norm_mul_cos_arg, ← mul_assoc, Complex.norm_mul_sin_arg]
    dsimp [gridPoint,d]
    ring
  rw [ginner, period, Real.cos_add_int_mul_two_pi]
  simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left coslow (norm_nonneg w)

/-- The actual fixed-step algorithm on the stated circle regression problem.
A signed Gaussian box supplies the two lower bounds at time zero. The imaginary
coordinates can be arbitrary for this deterministic implication. The conclusion
retains the sign needed for a two-tail variance lower bound. -/
theorem circle_escape (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L σ : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 16*N*m/η)
    (n : ℕ → Net ℂ m) (update : ∀ t, n (t+1) =
      step (gridPoint N) (fun i => 1 + (gridPoint N i).re)
        (1/Real.sqrt m) (η/(N*Real.sqrt m)) (n t))
    (sign : |σ| = 1) (start : ∀ j, 2*L ≤ σ*(n 0).a j ∧ 2*L ≤ ((n 0).w j).re)
    (t : ℕ) :
    (Real.sqrt m/Real.pi) * (L*2^(3^t))^2 ≤
      ((-1)^t*σ)*populationMean (1/Real.sqrt m) (n t) := by
  have np : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ms := Real.sqrt_pos.mpr mp
  have msq := Real.sq_sqrt mp.le
  have m1 := Real.one_le_sqrt.mpr (show (1:ℝ) ≤ m by exact_mod_cast hm)
  have hsize : η*Real.sqrt m ≤ m := calc
    _ ≤ 1 * Real.sqrt m := mul_le_mul_of_nonneg_right hcap ms.le
    _ ≤ (Real.sqrt m)^2 := by nlinarith [mul_le_mul_of_nonneg_right m1 ms.le]
    _ = _ := msq
  have scale : (η/(N*Real.sqrt m)) * (1/Real.sqrt m) * L^2 = 16 := by
    rw [hscale]; field_simp; nlinarith [congrArg (fun v : ℝ => (N:ℝ)*v) msq]
  have noise : 16*(N:ℝ) ≤ (1 / Real.sqrt m) * (2*L)^2 := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ ms]
    have hsq : L^2*η = 16*N*m := (eq_div_iff hη.ne').mp hscale
    apply le_of_mul_le_mul_right (a := η) _ hη
    nlinarith [mul_le_mul_of_nonneg_left hsize (show 0 ≤ 16*(N:ℝ) by positivity)]
  have lab (i : Fin N) : |1 + (gridPoint N i).re| ≤ 2 := by
    apply (abs_add_le _ _).trans
    have hh := Complex.abs_re_le_norm (gridPoint N i)
    rw [grid_norm] at hh
    rw [abs_one]
    linarith
  have initial : Cone (n 0) σ (2*L) := fun j =>
    ⟨(start j).1, (start j).2.trans (Complex.re_le_norm _)⟩
  have path := escape (gridPoint N) _ _ _ _ (one_div_pos.mpr ms) (by positivity) hL
    (fun i => (grid_norm N i).le) (grid_coverage N hN) lab scale noise n update σ sign initial t
  have mean := signed_mean (1/Real.sqrt m) _ (radiusFloor L t) (n t) (by positivity)
    (by dsimp [radiusFloor]; positivity) path
  have coef : (1/Real.sqrt m/Real.pi)*m = Real.sqrt m/Real.pi := by
    field_simp
    linarith
  rwa [coef] at mean

end CircleEscape

