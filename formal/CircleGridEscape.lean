module

public import CircleEscapeBridge
import all CircleEscapeBridge
public import CircleGridMargin
import all CircleEscape
import Mathlib.Tactic

/-! The grid second moment strengthens the signed-box escape estimate to
`L²=64m/η`, uniformly in the number of circle samples. -/

public section
noncomputable section
open CircleEscape
namespace CircleGridEscape
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N m : ℕ}

/-- Lower bound on a single signed readout gradient, from the actual finite sum.
The signed output includes only nonnegative contributions on the cone. -/
private theorem signed_gradient (x : Fin N → V) (y : Fin N → ℝ) (n : Net V m) (c σ : ℝ)
    (hc : 0 ≤ c) (hu : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, σ*y i ≤ 2)
    (pos : ∀ j, 0 ≤ σ*n.a j) (moment : ∀ w, N*‖w‖^2/16 ≤ ∑ i, feature w (x i)^2)
    (j : Fin m) :
    c*(σ*n.a j)*N*‖n.w j‖^2/16 - 2*N*‖n.w j‖ ≤
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
      have hh := mul_le_mul_of_nonneg_left (moment w)
        (mul_nonneg hc (pos j))
      linarith
    _ = ∑ i, (c*(σ*n.a j)*(h i)^2-2*‖w‖) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => row i

/-- A large, aligned-sign state sends every readout to the opposite sign in
one actual GD step. All signed readout magnitudes and hidden radii grow at
least cubically. The hypotheses on c,k,L are explicit scalar checks. -/
theorem step_cone_grid (x : Fin N → V) (y : Fin N → ℝ) (c k L σ s : ℝ) (n : Net V m)
    (hc : 0 < c) (hk : 0 < k) (hL : 0 < L) (hu : ∀ i, ‖x i‖ ≤ 1)
    (moment : ∀ w, N*‖w‖^2/16 ≤ ∑ i, feature w (x i)^2) (hy : ∀ i, σ*y i ≤ 2)
    (unitSign : σ^2 = 1) (large : 2*L ≤ s) (state : Cone n σ s)
    (scale : k*c*N*L^2 = 64) (noise : 64 ≤ c*(2*L)^2) :
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
    (fun i => hs0.trans (state i).1) moment j
  have dk : k*(c*A*N*W^2/16 - 2*N*W) ≤ D := mul_le_mul_of_nonneg_left key hk.le
  have hsize : 64 ≤ c*(A*W) := by
    apply noise.trans
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [sq]
    exact mul_le_mul (large.trans hA) (large.trans hW) (by linarith) (hs0.trans hA)
  have prod := mul_le_mul_of_nonneg_right hsize (mul_nonneg (Nat.cast_nonneg N) hW0)
  have hlow : k*(c*A*N*W^2/32) ≤ D := by
    apply le_trans _ dk
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  have hD : 2*A*W^2 ≤ D*L^2 := by
    have hg := mul_le_mul_of_nonneg_right hlow (sq_nonneg L)
    calc
      _ = (k*c*N*L^2) * A*W^2/32 := by rw [scale]; ring
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

private theorem iterate_cone (x : Fin N → V) (y : Fin N → ℝ) (c k L : ℝ)
    (hc : 0 < c) (hk : 0 < k) (hL : 0 < L) (hu : ∀ i, ‖x i‖ ≤ 1)
    (moment : ∀ w, N*‖w‖^2/16 ≤ ∑ i, feature w (x i)^2) (hy : ∀ i, |y i| ≤ 2)
    (scale : k*c*N*L^2 = 64) (noise : 64 ≤ c*(2*L)^2)
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
    have h := step_cone_grid x y c k L v (radiusFloor L t) (n t) hc hk hL hu moment
      hlabel hv2 (floor_large L hL.le t) ih scale noise
    rw [floor_step L hL t] at h
    rw [update, pow_succ]
    simpa only [v, mul_neg_one, neg_mul] using h

/-- The actual fixed-step algorithm on the stated circle regression problem.
A signed Gaussian box supplies the two lower bounds at time zero. The imaginary
coordinates can be arbitrary for this deterministic implication. The conclusion
retains the sign needed for a two-tail variance lower bound. -/
theorem circle_escape_uniform (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L σ : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 64*m/η)
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
  have scale : (η/(N*Real.sqrt m)) * (1/Real.sqrt m) * N * L^2 = 64 := by
    rw [hscale]; field_simp; nlinarith [congrArg (fun v : ℝ => (N:ℝ)*v) msq]
  have noise : 64 ≤ (1 / Real.sqrt m) * (2*L)^2 := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ ms]
    have hsq : L^2*η = 64*m := (eq_div_iff hη.ne').mp hscale
    apply le_of_mul_le_mul_right (a := η) _ hη
    nlinarith
  have lab (i : Fin N) : |1 + (gridPoint N i).re| ≤ 2 := by
    apply (abs_add_le _ _).trans
    have hh := Complex.abs_re_le_norm (gridPoint N i)
    rw [grid_norm] at hh
    rw [abs_one]
    linarith
  have initial : Cone (n 0) σ (2*L) := fun j =>
    ⟨(start j).1, (start j).2.trans (Complex.re_le_norm _)⟩
  have path := iterate_cone (gridPoint N) _ _ _ _ (one_div_pos.mpr ms) (by positivity) hL
    (fun i => (grid_norm N i).le) (fun w => (CircleGridMargin.grid_relu_sum_bounds N hN w).2) lab scale noise n update σ sign initial t
  have mean := signed_mean (1/Real.sqrt m) _ (radiusFloor L t) (n t) (by positivity)
    (by dsimp [radiusFloor]; positivity) path
  have coef : (1/Real.sqrt m/Real.pi)*m = Real.sqrt m/Real.pi := by
    field_simp
    linarith
  rwa [coef] at mean

open MeasureTheory ProbabilityTheory Set CircleEscapeBridge

/-- The full Gaussian-box lower bound with an escape scale independent of N.
The seed exponent is exactly `-896 m²/η`. Finite-cap square integrability is
assumed as in the original bridge. -/
theorem benchmark_bounds_uniform (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L b : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 64*m/η)
    (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Seed m → ℕ → Net ℂ m) (start : ∀ ω, n ω 0 = initial ω)
    (update : ∀ ω t, n ω (t+1) = step (gridPoint N) (fun i => 1+(gridPoint N i).re)
        (1/Real.sqrt m) (η/(N*Real.sqrt m)) (n ω t))
    (hF : MemLp (trainedMean n T) 2 (seedLaw m)) (hZ : MemLp (reference N m b) 2 (seedLaw m)) :
    Real.exp (-896*m^2/η) * (amplitude m T L)^2 ≤ variance (trainedMean n T) (seedLaw m) ∧
    Real.exp (-896*m^2/η) * (max (amplitude m T L-referenceCap m L) 0)^2 ≤
      ∫ ω, (trainedMean n T ω-reference N m b ω)^2 ∂(seedLaw m) := by
  let A := amplitude m T L
  let F := trainedMean n T
  have hA : 0 ≤ A := by change 0 ≤ (Real.sqrt m/Real.pi)*(L*2^(3^T))^2; positivity
  have mass (neg : Bool) :
      Real.exp (-896*m^2/η) ≤ (seedLaw m).real (box m L neg) := by
    have expBound := exponential_mass 4 m (by decide) hm η L hη hcap hL
      (by convert hscale using 1; norm_num)
    have eq : -896*(m:ℝ)^2/η = -14*m*L^2 := by rw [hscale]; ring
    rw [eq]
    exact expBound.trans (signed_gaussian_mass m L hL.le neg)
  have hp (ω : Seed m) (hω : ω ∈ box m L false) : A ≤ (-1)^T*F ω := by
    have initPos (j : Fin m) : 2*L ≤ 1*(n ω 0).a j ∧ 2*L ≤ ((n ω 0).w j).re := by
      rw [start, one_mul]
      exact ⟨(hω (j,0) (mem_univ _)).1, (hω (j,1) (mem_univ _)).1⟩
    simpa only [A,F,amplitude,trainedMean,mul_one] using circle_escape_uniform N m hN hm
      η L 1 hη hcap hL hscale (n ω) (update ω) (by norm_num) initPos T
  have hn (ω : Seed m) (hω : ω ∈ box m L true) : A ≤ -((-1)^T*F ω) := by
    have initNeg (j : Fin m) : 2*L ≤ (-1)*(n ω 0).a j ∧ 2*L ≤ ((n ω 0).w j).re := by
      rw [start, neg_one_mul]
      exact ⟨(hω (j,0) (mem_univ _)).1, (hω (j,1) (mem_univ _)).1⟩
    simpa only [A,F,amplitude,trainedMean,mul_neg_one,neg_mul] using circle_escape_uniform N m hN hm
      η L (-1) hη hcap hL hscale (n ω) (update ω) (by norm_num) initNeg T
  constructor
  · rcases Nat.even_or_odd T with ev | od
    · apply CircleTails.variance_of_opposite_tails hF (measurable_box m L false)
        (measurable_box m L true) hA (mass false) (mass true)
      · simpa only [ev.neg_one_pow,one_mul] using hp
      · intro ω hω; have h := hn ω hω; rw [ev.neg_one_pow,one_mul] at h; linarith
    · apply CircleTails.variance_of_opposite_tails hF (measurable_box m L true)
        (measurable_box m L false) hA (mass true) (mass false)
      · simpa only [od.neg_one_pow,neg_one_mul,neg_neg] using hn
      · intro ω hω; have h := hp ω hω; rw [od.neg_one_pow,neg_one_mul] at h; linarith
  · apply CircleEscapeMoment.paired_second_moment_of_escape hF hZ (measurable_box m L false)
      (mass false) _ (reference_on_box N m (by omega) (by omega) L b hL.le hb hb')
    intro ω hω
    simpa [abs_mul, abs_pow] using (hp ω hω).trans (le_abs_self _)

end CircleGridEscape
