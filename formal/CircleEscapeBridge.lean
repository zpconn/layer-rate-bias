module

public import CircleEscape
import all CircleEscape
import Mathlib.Analysis.Real.Pi.Bounds
public import CircleEscapeMoment
public import CircleTails
import Mathlib.Tactic

/-! Combine the two deterministic signed escape trajectories with their
probability masses on a common seed space. Both signs use the same labels,
optimizer, horizon and reference. -/

public section
noncomputable section

open MeasureTheory ProbabilityTheory Set CircleEscape
namespace CircleEscapeBridge

def trainedMean {Ω : Type*} {m : ℕ} (n : Ω → ℕ → Net ℂ m) (T : ℕ) (ω : Ω) : ℝ :=
  populationMean (1/Real.sqrt m) (n ω T)

def amplitude (m T : ℕ) (L : ℝ) : ℝ :=
  (Real.sqrt m / Real.pi) * (L*2^(3^T))^2

/-- Joint lower bounds on the variance and paired error of actual GD, for
any seed law that puts at least p mass in each indicated signed box.
The reference only needs to be bounded on the positive-initialization box.
The two boxes exchange upper/lower tail roles at each odd step. -/
theorem box_moment_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 16*N*m/η)
    (n : Ω → ℕ → Net ℂ m) (update : ∀ ω t, n ω (t+1) =
      step (gridPoint N) (fun i => 1+(gridPoint N i).re)
        (1/Real.sqrt m) (η/(N*Real.sqrt m)) (n ω t))
    (P M : Set Ω) (mP : MeasurableSet P) (mM : MeasurableSet M)
    (p B : ℝ) (massP : p ≤ μ.real P) (massM : p ≤ μ.real M)
    (pos : ∀ ω ∈ P, ∀ j, 2*L ≤ (n ω 0).a j ∧ 2*L ≤ ((n ω 0).w j).re)
    (neg : ∀ ω ∈ M, ∀ j, 2*L ≤ -(n ω 0).a j ∧ 2*L ≤ ((n ω 0).w j).re)
    (Z : Ω → ℝ) (hF : MemLp (trainedMean n T) 2 μ) (hZ : MemLp Z 2 μ)
    (refBound : ∀ ω ∈ P, |Z ω| ≤ B) :
    p * (amplitude m T L)^2 ≤ variance (trainedMean n T) μ ∧
    p * (max (amplitude m T L-B) 0)^2 ≤ ∫ ω, (trainedMean n T ω-Z ω)^2 ∂μ := by
  let F := trainedMean n T
  let A := amplitude m T L
  have hA : 0 ≤ A := by dsimp [A, amplitude]; positivity
  have hp (ω : Ω) (hω : ω ∈ P) : A ≤ (-1)^T*F ω := by
    simpa [A,F,amplitude,trainedMean] using circle_escape N m hN hm η L 1 hη hcap hL hscale
      (n ω) (update ω) (by norm_num) (by simpa using pos ω hω) T
  have hn (ω : Ω) (hω : ω ∈ M) : A ≤ -((-1)^T*F ω) := by
    simpa [A,F,amplitude,trainedMean] using circle_escape N m hN hm η L (-1) hη hcap hL hscale
      (n ω) (update ω) (by norm_num) (by simpa using neg ω hω) T
  have parity : (-1:ℝ)^T = 1 ∨ (-1:ℝ)^T = -1 := by
    rcases Nat.even_or_odd T with h | h
    · exact Or.inl h.neg_one_pow
    · exact Or.inr h.neg_one_pow
  constructor
  · rcases parity with even | odd
    · apply CircleTails.variance_of_opposite_tails hF mP mM hA massP massM
      · simpa [even] using hp
      · intro ω hω; have h := hn ω hω; rw [even, one_mul] at h; linarith
    · apply CircleTails.variance_of_opposite_tails hF mM mP hA massM massP
      · simpa [odd] using hn
      · intro ω hω; have h := hp ω hω; rw [odd, neg_one_mul] at h; linarith
  · apply CircleEscapeMoment.paired_second_moment_of_escape hF hZ mP massP _ refBound
    intro ω hω
    have h := (hp ω hω).trans (le_abs_self _)
    simpa [F, abs_mul, abs_pow] using h

/-- Three scalar Gaussian coordinates per neuron, in order a, w₁, w₂. -/
abbrev Seed (m : ℕ) := (Fin m × Fin 3) → ℝ

def seedLaw (m : ℕ) : Measure (Seed m) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (m : ℕ) : IsProbabilityMeasure (seedLaw m) := by
  unfold seedLaw
  infer_instance

def initial {m : ℕ} (ω : Seed m) : Net ℂ m :=
  ⟨fun j => ω (j,0), fun j => ⟨ω (j,1), ω (j,2)⟩⟩

def boxInterval (L : ℝ) (negative : Bool) (coord : Fin 3) : Set ℝ :=
  if negative = true ∧ coord = 0 then (fun z : ℝ => -z) ⁻¹' Icc (2*L) (3*L)
  else Icc (2*L) (3*L)

def box (m : ℕ) (L : ℝ) (negative : Bool) : Set (Seed m) :=
  univ.pi (fun j => boxInterval L negative j.2)

theorem measurable_box (m : ℕ) (L : ℝ) (negative : Bool) :
    MeasurableSet (box m L negative) := by
  apply MeasurableSet.pi (Set.to_countable _)
  intro i _
  unfold boxInterval
  split_ifs
  · exact measurableSet_Icc.preimage measurable_neg
  · exact measurableSet_Icc

/-- A concrete density lower bound for either signed box. The negative box
reflects exactly the readout coordinates of the standard product Gaussian. -/
theorem signed_gaussian_mass (m : ℕ) (L : ℝ) (hL : 0 ≤ L) (negative : Bool) :
    (L * gaussianPDFReal 0 1 (3*L))^(3*m) ≤ (seedLaw m).real (box m L negative) := by
  let G := gaussianReal 0 1
  let I := Icc (2*L) (3*L)
  have equal (i : Fin m × Fin 3) : G (boxInterval L negative i.2) = G I := by
    dsimp [boxInterval]
    split_ifs
    · change G ((fun z : ℝ => -z) ⁻¹' I) = G I
      rw [← Measure.map_apply (by fun_prop : Measurable (fun z : ℝ => -z)) (show MeasurableSet I from measurableSet_Icc)]
      simp [G,I, gaussianReal_map_neg]
    · rfl
  simp only [seedLaw, box, measureReal_def, Measure.pi_pi]
  change _ ≤ (∏ i : Fin m × Fin 3, G (boxInterval L negative i.2)).toReal
  simp only [equal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, ENNReal.toReal_pow, mul_comm m 3]
  exact pow_le_pow_left₀ (mul_nonneg hL (gaussianPDFReal_nonneg _ _ _))
    (CircleGrowth.gaussian_interval_mass L hL) _

/-- The joint lower bounds for the actual standard Gaussian parameter law.
The only remaining distribution-level inputs are square integrability at this
finite cap and the bound on the same-seed reference on the positive box. -/
theorem gaussian_moment_bounds (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 16*N*m/η)
    (n : Seed m → ℕ → Net ℂ m) (start : ∀ ω, n ω 0 = initial ω)
    (update : ∀ ω t, n ω (t+1) = step (gridPoint N) (fun i => 1+(gridPoint N i).re)
        (1/Real.sqrt m) (η/(N*Real.sqrt m)) (n ω t))
    (Z : Seed m → ℝ) (B : ℝ) (hF : MemLp (trainedMean n T) 2 (seedLaw m))
    (hZ : MemLp Z 2 (seedLaw m)) (refBound : ∀ ω ∈ box m L false, |Z ω| ≤ B) :
    (L*gaussianPDFReal 0 1 (3*L))^(3*m) * (amplitude m T L)^2 ≤
        variance (trainedMean n T) (seedLaw m) ∧
    (L*gaussianPDFReal 0 1 (3*L))^(3*m) * (max (amplitude m T L-B) 0)^2 ≤
        ∫ ω, (trainedMean n T ω-Z ω)^2 ∂(seedLaw m) := by
  apply box_moment_bounds (seedLaw m) N m T hN hm η L hη hcap hL hscale n update
    (box m L false) (box m L true) (measurable_box ..) (measurable_box ..) _ B
    (signed_gaussian_mass m L hL.le false) (signed_gaussian_mass m L hL.le true)
    _ _ Z hF hZ refBound
  · intro ω hω j
    rw [start]
    exact ⟨(hω (j,0) (Set.mem_univ _)).1, (hω (j,1) (Set.mem_univ _)).1⟩
  · intro ω hω j
    rw [start]
    exact ⟨(hω (j,0) (Set.mem_univ _)).1, (hω (j,1) (Set.mem_univ _)).1⟩

/-- The actual grid-interpolation reference (the grid label average is one). -/
def reference (N m : ℕ) (b : ℝ) (ω : Seed m) : ℝ :=
  populationMean (1/Real.sqrt m) (initial ω) -
    b*((∑ i, output (1/Real.sqrt m) (initial ω) (gridPoint N i))/N-1)

def referenceCap (m : ℕ) (L : ℝ) : ℝ := 1 + 18*Real.sqrt 2*Real.sqrt m*L^2

theorem reference_on_box (N m : ℕ) (hn : 0 < N) (hm : 0 < m) (L b : ℝ)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (hb' : b ≤ 1) (ω : Seed m) (hω : ω ∈ box m L false) :
    |reference N m b ω| ≤ referenceCap m L := by
  let u := initial ω
  let C := 9*Real.sqrt 2 * L^2
  have cp : 0 ≤ C := by dsimp [C]; positivity
  have ms : 0 < Real.sqrt m := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)
  have np : (0:ℝ) < N := Nat.cast_pos.mpr hn
  have coord (j : Fin m) (k : Fin 3) : ω (j,k) ∈ Icc (2*L) (3*L) := hω (j,k) (mem_univ _)
  have bound (j : Fin m) : 0 ≤ u.a j ∧ u.a j * ‖u.w j‖ ≤ C := by
    have apos := (coord j 0).1
    have acap := (coord j 0).2
    have pos₁ := (coord j 1).1
    have pos₂ := (coord j 2).1
    have sq₁ := pow_le_pow_left₀ (by linarith : 0 ≤ ω (j,1)) (coord j 1).2 2
    have sq₂ := pow_le_pow_left₀ (by linarith : 0 ≤ ω (j,2)) (coord j 2).2 2
    have wc : ‖u.w j‖ ≤ 3*L*Real.sqrt 2 := by
      rw [Complex.norm_def, Real.sqrt_le_iff, Complex.normSq_apply]
      constructor
      · positivity
      · change ω (j,1)*ω (j,1)+ω (j,2)*ω (j,2) ≤ _
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
        nlinarith
    constructor
    · change 0 ≤ ω (j,0); linarith
    · calc
        _ ≤ (3*L)*(3*L*Real.sqrt 2) :=
          mul_le_mul acap wc (norm_nonneg _) (by linarith)
        _ = _ := by dsimp [C]; ring
  have sm : (1/Real.sqrt m) * m = Real.sqrt m := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg m)
    field_simp
    linarith
  have budget (f : Fin m → ℝ) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ ‖u.w j‖) :
      0 ≤ (1/Real.sqrt m)*∑ j, u.a j*f j ∧
      (1/Real.sqrt m)*∑ j, u.a j*f j ≤ Real.sqrt m*C := by
    constructor
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (bound j).1 (hf j).1)
    · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
          (mul_le_mul_of_nonneg_left (hf j).2 (bound j).1).trans (bound j).2)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have h := mul_le_mul_of_nonneg_left hsum (one_div_pos.mpr ms).le
      rwa [← mul_assoc, sm] at h
  have pr := budget (fun j => ‖u.w j‖) (fun j => ⟨norm_nonneg _, le_rfl⟩)
  have row (i : Fin N) : 0 ≤ output (1/Real.sqrt m) u (gridPoint N i) ∧
      output (1/Real.sqrt m) u (gridPoint N i) ≤ Real.sqrt m*C := by
    unfold output
    apply budget (fun j => feature (u.w j) (gridPoint N i))
    intro j
    refine ⟨le_max_right _ _, max_le ?_ (norm_nonneg _)⟩
    simpa [grid_norm] using real_inner_le_norm (u.w j) (gridPoint N i)
  let avg := (∑ i, output (1/Real.sqrt m) u (gridPoint N i))/N
  have ag : 0 ≤ avg := div_nonneg (Finset.sum_nonneg (fun i _ => (row i).1)) np.le
  have ac : avg ≤ Real.sqrt m*C := by
    apply (div_le_iff₀ np).mpr
    simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (row i).2)
  let mean := populationMean (1/Real.sqrt m) u
  have meq : mean = ((1/Real.sqrt m)*∑ j, u.a j*‖u.w j‖)/Real.pi := by
    dsimp [mean,populationMean]; ring
  have mq : 0 ≤ mean := by rw [meq]; exact div_nonneg pr.1 Real.pi_pos.le
  have mc : mean ≤ Real.sqrt m*C := by
    rw [meq]
    exact (div_le_self pr.1 (by linarith [Real.pi_gt_three])).trans pr.2
  have cnonneg := mul_nonneg (Real.sqrt_nonneg m) cp
  have hba : b*avg ≤ Real.sqrt m*C := by
    calc _ ≤ 1*avg := mul_le_mul_of_nonneg_right hb' ag
         _ ≤ _ := by simpa using ac
  change |mean-b*(avg-1)| ≤ referenceCap m L
  have coeff : referenceCap m L = 1+2*(Real.sqrt m*C) := by dsimp [referenceCap,C]; ring
  rw [coeff]
  exact abs_le.mpr ⟨by nlinarith, by nlinarith [mul_nonneg hb ag]⟩

theorem exponential_mass (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 16*N*m/η) :
    Real.exp (-14*m*L^2) ≤ (L*gaussianPDFReal 0 1 (3*L))^(3*m) := by
  have hN' : (3:ℝ) ≤ N := by exact_mod_cast hN
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have Lsq : 48 ≤ L^2 := by
    have h := (eq_div_iff hη.ne').mp hscale
    have prod := mul_le_mul hN' hm' (by norm_num : (0:ℝ) ≤ 1) (Nat.cast_nonneg N)
    nlinarith [mul_le_mul_of_nonneg_left hcap (sq_nonneg L)]
  have sqcap : Real.sqrt (2*Real.pi) ≤ L := Real.sqrt_le_iff.mpr ⟨hL.le, by linarith [Real.pi_lt_four]⟩
  have pref : 1 ≤ L*(Real.sqrt (2*Real.pi))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; simpa using sqcap
  let q := -(3*L)^2/2
  have bound : Real.exp q ≤ L*gaussianPDFReal 0 1 (3*L) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, ← mul_assoc]
    simpa only [one_mul, q] using mul_le_mul_of_nonneg_right pref (Real.exp_pos q).le
  calc
    _ ≤ Real.exp ((3*m:ℕ)*q) := by
      apply Real.exp_le_exp.mpr
      push_cast
      dsimp [q]
      nlinarith [mul_nonneg (Nat.cast_nonneg m) (sq_nonneg L)]
    _ = (Real.exp q)^(3*m) := Real.exp_nat_mul q _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le bound _

/-- Numerical constants as in the signed-box paper bound. Only finite-cap
square integrability of the actual GD output and the reference remains supplied
from outside this theorem. The entire Gaussian box-to-moment chain is checked. -/
theorem benchmark_bounds (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L b : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 16*N*m/η)
    (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Seed m → ℕ → Net ℂ m) (start : ∀ ω, n ω 0 = initial ω)
    (update : ∀ ω t, n ω (t+1) = step (gridPoint N) (fun i => 1+(gridPoint N i).re)
        (1/Real.sqrt m) (η/(N*Real.sqrt m)) (n ω t))
    (hF : MemLp (trainedMean n T) 2 (seedLaw m)) (hZ : MemLp (reference N m b) 2 (seedLaw m)) :
    Real.exp (-14*m*L^2) * (amplitude m T L)^2 ≤ variance (trainedMean n T) (seedLaw m) ∧
    Real.exp (-14*m*L^2) * (max (amplitude m T L-referenceCap m L) 0)^2 ≤
      ∫ ω, (trainedMean n T ω-reference N m b ω)^2 ∂(seedLaw m) := by
  have both := gaussian_moment_bounds N m T hN hm η L hη hcap hL hscale n start update
    _ _ hF hZ (reference_on_box N m (by omega) (by omega) L b hL.le hb hb')
  have mass := exponential_mass N m hN hm η L hη hcap hL hscale
  exact ⟨(mul_le_mul_of_nonneg_right mass (sq_nonneg _)).trans both.1,
    (mul_le_mul_of_nonneg_right mass (sq_nonneg _)).trans both.2⟩

end CircleEscapeBridge
