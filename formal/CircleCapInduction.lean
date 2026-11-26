module

public import CircleInitializationCheck
public import CircleGridMoments
public import CircleAngularGeometry
public import CircleEscapeBridge
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationCheck
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Actual simultaneous GD energy expansion and the initial spectral cap. -/

public section
noncomputable section
namespace CircleCapInduction
open CircleEscape CircleInitializationCheck
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m N : ℕ}

def rawEnergy (n : Net V m) : ℝ := ∑ j, ((n.a j)^2 + ‖n.w j‖^2)

def energy (n : Net V m) : ℝ := rawEnergy n / m

/-- Squared norm of the transpose of the unscaled network Jacobian acting on z. -/
def jacSq (x : Fin N → V) (n : Net V m) (z : Fin N → ℝ) : ℝ :=
  ∑ j, ((∑ i, z i * feature (n.w j) (x i))^2 +
    (n.a j)^2 * ‖∑ i, (z i * gate (n.w j) (x i)) • x i‖^2)

/-- Rayleigh upper bounds for JJᵀ/N, where the actual Jacobian includes 1/√m. -/
def GramBound (x : Fin N → V) (n : Net V m) (L : ℝ) : Prop :=
  ∀ z, jacSq x n z ≤ (N:ℝ) * m * L * ∑ i, (z i)^2

def IsTopGram (x : Fin N → V) (n : Net V m) (L : ℝ) : Prop :=
  IsLeast {l | GramBound x n l} L

/-- Exact two-block square expansion. The mixed terms coincide by gate_projection,
including at a zero preactivation. -/
theorem raw_energy_step (x : Fin N → V) (y : Fin N → ℝ) (n : Net V m) (c k : ℝ) :
    let r := fun i => output c n (x i) - y i
    rawEnergy (step x y c k n) - rawEnergy n =
      -4*k*(∑ i, r i * ∑ j, n.a j * feature (n.w j) (x i)) + k^2 * jacSq x n r := by
  intro r
  let g := fun j => ∑ i, r i * feature (n.w j) (x i)
  let v := fun j => ∑ i, (r i * gate (n.w j) (x i)) • x i
  have mixed (j : Fin m) : inner ℝ (n.w j) (v j) = g j := by
    simp only [v, g, inner_sum, real_inner_smul_right, mul_assoc, gate_projection]
  have row (j : Fin m) :
      (n.a j-k*g j)^2 + ‖n.w j-(k*n.a j) • v j‖^2 -
        ((n.a j)^2 + ‖n.w j‖^2) =
      -4*k*(n.a j*g j) + k^2*((g j)^2+(n.a j)^2*‖v j‖^2) := by
    rw [norm_sub_sq_real, real_inner_smul_right, mixed, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  have swap : ∑ j, n.a j * g j = ∑ i, r i * ∑ j, n.a j * feature (n.w j) (x i) := by
    simp only [g, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change (∑ j, ((n.a j-k*g j)^2 + ‖n.w j-(k*n.a j) • v j‖^2)) -
      (∑ j, ((n.a j)^2 + ‖n.w j‖^2)) = _
  rw [← Finset.sum_sub_distrib]
  simp_rw [row]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, swap]
  rfl

/-- Once the current curvature is bounded, completing a square at each observation
pays for the next step. The sole spectral hypothesis is the actual Jacobian
Rayleigh bound defined above. -/
theorem actual_increment (x : Fin N → V) (y : Fin N → ℝ) (n : Net V m)
    (hN : 0 < N) (hm : 0 < m) (η L : ℝ) (hη : 0 ≤ η) (cap : η*L ≤ 7/2)
    (bound : GramBound x n L) (labels : ∑ i, (y i)^2 ≤ (3/2:ℝ)*N) :
    (m:ℝ)*(energy (step x y (1/Real.sqrt m) (η/(N*Real.sqrt m)) n) - energy n) ≤ 12*η := by
  let r := fun i => output (1/Real.sqrt m) n (x i) - y i
  let s := Real.sqrt m
  have np : (0:ℝ) < N := by exact_mod_cast hN
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have sp : 0 < s := Real.sqrt_pos.mpr mp
  have sqr : s^2 = m := Real.sq_sqrt mp.le
  have score (i : Fin N) : (∑ j, n.a j * feature (n.w j) (x i)) = s*(r i + y i) := by
    dsimp [r, output, s]; field_simp [Real.sqrt_ne_zero'.mpr mp]; ring
  have expand := raw_energy_step x y n (1/s) (η/(N*s))
  change rawEnergy _ - rawEnergy n = -4*(η/(N*s))*(∑ i, r i * ∑ j,
    n.a j * feature (n.w j) (x i)) + (η/(N*s))^2 * jacSq x n r at expand
  simp_rw [score, show ∀ i, r i * (s * (r i + y i)) = s * (r i * (r i + y i)) by
    intro i; ring] at expand
  rw [← Finset.mul_sum] at expand
  have gn := mul_le_mul_of_nonneg_left (bound r) (sq_nonneg (η/((N:ℝ)*s)))
  have form : (η/((N:ℝ)*s))^2 * ((N:ℝ)*m*L * ∑ i, (r i)^2) =
      (η / N) * (η * L * ∑ i, (r i)^2) := by
    rw [← sqr]; field_simp [sp.ne', np.ne']
  rw [form] at gn
  have row (i : Fin N) : -4 * (r i*(r i+y i)) + η*L*(r i)^2 ≤ 8*(y i)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right cap (sq_nonneg (r i)), sq_nonneg (r i+4*y i)]
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at summed
  have rate := mul_le_mul_of_nonneg_left (summed.trans (by linarith :
      8*(∑ i, (y i)^2) ≤ 8*(3/2:ℝ)*N)) (div_nonneg hη np.le)
  have mixed : -4*(η/((N:ℝ)*s))*(s*(∑ i, r i*(r i+y i))) =
      (η / N)*(-4*(∑ i, r i*(r i+y i)))  := by field_simp
  rw [mixed] at expand
  have endv : η/(N:ℝ)*(8*(3/2:ℝ)*N) = 12*η := by field_simp; ring
  rw [endv, mul_add] at rate
  have cancel (a b : ℝ) : (m:ℝ)*(a/m-b/m) = a-b := by field_simp
  rw [energy, energy, cancel]
  linarith

def C (N : ℕ) : ℝ := 1/4 + 4/N
def ell (N : ℕ) : ℝ := (1/Real.pi-2/N)^2


/-- This test only uses energy increments proved at strictly earlier indices. -/
theorem cap_induction (m T : ℕ) (hm : 0 < m) (C e : ℝ) (hC : 0 ≤ C) (he : 0 < e)
    (P L : ℕ → ℝ) (initial : e * P 0 ≤ L 0) (upper : ∀ s ≤ T, L s ≤ C * P s)
    (span : C/e+12*C*T/m ≤ 7/2)
    (increment : ∀ s < T, capRate (L 0)*L s ≤ 7/2 →
      (m:ℝ)*(P (s+1)-P s) ≤ 12*capRate (L 0)) :
    ∀ s ≤ T, P s ≤ P 0 + 12*capRate (L 0)*s/m ∧ capRate (L 0)*L s ≤ 7/2 := by
  let η := capRate (L 0)
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ max 1 (L 0) := le_max_left _ _
  have hp : 0 < max 1 (L 0) := by linarith
  have ηpos : 0 ≤ η := by dsimp [η,capRate]; positivity
  have ηle : η ≤ 1 := by dsimp [η,capRate]; exact (div_le_iff₀ hp).mpr (by linarith)
  have ηL : η*L 0 ≤ 1 := by
    dsimp [η,capRate]
    rw [one_div, inv_mul_eq_div]
    exact (div_le_one hp).mpr (le_max_right _ _)
  have ini : η*P 0 ≤ 1/e := by
    apply (le_div_iff₀ he).mpr
    nlinarith [mul_le_mul_of_nonneg_left initial ηpos]
  have second (s : ℕ) (hs : s ≤ T) (first : P s ≤ P 0 + 12*η*s/m) :
      η*L s ≤ 7/2 := by
    have st : (s:ℝ) ≤ T := by exact_mod_cast hs
    have etle := (mul_le_mul ηle ηle ηpos (by norm_num : (0:ℝ) ≤ 1))
    have er : η*η*s ≤ T := (mul_le_mul_of_nonneg_right etle (Nat.cast_nonneg s)).trans (by simpa)
    have ext := mul_le_mul_of_nonneg_left er (show 0 ≤ 12*C/(m:ℝ) by positivity)
    have h₁ := mul_le_mul_of_nonneg_left (upper s hs) ηpos
    have h₂ := mul_le_mul_of_nonneg_left first (mul_nonneg ηpos hC)
    have h₃ := mul_le_mul_of_nonneg_left ini hC
    calc
      η * L s ≤ (η*C)*(P 0 + 12*η*s/m) := by linarith only [h₁,h₂]
      _ = C*(η*P 0) + (12*C/m)*(η*η*s) := by ring
      _ ≤ C*(1/e) + (12*C/m)*T := add_le_add h₃ ext
      _ = C/e+12*C*T/m := by ring
      _ ≤ _ := span
  intro s
  induction s with
  | zero => intro hs; exact ⟨by simp, second 0 hs (by simp)⟩
  | succ s ih =>
    intro hs
    obtain ⟨prior, curvature⟩ := ih (Nat.le_of_succ_le hs)
    have inc := increment s (Nat.lt_of_succ_le hs) curvature
    have rise : P (s+1)-P s ≤ 12*η/m := (le_div_iff₀ mp).mpr (by linarith only [inc])
    have next : P (s+1) ≤ P 0 + 12*η*(s+1:ℕ)/m := by
      push_cast
      rw [mul_add, add_div, mul_one]
      linarith
    exact ⟨next,second _ hs next⟩

/-- Numeric verification with π<22/7 for the sharper grid constants. -/
theorem span_81 (N m T : ℕ) (hN : 81 ≤ N) (hm : 0 < m) (hT : 200*T ≤ m) :
    0 < ell N ∧ C N / ell N + 12 * C N * T / m ≤ 7/2 := by
  have n81 : (81:ℝ) ≤ N := by exact_mod_cast hN
  have np : (0:ℝ) < N := by linarith
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have tm : (200:ℝ)*T ≤ m := by exact_mod_cast hT
  have A : (4:ℝ)/N ≤ 4/81 := by apply (div_le_iff₀ np).mpr; linarith
  have B : (2:ℝ)/N ≤ 2/81 := by apply (div_le_iff₀ np).mpr; linarith
  have pi : 7/22 ≤ 1/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_lt_d4]
  have lb : (7/22-2/81:ℝ) ≤ 1/Real.pi-2/N := by linarith
  have elb : (7/22-2/81:ℝ)^2 ≤ ell N := pow_le_pow_left₀ (by norm_num) lb 2
  have ep : 0 < ell N := (by norm_num : (0:ℝ)<(7/22-2/81)^2).trans_le elb
  have ub : C N ≤ 1/4+4/81 := by unfold C; linarith
  have ratio : C N / ell N ≤ (1/4+4/81:ℝ)/(7/22-2/81)^2 := by
    exact div_le_div₀ (by norm_num) ub (by norm_num) elb
  have xt : 12*C N*T/m ≤ 12*(1/4+4/81:ℝ)/200 := by
    apply (div_le_iff₀ mp).mpr
    nlinarith [mul_le_mul_of_nonneg_right ub (Nat.cast_nonneg T)]
  exact ⟨ep, (add_le_add ratio xt).trans (by norm_num)⟩

theorem label_energy (N : ℕ) (hN : 3 ≤ N) :
    ∑ i : Fin N, (1+(gridPoint N i).re)^2 = (3/2:ℝ)*N := by
  have re (i : Fin N) : inner ℝ (1:ℂ) (gridPoint N i) = (gridPoint N i).re := by
    rw [Complex.inner]; simp
  have h1 := CircleGridMoments.projection_sum N hN (1:ℂ)
  have h2 := CircleGridMoments.projection_sq_sum N hN (1:ℂ)
  simp_rw [re] at h1 h2
  simp only [norm_one, one_pow, mul_one] at h2
  simp only [show ∀ r : ℝ, (1+r)^2 = 1+2*r+r^2 by intro r;ring,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, add_zero, h2,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- The actual circle-network recurrence, with the two geometric comparisons
made explicit. The hypothesis on GramBound is the mathematical meaning of L
being a Rayleigh upper bound for the current normalized Jacobian. -/
theorem train_cap (N m T : ℕ) (hN : 3 ≤ N) (hm : 0 < m) (initial : Net ℂ m)
    (L : ℕ → ℝ) (he : 0 < ell N) (span : C N/ell N + 12*C N*T/m ≤ 7/2)
    (lower : ell N*energy initial ≤ L 0)
    (upper : ∀ t ≤ T, L t ≤ C N*energy (train N m (capRate (L 0)) initial t))
    (gram : ∀ t < T, GramBound (gridPoint N) (train N m (capRate (L 0)) initial t) (L t)) :
    ∀ t ≤ T, energy (train N m (capRate (L 0)) initial t) ≤
      energy initial + 12*capRate (L 0)*t/m ∧ capRate (L 0)*L t ≤ 7/2 := by
  have ηpos : 0 ≤ capRate (L 0) := by unfold capRate; positivity
  exact cap_induction m T hm (C N) (ell N) (by unfold C; positivity) he
    (fun t => energy (train N m (capRate (L 0)) initial t)) L lower upper span
    (fun t ht h => actual_increment (gridPoint N) _ _ (by omega) hm _ _ ηpos h
      (gram t ht) (label_energy N hN).le)


private theorem gate_sq (w x : V) : gate w x ^ 2 = gate w x := by
  unfold gate; split <;> norm_num

/-- A bound for *all vector projections* controls the hidden block through its
adjoint, avoiding a factor of two from a coordinatewise or trace bound. -/
theorem gram_upper (x : Fin N → V) (n : Net V m) (hm : 0 < m) (K : ℝ) (hK : 0 ≤ K)
    (quad : ∀ w v : V, (∑ i, gate w (x i) * (inner ℝ v (x i))^2) ≤
      (N:ℝ)*K*‖v‖^2) : GramBound x n (K * energy n) := by
  intro z
  let R := ∑ i, (z i)^2
  have R0 : 0 ≤ R := Finset.sum_nonneg fun i _ => sq_nonneg _
  have cs (f : Fin N → ℝ) : (∑ i, z i*f i)^2 ≤ R*(∑ i, (f i)^2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hidden (w : V) : ‖∑ i, (z i*gate w (x i)) • x i‖^2 ≤ R*((N:ℝ)*K) := by
    let v := ∑ i, (z i*gate w (x i)) • x i
    have proj : ‖v‖^2 = ∑ i, z i*(gate w (x i)*inner ℝ v (x i)) := by
      calc ‖v‖^2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
           _ = _  := by
             change inner ℝ v (∑ i, (z i * gate w (x i)) • x i) = _
             simp only [inner_sum, real_inner_smul_right, mul_assoc]
    have c := cs (fun i => gate w (x i)*inner ℝ v (x i))
    simp only [mul_pow,gate_sq] at c
    rw [← proj] at c
    have est := c.trans (mul_le_mul_of_nonneg_left (quad w v) R0)
    change ‖v‖^2 ≤ _
    by_cases hv : v = 0
    · simpa [hv] using mul_nonneg R0 (mul_nonneg (Nat.cast_nonneg N) hK)
    · apply le_of_mul_le_mul_right (a := ‖v‖^2)
      · nlinarith only [est]
      · positivity
  have readout (w : V) : (∑ i, z i*feature w (x i))^2 ≤ R*((N:ℝ)*K*‖w‖^2) := by
    have q := quad w w
    have id (i : Fin N) : (feature w (x i))^2 = gate w (x i) * (inner ℝ w (x i))^2 := by
      rw [← gate_projection, mul_pow, gate_sq]
    exact (cs _).trans (mul_le_mul_of_nonneg_left (by simpa only [id] using q) R0)
  have row (j : Fin m) : (∑ i, z i*feature (n.w j) (x i))^2 +
      (n.a j)^2*‖∑ i, (z i*gate (n.w j) (x i)) • x i‖^2 ≤
      R*((N:ℝ)*K)*((n.a j)^2+‖n.w j‖^2) := by
    have h := mul_le_mul_of_nonneg_left (hidden (n.w j)) (sq_nonneg (n.a j))
    linarith only [readout (n.w j), h]
  have all := Finset.sum_le_sum (s := Finset.univ) (fun j _ => row j)
  rw [← Finset.mul_sum] at all
  apply all.trans_eq
  unfold energy rawEnergy
  change R*((N:ℝ)*K)*_ = (N:ℝ)*m*(K*(_/m))*R
  field_simp [Nat.cast_ne_zero.mpr hm.ne']


/-- The constant training vector tests the radial hidden component of each
initial neuron. No lower bound on a nonzero hidden radius is required. -/
theorem gram_lower (x : Fin N → V) (n : Net V m) (hN : 0 < N) (hm : 0 < m)
    (q L : ℝ) (hq : 0 ≤ q) (nz : ∀ j, n.w j ≠ 0)
    (angular : ∀ w, ((N:ℝ)*q)*‖w‖ ≤ ∑ i, feature w (x i))
    (upper : GramBound x n L) : q^2 * energy n ≤ L := by
  have np : (0:ℝ) < N := by exact_mod_cast hN
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have nq : 0 ≤ (N:ℝ)*q := mul_nonneg np.le hq
  have row (j : Fin m) :
      ((N:ℝ)*q)^2*((n.a j)^2+‖n.w j‖^2) ≤
      (∑ i, feature (n.w j) (x i))^2 +
        (n.a j)^2*‖∑ i, gate (n.w j) (x i) • x i‖^2 := by
    let w := n.w j
    let v := ∑ i, gate w (x i) • x i
    have proj : inner ℝ w v = ∑ i, feature w (x i) := by
      simp [v, inner_sum, real_inner_smul_right, gate_projection]
    have ref := angular w
    have h : (N:ℝ)*q*‖w‖ ≤ ‖v‖*‖w‖ := by
      calc _ ≤ inner ℝ w v := proj.ge.trans' ref
           _ ≤ _ := (real_inner_le_norm _ _).trans_eq (mul_comm _ _)
    have rad : (N:ℝ)*q ≤ ‖v‖ := le_of_mul_le_mul_right h (norm_pos_iff.mpr (nz j))
    have h1 := pow_le_pow_left₀ (mul_nonneg nq (norm_nonneg w)) ref 2
    have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nq rad 2) (sq_nonneg (n.a j))
    change ((N:ℝ)*q)^2*((n.a j)^2+‖w‖^2) ≤ (∑ i, feature w (x i))^2+(n.a j)^2*‖v‖^2
    nlinarith only [h1,h2]
  have s := Finset.sum_le_sum (s := Finset.univ) (fun j _ => row j)
  rw [← Finset.mul_sum] at s
  have test := upper (fun _ => 1)
  simp only [jacSq, one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at test
  have hr := s.trans test
  unfold energy rawEnergy
  rw [← mul_div_assoc]
  apply (div_le_iff₀ mp).mpr
  apply le_of_mul_le_mul_left (a := (N:ℝ)^2)
  · nlinarith only [hr]
  · positivity

/-- The largest normalized Gram eigenvalue, characterized by its Rayleigh
quotients. Using an infimum of upper bounds avoids any eigenvector choice. -/
def curvature (x : Fin N → V) (n : Net V m) : ℝ := sInf {L | GramBound x n L}

theorem curvature_isTop (x : Fin N → V) (n : Net V m) (hN : 0 < N) (hm : 0 < m)
    (nonempty : ∃ L, GramBound x n L) : IsTopGram x n (curvature x n) := by
  have np : (0:ℝ) < N := by exact_mod_cast hN
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have incl : Set.Nonempty {L | GramBound x n L} := nonempty
  have bdd : BddBelow {L | GramBound x n L} := by
    refine ⟨0, fun L hL => ?_⟩
    have h := hL (fun _ => 1)
    have jpos : 0 ≤ jacSq x n (fun _ => 1) :=
      Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    simp only [one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
    exact nonneg_of_mul_nonneg_right
      (nonneg_of_mul_nonneg_left (jpos.trans h) np) (mul_pos np mp)
  refine ⟨?_, fun l hl => csInf_le bdd hl⟩
  intro z
  by_cases zero : ∀ i, z i = 0
  · simp [jacSq,zero]
  push Not at zero
  obtain ⟨i,hi⟩ := zero
  have sr : 0 < ∑ k, (z k)^2 := lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ i))
  let d := (N:ℝ)*m*∑ k, (z k)^2
  have dp : 0 < d := mul_pos (mul_pos np mp) sr
  have lb : jacSq x n z/d ≤ curvature x n := by
    apply le_csInf incl
    intro l hl
    apply (div_le_iff₀ dp).mpr
    calc _ ≤ _ := hl z
         _ = l*d := by dsimp [d]; ring
  calc _ ≤ curvature x n * d := (div_le_iff₀ dp).mp lb
       _ = _ := by dsimp [d]; ring

/-- Unconditional-in-time deterministic constant selection for an actual network.
The only geometric inputs are single-neuron scalar quadratures on the grid;
upper and lower Gram comparisons and all iterated energy increments are proved. -/
theorem circle_cap_of_quadratures (N m T : ℕ) (hN : 7 ≤ N) (hm : 0 < m)
    (span : C N/ell N + 12*C N*T/m ≤ 7/2)
    (n : Net ℂ m) (nz : ∀ j, n.w j ≠ 0)
    (quad : ∀ w v : ℂ, (∑ i, gate w (gridPoint N i)*(inner ℝ v (gridPoint N i))^2) ≤
      ((N:ℝ)/4+4)*‖v‖^2)
    (avg : ∀ w : ℂ, ((N:ℝ)/Real.pi-2)*‖w‖ ≤ ∑ i, feature w (gridPoint N i)) :
    let η := capRate (curvature (gridPoint N) n)
    ∀ t ≤ T, energy (train N m η n t) ≤ energy n + 12*η*t/m ∧
      η*curvature (gridPoint N) (train N m η n t) ≤ 7/2 := by
  intro η
  have hn : 0 < N := by omega
  have np : (0:ℝ) < N := by exact_mod_cast hn
  have K : 0 ≤ C N := by unfold C; positivity
  have nC : (N:ℝ)*C N = (N:ℝ)/4+4 := by unfold C; field_simp
  have u (s : Net ℂ m) := gram_upper (gridPoint N) s hm (C N) K
    (fun w v => by rw [nC]; exact quad w v)
  have top (s : Net ℂ m) := curvature_isTop (gridPoint N) s hn hm ⟨_,u s⟩
  have n7 : (7:ℝ) ≤ N := by exact_mod_cast hN
  have qpos : 0 < 1/Real.pi-2/(N:ℝ) := by
    have a : (2:ℝ)/N ≤ 2/7 := (div_le_iff₀ np).mpr (by linarith)
    have b : (7:ℝ)/22 ≤ 1/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d4])
    linarith
  have nq : (N:ℝ)*(1/Real.pi-2/N) = N/Real.pi-2 := by field_simp
  have lo := gram_lower (gridPoint N) n hn hm _ _ qpos.le nz (fun w => by rw [nq]; exact avg w) (top n).1
  let L := fun t => curvature (gridPoint N) (train N m η n t)
  have pos : 0 < ell N := sq_pos_of_pos qpos
  exact train_cap N m T (by omega) hm n L pos span lo
    (fun t _ => (top _).2 (u _)) (fun t _ => (top _).1)


/-- The concrete cap theorem. The geometry of the strict active gates,
the normalized Jacobian bounds, and the exact energy increments are proved. -/
theorem circle_cap_of_span (N m T : ℕ) (hN : 7 ≤ N) (odd : Odd N) (hm : 0 < m)
    (span : C N/ell N + 12*C N*T/m ≤ 7/2) (n : Net ℂ m) (nz : ∀ j, n.w j ≠ 0) :
    let η := capRate (curvature (gridPoint N) n)
    ∀ t ≤ T, energy (train N m η n t) ≤ energy n + 12*η*t/m ∧
      η*curvature (gridPoint N) (train N m η n t) ≤ 7/2 :=
  circle_cap_of_quadratures N m T hN hm span n nz
    (CircleAngularGeometry.grid_gated_sq_upper N (by omega) odd)
    (CircleAngularGeometry.grid_mean_lower N (by omega))

/-- Explicit finite range of the actual equal-rate update with its initial
spectral cap. All hidden radii need only be nonzero at initialization. -/
theorem circle_cap_81 (N m T : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (hT : 200*T ≤ m) (n : Net ℂ m) (nz : ∀ j, n.w j ≠ 0) :
    let η := capRate (curvature (gridPoint N) n)
    ∀ t ≤ T, energy (train N m η n t) ≤ energy n + 12*η*t/m ∧
      η*curvature (gridPoint N) (train N m η n t) ≤ 7/2 :=
  circle_cap_of_span N m T (by omega) odd hm (span_81 N m T hN hm hT).2 n nz

/-- The actual deterministic stopping cap used in the growing-grid paper. -/
def fitHorizon (N : ℕ) : ℕ :=
  ⌈2*Real.pi^2*(N:ℝ)^2*Real.log (2*Real.sqrt 12*(N:ℝ)^((7:ℝ)/2))⌉₊

theorem fitHorizon_span (N : ℕ) (hN : 81 ≤ N) : 200 * fitHorizon N ≤ N^32 := by
  have n81 : (81:ℝ) ≤ N := by exact_mod_cast hN
  have np : 0 < (N:ℝ) := by linarith
  have pow4 : (N:ℝ)^((7:ℝ)/2) ≤ (N:ℝ)^4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := (N:ℝ)) (by linarith) (by norm_num : (7:ℝ)/2 ≤ 4)
  have scale : 2*Real.sqrt 12 ≤ (N:ℝ)^2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (12:ℝ)),sq_nonneg ((N:ℝ)-10)]
  have arg : 2*Real.sqrt 12*(N:ℝ)^((7:ℝ)/2) ≤ (N:ℝ)^6 := by
    apply (mul_le_mul scale pow4 (by positivity) (sq_nonneg _)).trans_eq
    ring
  have logb := Real.log_le_log (by positivity) arg
  rw [Real.log_pow] at logb
  have log6 : Real.log (2*Real.sqrt 12*(N:ℝ)^((7:ℝ)/2)) ≤ 6*N := by
    linarith [Real.log_le_self np.le]
  have p20 : 2*Real.pi^2 ≤ 20 := by
    nlinarith [Real.pi_pos,Real.pi_lt_d4,
      mul_self_le_mul_self Real.pi_pos.le (le_of_lt Real.pi_lt_d4)]
  have short : fitHorizon N ≤ 120*N^3 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc _ ≤ (2*Real.pi^2*(N:ℝ)^2)*(6*N) := mul_le_mul_of_nonneg_left log6 (by positivity)
         _ = 2*Real.pi^2*(6*(N:ℝ)^3) := by ring
         _ ≤ 20*(6*(N:ℝ)^3) := mul_le_mul_of_nonneg_right p20 (by positivity)
         _ = _ := by ring
  have giant : 24000 ≤ N^29 :=
    (by norm_num : 24000 ≤ 81^3).trans ((Nat.pow_le_pow_left hN 3).trans
      (Nat.pow_le_pow_right (by omega) (by decide)))
  calc 200*fitHorizon N ≤ 200*(120*N^3) := Nat.mul_le_mul_left _ short
       _ = 24000*N^3 := by ring
       _ ≤ N^29*N^3 := Nat.mul_le_mul_right _ giant
       _ = N^32 := by ring


/-- All updates through the specified fit horizon satisfy both bounds. -/
theorem cap_through_fitHorizon (N : ℕ) (hN : 81 ≤ N) (odd : Odd N)
    (n : Net ℂ (N^32)) (nz : ∀ j, n.w j ≠ 0) :
    let η := capRate (curvature (gridPoint N) n)
    ∀ t ≤ fitHorizon N, energy (train N (N^32) η n t) ≤ energy n + 12*η*t/(N^32:ℕ) ∧
      η*curvature (gridPoint N) (train N (N^32) η n t) ≤ 7/2 :=
  circle_cap_81 N _ _ hN odd (pow_pos (by omega) _) (fitHorizon_span N hN) n nz

open CircleEscapeBridge MeasureTheory ProbabilityTheory

/-- For each width, the real part of every Gaussian-initialized hidden unit is
nonzero almost surely, hence its radius is nonzero as well. -/
theorem gaussian_hidden_ne_zero (m : ℕ) :
    ∀ᵐ ω ∂seedLaw m, ∀ j, (initial ω).w j ≠ 0 := by
  have : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  apply ae_all_iff.mpr
  intro j
  have h : ∀ᵐ ω ∂seedLaw m, ω (j,1) ≠ 0 :=
    Measure.ae_eval_ne (μ := fun _ : Fin m × Fin 3 => gaussianReal 0 1) (j,1) 0
  filter_upwards [h] with ω hw eq
  exact hw (congrArg Complex.re eq)

/-- The fitted-horizon cap on the original product Gaussian space. -/
theorem gaussian_fitHorizon (N : ℕ) (hN : 81 ≤ N) (odd : Odd N) :
    ∀ᵐ ω ∂seedLaw (N^32),
      let n := initial ω
      let η := capRate (curvature (gridPoint N) n)
      ∀ t ≤ fitHorizon N, energy (train N (N^32) η n t) ≤
        energy n + 12*η*t/(N^32:ℕ) ∧ η*curvature (gridPoint N) (train N (N^32) η n t) ≤ 7/2 := by
  filter_upwards [gaussian_hidden_ne_zero (N^32)] with ω nz
  exact cap_through_fitHorizon N hN odd (initial ω) nz

end CircleCapInduction
