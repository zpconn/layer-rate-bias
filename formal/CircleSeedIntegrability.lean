module

public import CircleGridEscape
public import CircleInitializationCheck
import all CircleInitializationCheck
import all CircleEscapeBridge
import all CircleEscape
import Mathlib.Tactic

/-! Finite-cap moments of the actual fixed-step recurrence under the product
Gaussian seed. Constants may depend on the step size, the design and the cap.
The degree of the parameter envelope is at most 3^T. -/

public section
noncomputable section

namespace CircleSeedIntegrability
open CircleEscape CircleEscapeBridge CircleInitializationCheck MeasureTheory ProbabilityTheory

def path (N m : ℕ) (η : ℝ) (ω : Seed m) (t : ℕ) : Net ℂ m := train N m η (initial ω) t

/-- A scalar envelope with all finite moments. -/
def radius {m : ℕ} (ω : Seed m) : ℝ := 1 + ∑ i, |ω i|

private theorem radius_one {m : ℕ} (ω : Seed m) : 1 ≤ radius ω := by
  simp only [radius, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

private theorem radius_power_mem (m d : ℕ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun ω : Seed m => (radius ω)^d) p (seedLaw m) := by
  have radial (q : ENNReal) (hq : q ≠ ⊤) : MemLp (radius (m:=m)) q (seedLaw m) := by
    apply (memLp_const (1:ℝ)).add
    apply memLp_finsetSum
    intro i _
    have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) q hq).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m × Fin 3 => gaussianReal 0 1) i)
    exact h.abs
  rcases d with _ | d
  · simpa using (memLp_const (μ := seedLaw m) (p := p) (1:ℝ))
  · let q : ENNReal := (d+1 : ℕ)
    have hn : q ≠ 0 := by dsimp [q]; positivity
    have ht : q ≠ ⊤ := by dsimp [q]; finiteness
    have h := (radial (p*q) (ENNReal.mul_ne_top hp ht)).norm_rpow_div q
    rw [ENNReal.mul_div_cancel_right hn ht] at h
    have hq : q.toReal = (d+1:ℕ) := ENNReal.toReal_natCast _
    rw [hq] at h
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg ((zero_le_one' ℝ).trans (radius_one _))] using h

private theorem sum_norm_cap {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M) :
    ‖∑ i, v i‖ ≤ Fintype.card ι * M := by
  apply (norm_sum_le _ _).trans
  simpa using Finset.sum_le_card_nsmul Finset.univ (fun i => ‖v i‖) M (fun i _ => hv i)

private def Bounded {m : ℕ} (u : Net ℂ m) (B : ℝ) :=
  ∀ j, |u.a j| ≤ B ∧ ‖u.w j‖ ≤ B

private theorem feature_cap (w x : ℂ) (unit : ‖x‖ ≤ 1) :
    |feature w x| ≤ ‖w‖ := by
  unfold feature
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le ((real_inner_le_norm w x).trans (by
    simpa using mul_le_mul_of_nonneg_left unit (norm_nonneg w))) (norm_nonneg _)

private theorem output_cap {m : ℕ} (c B : ℝ) (hb : 0 ≤ B) (u : Net ℂ m)
    (bound : Bounded u B) (x : ℂ) (hx : ‖x‖ ≤ 1) :
    |output c u x| ≤ (|c| * m)*B^2 := by
  rw [output,abs_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  refine (sum_norm_cap _ (B^2) ?_).trans_eq ?_
  · intro j
    rw [Real.norm_eq_abs, abs_mul, sq]
    exact mul_le_mul (bound j).1 ((feature_cap _ _ hx).trans (bound j).2) (abs_nonneg _) hb
  · simp

private theorem mean_cap {m : ℕ} (c B : ℝ) (hb : 0 ≤ B) (u : Net ℂ m) (bound : Bounded u B) :
    |populationMean c u| ≤ (|c/Real.pi| * m)*B^2 := by
  rw [populationMean,abs_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [← Real.norm_eq_abs]
  refine (sum_norm_cap _ (B^2) ?_).trans_eq ?_
  · intro j
    rw [Real.norm_eq_abs,abs_mul, abs_of_nonneg (norm_nonneg _),sq]
    exact mul_le_mul (bound j).1 (bound j).2 (norm_nonneg _) hb
  · simp

private theorem bound_step {N m : ℕ} (c k B : ℝ) (u : Net ℂ m) (hb : 1 ≤ B) (bound : Bounded u B)
    (x : Fin N → ℂ) (y : Fin N → ℝ) (hu : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, |y i| ≤ 2) :
    Bounded (step x y c k u) ((1 + |k| * N*(|c| * m+2))*B^3) := by
  let r := fun i => output c u (x i)-y i
  let A := |c| * m+2
  have bp : 0 ≤ B := zero_le_one.trans hb
  have hsq : 1 ≤ B^2 := one_le_pow₀ hb
  have hr (i : Fin N) : |r i| ≤ A*B^2 := by
    have h := (abs_sub _ _).trans (add_le_add (output_cap c B bp u bound (x i) (hu i)) (hy i))
    dsimp [r,A]
    linarith
  have b3 : B ≤ B^3 := by nlinarith [mul_le_mul_of_nonneg_left hsq bp]
  intro j
  have fsum := sum_norm_cap (fun i => r i * feature (u.w j) (x i)) (A*B^2*B) (by
    intro i
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hr i) ((feature_cap _ _ (hu i)).trans (bound j).2) (abs_nonneg _) (by dsimp [A]; positivity))
  have wsum := sum_norm_cap (fun i => (r i * gate (u.w j) (x i)) • x i) (A*B^2) (by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    have gateb : |gate (u.w j) (x i)| ≤ 1 := by unfold gate; split <;> norm_num
    calc
      _ ≤ (A*B^2 * 1) * 1 := by
        apply mul_le_mul _ (hu i) (norm_nonneg _) (by dsimp [A]; positivity)
        exact mul_le_mul (hr i) gateb (abs_nonneg _) (by dsimp [A]; positivity)
      _ = _ := by ring)
  simp only [Fintype.card_fin, Real.norm_eq_abs] at fsum wsum
  constructor
  · apply (abs_sub _ _).trans
    rw [abs_mul]
    change |u.a j| + |k| * |∑ i, r i*feature (u.w j) (x i)| ≤ _
    have h := add_le_add ((bound j).1.trans b3) (mul_le_mul_of_nonneg_left fsum (abs_nonneg k))
    dsimp only [A] at h
    linarith
  · apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs, abs_mul]
    change ‖u.w j‖ + |k| * |u.a j| * ‖∑ i, (r i*gate (u.w j) (x i)) • x i‖ ≤ _
    have h := add_le_add ((bound j).2.trans b3) (mul_le_mul
      (mul_le_mul_of_nonneg_left (bound j).1 (abs_nonneg k)) wsum (norm_nonneg _) (by positivity))
    dsimp only [A] at h
    linarith

private theorem initial_bound {m : ℕ} (ω : Seed m) : Bounded (initial ω) (2*radius ω) := by
  have cap (i : Fin m × Fin 3) : |ω i| ≤ radius ω := by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (ω j)) (Finset.mem_univ i)
    dsimp [radius]
    linarith
  intro j
  constructor
  · exact (cap (j,0)).trans (by linarith [radius_one ω])
  · exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      change |ω (j,1)| + |ω (j,2)| ≤ _; linarith [cap (j,1),cap (j,2)])

/-- Pointwise envelope for actual training, for arbitrary deterministic step
size. For each finite cap the coefficient is uniform over every Gaussian seed. -/
theorem parameter_growth (N m : ℕ) (η : ℝ) (t : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (ω : Seed m) j,
      |(path N m η ω t).a j| ≤ C*(radius ω)^(3^t) ∧
      ‖(path N m η ω t).w j‖ ≤ C*(radius ω)^(3^t) := by
  induction t with
  | zero =>
    exact ⟨2, by norm_num, fun ω j => by simpa [path,train] using initial_bound ω j⟩
  | succ t ih =>
    obtain ⟨C,hC,hs⟩ := ih
    let c : ℝ := 1/Real.sqrt m
    let k : ℝ := η/(N*Real.sqrt m)
    let D : ℝ := 1 + |k| * N * (|c| * m + 2)
    have hD : 1 ≤ D := by dsimp [D]; apply le_add_of_nonneg_right; positivity
    refine ⟨D*C^3, one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hC), ?_⟩
    intro ω j
    have hb := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (radius_one ω) (n := 3^t))
    have h := bound_step c k _ (path N m η ω t) hb (hs ω) (gridPoint N)
      (fun i => 1+(gridPoint N i).re) (fun i => (grid_norm N i).le) (by
        intro i
        have hh := Complex.abs_re_le_norm (gridPoint N i)
        rw [grid_norm] at hh
        exact (abs_add_le _ _).trans (by rw [abs_one]; linarith)) j
    change _ ≤ D * (C * (radius ω)^(3^t))^3 ∧ _ ≤ D * (C * (radius ω)^(3^t))^3 at h
    simpa only [path,train,c,k,mul_pow, pow_succ 3, pow_mul, mul_assoc] using h

private theorem feature_meas {Ω : Type*} [MeasurableSpace Ω] {w : Ω → ℂ}
    (hw : Measurable w) (x : ℂ) : Measurable (fun ω => feature (w ω) x) := by
  apply (show Continuous (fun z : ℂ => feature z x) by unfold feature; fun_prop).measurable.comp hw

private theorem gate_meas {Ω : Type*} [MeasurableSpace Ω] {w : Ω → ℂ}
    (hw : Measurable w) (x : ℂ) : Measurable (fun ω => gate (w ω) x) := by
  unfold gate
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt measurable_const
    ((show Continuous (fun z : ℂ => inner ℝ z x) by fun_prop).measurable.comp hw)

private theorem output_meas {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (u : Ω → Net ℂ m)
    (ha : ∀ j, Measurable fun ω => (u ω).a j) (hw : ∀ j, Measurable fun ω => (u ω).w j)
    (c : ℝ) (x : ℂ) : Measurable fun ω => output c (u ω) x := by
  unfold output
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ fun j _ => (ha j).mul (feature_meas (hw j) x)

/-- Every trained parameter is Borel measurable, including when a step lands
exactly at a zero preactivation. -/
theorem parameter_measurable (N m : ℕ) (η : ℝ) (t : ℕ) : ∀ j,
    Measurable (fun ω => (path N m η ω t).a j) ∧
    Measurable (fun ω => (path N m η ω t).w j) := by
  induction t with
  | zero =>
    intro j
    refine ⟨measurable_pi_apply _, ?_⟩
    change Measurable (fun ω : Seed m => (⟨ω (j,1), ω (j,2)⟩ : ℂ))
    have hp : Measurable (fun ω : Seed m => (ω (j,1),ω (j,2))) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    exact Complex.equivRealProdCLM.symm.continuous.measurable.comp hp
  | succ t ih =>
    let u := fun ω => path N m η ω t
    let r := fun ω (i : Fin N) => output (1/Real.sqrt m) (u ω) (gridPoint N i) - (1+(gridPoint N i).re)
    have hr i : Measurable (fun ω => r ω i) := (output_meas u (fun j => (ih j).1)
      (fun j => (ih j).2) _ _).sub measurable_const
    intro j
    constructor
    · apply (ih j).1.sub
      apply measurable_const.mul
      exact Finset.measurable_fun_sum _ fun i _ => (hr i).mul (feature_meas (ih j).2 (gridPoint N i))
    · apply (ih j).2.sub
      apply (measurable_const.mul (ih j).1).smul
      exact Finset.measurable_fun_sum _ fun i _ =>
        ((hr i).mul (gate_meas (ih j).2 (gridPoint N i))).smul measurable_const

private theorem dominated_mem {m d : ℕ} {F : Seed m → ℝ} (meas : Measurable F) (K : ℝ)
    (bound : ∀ ω, |F ω| ≤ K*(radius ω)^d) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp F p (seedLaw m) := by
  apply (radius_power_mem m d p hp).of_le_mul (c := K) meas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have hr := (zero_le_one' ℝ).trans (radius_one ω)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr d)] using bound ω

/-- Gaussian moments for the trained whole-circle mean for every finite
exponent and every deterministic finite training cap. -/
theorem trained_memLp (N m T : ℕ) (η : ℝ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (trainedMean (path N m η) T) p (seedLaw m) := by
  obtain ⟨C,hC,hbound⟩ := parameter_growth N m η T
  let c := 1/Real.sqrt m
  have hmeas : Measurable (trainedMean (path N m η) T) := by
    unfold trainedMean populationMean
    apply measurable_const.mul
    exact Finset.measurable_fun_sum _ fun j _ =>
      (parameter_measurable N m η T j).1.mul (parameter_measurable N m η T j).2.norm
  apply dominated_mem (d := (3^T)*2) hmeas ((|c/Real.pi| * m)*C^2) _ p hp
  intro ω
  have hpB : 0 ≤ C*(radius ω)^(3^T) := by have := radius_one ω; positivity
  have bound := mean_cap c _ hpB (path N m η ω T) (hbound ω)
  simpa only [trainedMean, c, mul_pow, pow_mul, mul_assoc] using bound

/-- Gaussian moments for the full shared-seed reference, including the grid
mean of the initial network. -/
theorem reference_memLp (N m : ℕ) (b : ℝ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (reference N m b) p (seedLaw m) := by
  have initA j : Measurable fun ω : Seed m => (initial ω).a j := (parameter_measurable N m 1 0 j).1
  have initW j : Measurable fun ω : Seed m => (initial ω).w j := (parameter_measurable N m 1 0 j).2
  let c := 1/Real.sqrt m
  have hout (i : Fin N) : MemLp (fun ω : Seed m => output c (initial ω) (gridPoint N i)) p (seedLaw m) := by
    apply dominated_mem (d := 2) (output_meas initial initA initW c _) (|c| * m * 4) _ p hp
    intro ω
    have h := output_cap c _ (by linarith [radius_one ω] : 0 ≤ 2*radius ω) _ (initial_bound ω)
      (gridPoint N i) (grid_norm N i).le
    nlinarith
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hout i)
  unfold reference
  apply (trained_memLp N m 0 1 p hp).sub
  apply MemLp.const_mul
  apply MemLp.sub _ (memLp_const (1:ℝ))
  simpa only [c, div_eq_mul_inv] using hsum.mul_const (N:ℝ)⁻¹

/-- The signed Gaussian cone lower bounds, specialized to the actual learner.
All finite-cap moment and initialization premises are discharged. -/
theorem actual_bounds (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L b : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 64*m/η)
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    Real.exp (-896*m^2/η) * (amplitude m T L)^2 ≤ variance (trainedMean (path N m η) T) (seedLaw m) ∧
    Real.exp (-896*m^2/η) * (max (amplitude m T L-referenceCap m L) 0)^2 ≤
      ∫ ω, (trainedMean (path N m η) T ω-reference N m b ω)^2 ∂(seedLaw m) :=
  CircleGridEscape.benchmark_bounds_uniform N m T hN hm η L b hη hcap hL hscale hb hb'
    (path N m η) (fun _ => rfl) (fun _ _ => rfl) (trained_memLp _ _ _ _ 2 (by norm_num))
    (reference_memLp _ _ _ 2 (by norm_num))

end CircleSeedIntegrability
