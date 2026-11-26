module

public import CircleDynamics
public import CircleGridMoments
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-! Weighted circle-network flow in Cartesian coordinates. Coordinates 0, 1, 2 of
each neuron are the readout and the two hidden weights. The flow assumption below
asks only for coordinate absolute continuity and the prescribed compatible
velocity almost everywhere. The loss and prediction chain rules are conclusions. -/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CircleFlowPath

abbrev Coord (m : ℕ) := Fin m × Fin 3
abbrev State (m : ℕ) := Coord m → ℝ

variable {m N : ℕ}

/-- Values of a ReLU slope, including all possible choices at zero. -/
def Admissible (s g : ℝ) : Prop :=
  0 ≤ g ∧ g ≤ 1 ∧ (0 < s → g = 1) ∧ (s < 0 → g = 0)

theorem gate_times_input {s g : ℝ} (hg : Admissible s g) :
    g*s = max s 0 := by
  rcases lt_trichotomy s 0 with h|h|h
  · simp [hg.2.2.2 h, max_eq_right h.le]
  · simp [h]
  · simp [hg.2.2.1 h, max_eq_left h.le]

/-- At a common differentiability point, on the zero set the derivative of both
the preactivation and its positive part is zero. This covers arbitrary gates. -/
theorem relu_derivative {f : ℝ → ℝ} {s v g : ℝ}
    (hf : HasDerivAt f v s) (hk : DifferentiableAt ℝ (fun t => max (f t) 0) s)
    (hg : Admissible (f s) g) :
    HasDerivAt (fun t => max (f t) 0) (g*v) s := by
  rcases lt_trichotomy (f s) 0 with h|h|h
  · rw [hg.2.2.2 h, zero_mul]
    apply (hasDerivAt_const s 0).congr_of_eventuallyEq
    exact (hf.continuousAt.eventually_lt continuousAt_const h).mono fun t ht => max_eq_right ht.le
  · have hmin : IsLocalMin (fun t => max (f t) 0) s :=
      Eventually.of_forall fun t => by simp [h]
    have hmin' : IsLocalMin (fun t => max (f t) 0 - f t) s :=
      Eventually.of_forall fun t => by simp [h]
    have hz := hmin.hasDerivAt_eq_zero hk.hasDerivAt
    have hv := hmin'.hasDerivAt_eq_zero (hk.hasDerivAt.sub hf)
    have hzero : v = 0 := by linarith
    simpa [hzero,hz] using hk.hasDerivAt
  · rw [hg.2.2.1 h, one_mul]
    exact hf.congr_of_eventuallyEq ((continuousAt_const.eventually_lt hf.continuousAt h).mono
      fun t ht => max_eq_left ht.le)

def pre (z : State m) (j : Fin m) (x : ℝ × ℝ) : ℝ :=
  x.1*z (j,1) + x.2*z (j,2)

def output (c : ℝ) (z : State m) (x : ℝ × ℝ) : ℝ :=
  c*∑ j, z (j,0)*max (pre z j x) 0

def row (c : ℝ) (z : State m) (x : ℝ × ℝ) (g : Fin m → ℝ) : State m :=
  fun p => c * ![max (pre z p.1 x) 0, z (p.1,0)*g p.1*x.1, z (p.1,0)*g p.1*x.2] p.2

def pair (u v : State m) : ℝ := ∑ p, u p*v p

theorem row_action (c : ℝ) (z v : State m) (x : ℝ × ℝ) (g : Fin m → ℝ) :
    pair (row c z x g) v =
      c*∑ j, (v (j,0)*max (pre z j x) 0 + z (j,0)*g j*pre v j x) := by
  rw [pair, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Fin.sum_univ_three, row, pre]
  ring

theorem homogeneity (c : ℝ) (z : State m) (x : ℝ × ℝ) (g : Fin m → ℝ)
    (hg : ∀ j, Admissible (pre z j x) (g j)) :
    pair (row c z x g) z = 2 * output c z x := by
  rw [row_action, output]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show z (j,0)*g j*pre z j x = z (j,0)*max (pre z j x) 0 by
    rw [mul_assoc, gate_times_input (hg j)]]
  ring

private theorem acsum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {T : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) 0 T) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) 0 T := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show ContDiff ℝ 1 (fun _ : ℝ => (0:ℝ)) by fun_prop).contDiffOn.absolutelyContinuousOnInterval (a:=0) (b:=T)
  | insert i s hi ih =>
    simpa [Finset.sum_insert hi] using (hf i (by simp)).fun_add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem acpre {z : ℝ → State m} {T : ℝ}
    (hz : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T)
    (j : Fin m) (x : ℝ × ℝ) :
    AbsolutelyContinuousOnInterval (fun t => pre (z t) j x) 0 T :=
  ((hz (j,1)).const_mul x.1).fun_add ((hz (j,2)).const_mul x.2)

private theorem acfeature {z : ℝ → State m} {T : ℝ}
    (hz : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T)
    (j : Fin m) (x : ℝ × ℝ) :
    AbsolutelyContinuousOnInterval (fun t => max (pre (z t) j x) 0) 0 T :=
  (LipschitzWith.id.max_const 0).comp_absolutelyContinuousOnInterval (acpre hz j x)

theorem output_ac {z : ℝ → State m} {T : ℝ}
    (hz : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T)
    (c : ℝ) (x : ℝ × ℝ) :
    AbsolutelyContinuousOnInterval (fun t => output c (z t) x) 0 T :=
  (acsum Finset.univ _ (fun j _ => (hz (j,0)).fun_mul (acfeature hz j x))).const_mul c

theorem output_deriv {z : ℝ → State m} {s : ℝ} {v : State m} {c : ℝ} {x : ℝ × ℝ}
    (hv : ∀ p, HasDerivAt (fun t => z t p) (v p) s)
    (hk : ∀ j, DifferentiableAt ℝ (fun t => max (pre (z t) j x) 0) s)
    (g : Fin m → ℝ) (hg : ∀ j, Admissible (pre (z s) j x) (g j)) :
    HasDerivAt (fun t => output c (z t) x) (pair (row c (z s) x g) v) s := by
  rw [row_action]
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro j _
  have hf : HasDerivAt (fun t => pre (z t) j x) (pre v j x) s :=
    ((hv (j,1)).const_mul x.1).add ((hv (j,2)).const_mul x.2)
  simpa [mul_assoc,Pi.mul_def] using! (hv (j,0)).mul (relu_derivative hf (hk j) (hg j))

def rate (τ : ℝ) (p : Coord m) := if p.2 = 0 then 1 else τ

def residual (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c : ℝ) (z : State m) :=
  fun i => output c z (x i) - y i

def loss (r : Fin N → ℝ) := (1/(2*(N:ℝ))) * ∑ i, r i ^ 2

def gradient (J : Fin N → State m) (r : Fin N → ℝ) : State m :=
  fun p => (1/(N:ℝ))*∑ i, r i*J i p

def velocity (τ : ℝ) (J : Fin N → State m) (r : Fin N → ℝ) : State m :=
  fun p => -(rate τ p)*gradient J r p

theorem adjoint (J : Fin N → State m) (r : Fin N → ℝ) (v : State m) :
    pair (gradient J r) v = (1/(N:ℝ))*∑ i, r i*pair (J i) v := by
  simp only [pair, gradient, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

private theorem rate_pos {τ : ℝ} (hτ : 0 < τ) (p : Coord m) : 0 < rate τ p := by
  unfold rate
  split <;> positivity

def kinetic (τ : ℝ) (v : State m) : ℝ := ∑ p, v p ^ 2 / rate τ p

theorem weighted_descent (τ : ℝ) (hτ : 0 < τ) (J : Fin N → State m) (r : Fin N → ℝ) :
    pair (gradient J r) (velocity τ J r) = -kinetic τ (velocity τ J r) := by
  rw [pair, kinetic, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold velocity
  field_simp [(rate_pos hτ p).ne']

theorem weighted_radial (τ : ℝ) (hτ : 0 < τ) (c : ℝ) (x : Fin N → ℝ × ℝ)
    (z : State m) (g : Fin N → Fin m → ℝ) (r : Fin N → ℝ)
    (hg : ∀ i j, Admissible (pre z j (x i)) (g i j)) :
    (∑ p, 2*z p * velocity τ (fun i => row c z (x i) (g i)) r p / rate τ p) =
      -(4/(N:ℝ))*∑ i, r i * output c z (x i) := by
  let J := fun i => row c z (x i) (g i)
  calc
    _ = -2 * pair (gradient J r) z := by
      rw [pair, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [J, velocity]
      field_simp [(rate_pos hτ p).ne']
    _ = _ := by
      rw [adjoint]
      simp only [J, homogeneity _ _ _ _ (hg _), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A realized weighted trajectory on the physical-time interval. The normalized
circle model uses c=1/√m. The slope hypotheses are pointwise and include any
Clarke-compatible convex combination of incident region Jacobians. -/
structure IsFlow (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ T : ℝ)
    (z : ℝ → State m) : Prop where
  ac : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T
  compatible : ∀ᵐ t, t ∈ uIcc 0 T → ∃ g : Fin N → Fin m → ℝ,
    (∀ i j, Admissible (pre (z t) j (x i)) (g i j)) ∧
    ∀ p, HasDerivAt (fun s => z s p)
      (velocity τ (fun i => row c (z t) (x i) (g i)) (residual x y c (z t)) p) t

theorem residual_ac {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ} {c τ T : ℝ}
    (F : IsFlow x y c τ T z) (i : Fin N) :
    AbsolutelyContinuousOnInterval (fun t => residual x y c (z t) i) 0 T :=
  (output_ac F.ac c (x i)).fun_sub
    ((show ContDiff ℝ 1 (fun _ : ℝ => y i) by fun_prop).contDiffOn.absolutelyContinuousOnInterval)

theorem loss_ac {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ} {c τ T : ℝ}
    (F : IsFlow x y c τ T z) :
    AbsolutelyContinuousOnInterval (fun t => loss (residual x y c (z t))) 0 T := by
  apply AbsolutelyContinuousOnInterval.const_mul
  apply acsum
  intro i _
  simpa only [pow_two] using (residual_ac F i).fun_mul (residual_ac F i)

def curveVelocity (z : ℝ → State m) (t : ℝ) : State m :=
  fun p => deriv (fun s => z s p) t

/-- Residual dynamics are derived by differentiating the actual network, including
time spent on a grid kink. The same representing Jacobian appears in both updates. -/
theorem ae_residual_eq {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (F : IsFlow x y c τ T z) :
    ∀ᵐ t, t ∈ uIcc 0 T → ∃ g : Fin N → Fin m → ℝ,
      (∀ i j, Admissible (pre (z t) j (x i)) (g i j)) ∧
      let J := fun i => row c (z t) (x i) (g i)
      curveVelocity z t = velocity τ J (residual x y c (z t)) ∧
        ∀ i, HasDerivAt (fun s => residual x y c (z s) i)
          (pair (J i) (curveVelocity z t)) t := by
  have hfeatures : ∀ᵐ t, ∀ i j, t ∈ uIcc 0 T →
      DifferentiableAt ℝ (fun s => max (pre (z s) j (x i)) 0) t :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => (acfeature F.ac j (x i)).ae_differentiableAt
  filter_upwards [F.compatible,hfeatures] with t ht hk
  intro ht'
  obtain ⟨g,hg,hv⟩ := ht ht'
  have hvel : curveVelocity z t = _ := funext fun p => (hv p).deriv
  refine ⟨g,hg,hvel,?_⟩
  intro i
  rw [hvel]
  exact (output_deriv hv (fun j => hk i j ht') (g i) (hg i)).sub_const _

/-- Exact weighted loss dissipation along every compatible absolutely continuous
training path, a.e. through all activation changes. -/
theorem loss_dissipation {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (F : IsFlow x y c τ T z) :
    ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun s => loss (residual x y c (z s)))
      (-kinetic τ (curveVelocity z t)) t := by
  filter_upwards [ae_residual_eq F] with t ht
  intro hmem
  obtain ⟨g,_,hv,hr⟩ := ht hmem
  let J := fun i => row c (z t) (x i) (g i)
  let r := residual x y c (z t)
  have chain := (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => (hr i).pow 2).const_mul (1/(2*(N:ℝ)))
  convert chain using 1
  · rfl
  rw [hv, ← weighted_descent τ hτ, adjoint]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

theorem radial_derivative {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (F : IsFlow x y c τ T z) :
    ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun s => kinetic τ (z s))
      (-(4/(N:ℝ))*∑ i, residual x y c (z t) i * output c (z t) (x i)) t := by
  filter_upwards [F.compatible] with t h
  intro ht
  obtain ⟨g,hg,hv⟩ := h ht
  rw [← weighted_radial τ hτ c x (z t) g _ hg]
  apply HasDerivAt.fun_sum
  intro p _
  simpa using ((hv p).pow 2).div_const (rate τ p)


private theorem integrate_upper {f : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hac : AbsolutelyContinuousOnInterval f 0 T)
    (bound : ∀ᵐ s, s ∈ uIcc 0 T → deriv f s ≤ C) :
    f T - f 0 ≤ T*C := by
  rw [← hac.integral_deriv_eq_sub]
  have hrestr : deriv f ≤ᵐ[volume.restrict (Icc 0 T)] (fun _ => C) := by
    change ∀ᵐ s ∂volume.restrict (Icc 0 T), deriv f s ≤ C
    rw [ae_restrict_iff' measurableSet_Icc]
    simpa [uIcc_of_le hT] using bound
  simpa [smul_eq_mul] using intervalIntegral.integral_mono_ae_restrict hT
    hac.intervalIntegrable_deriv (intervalIntegrable_const (c:=C)) hrestr

/-- Integrated radial estimate with the actual teacher's empirical mean square. -/
theorem radial_bound {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T) (F : IsFlow x y c τ T z) :
    kinetic τ (z T) - kinetic τ (z 0) ≤ T * ((1/(N:ℝ))*∑ i, y i^2) := by
  apply integrate_upper hT
  · apply acsum
    intro p _
    simpa [div_eq_inv_mul,pow_two] using ((F.ac p).fun_mul (F.ac p)).const_mul (rate τ p)⁻¹
  filter_upwards [radial_derivative hτ F] with t ht
  intro hmem
  rw [(ht hmem).deriv]
  have h : ∀ i, -4*(residual x y c (z t) i * output c (z t) (x i)) ≤ y i ^ 2 := by
    intro i
    unfold residual
    nlinarith [sq_nonneg (2*output c (z t) (x i)-y i)]
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => h i))
    (show 0 ≤ 1/(N:ℝ) by positivity)
  rw [← Finset.mul_sum, ← mul_assoc] at hs
  convert hs using 1
  ring

/-- Integrate the dual inequality 2q⋅v ≤ ‖v‖²_(D⁻¹)+‖q‖²_D against the
loss chain rule. This avoids any hypothesis about integrability of squared speed. -/
theorem path_test_bound {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T) (F : IsFlow x y c τ T z) (q : State m) :
    2*pair q (z T) + loss (residual x y c (z T)) -
      (2*pair q (z 0) + loss (residual x y c (z 0))) ≤ T*(∑ p, rate τ p*(q p)^2) := by
  let l := fun t => loss (residual x y c (z t))
  let pot := fun t => 2*pair q (z t) + l t
  change pot T-pot 0 ≤ _
  apply integrate_upper hT
  · apply AbsolutelyContinuousOnInterval.fun_add _ (loss_ac F)
    apply AbsolutelyContinuousOnInterval.const_mul
    apply acsum
    intro p _
    exact (F.ac p).const_mul _
  filter_upwards [loss_dissipation hτ F,F.compatible] with t hl hv
  intro hmem
  obtain ⟨g,_,hv⟩ := hv hmem
  have hz (p) : HasDerivAt (fun s => z s p) (curveVelocity z t p) t := (hv p).differentiableAt.hasDerivAt
  have hpair := (HasDerivAt.fun_sum (u:=Finset.univ) (fun p _ => (hz p).const_mul (q p))).const_mul 2
  have hpot := hpair.add (hl hmem)
  change deriv pot t ≤ _
  rw [show deriv pot t = 2*pair q (curveVelocity z t) + -kinetic τ (curveVelocity z t) by exact hpot.deriv]
  simp only [pair, kinetic, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hpos := rate_pos hτ p
  have he := sq_nonneg (rate τ p*q p - curveVelocity z t p)
  have hdiv := div_nonneg he hpos.le
  field_simp [hpos.ne'] at hdiv ⊢
  nlinarith

/-- Finite-time squared weighted displacement, bounded by elapsed time times
the actual drop in empirical loss. No smoothness at ReLU kinks is imposed. -/
theorem weighted_displacement {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (hT : 0 ≤ T) (F : IsFlow x y c τ T z) :
    kinetic τ (fun p => z T p-z 0 p) ≤
      T*(loss (residual x y c (z 0))-loss (residual x y c (z T))) := by
  rcases hT.eq_or_lt with he|hp
  · subst T
    simp [kinetic]
  let Δ := fun p => z T p-z 0 p
  let q := fun p => Δ p/(T*rate τ p)
  have h := path_test_bound hτ hp.le F q
  have first : T*(pair q (z T)-pair q (z 0)) = kinetic τ Δ := by
    simp only [pair, kinetic, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [q,Δ]
    field_simp [hp.ne',(rate_pos hτ p).ne']
  have sec : T^2*(∑ p, rate τ p*(q p)^2) = kinetic τ Δ := by
    simp only [kinetic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [q]
    field_simp [hp.ne',(rate_pos hτ p).ne']
  have h' := mul_le_mul_of_nonneg_left h hp.le
  change kinetic τ Δ ≤ _
  nlinarith [first,sec]

/-- For the two benchmark multipliers the squared Euclidean parameter
displacement is bounded by 2tL(0), uniformly in the initial state. -/
theorem euclidean_displacement {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hτ : 0 < τ) (hcap : τ ≤ 2) (hT : 0 ≤ T) (F : IsFlow x y c τ T z) :
    (∑ p, (z T p-z 0 p)^2) ≤ 2*T*loss (residual x y c (z 0)) := by
  let Δ := fun p => z T p-z 0 p
  have h : (∑ p, Δ p^2) ≤ 2*kinetic τ Δ := by
    rw [kinetic, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _
    have hs : rate τ p ≤ 2 := by unfold rate; split <;> linarith
    rw [← mul_div_assoc, le_div_iff₀ (rate_pos hτ p)]
    nlinarith [mul_nonneg (sq_nonneg (Δ p)) (sub_nonneg.mpr hs)]
  have hw := weighted_displacement hτ hT F
  change kinetic τ Δ ≤ _ at hw
  have hL : 0 ≤ loss (residual x y c (z T)) := by unfold loss; positivity
  change (∑ p, Δ p^2) ≤ _
  nlinarith [mul_nonneg hT hL]


/-- Coherent affine combinations of slopes preserve all gate constraints. -/
theorem gate_mix {s g h a b : ℝ} (hg : Admissible s g) (hh : Admissible s h)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) : Admissible s (a*g+b*h) := by
  refine ⟨add_nonneg (mul_nonneg ha hg.1) (mul_nonneg hb hh.1), ?_, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left hg.2.1 ha, mul_le_mul_of_nonneg_left hh.2.1 hb]
  · intro hs
    simpa [hg.2.2.1 hs,hh.2.2.1 hs] using hab
  · intro hs
    simp [hg.2.2.2 hs,hh.2.2.2 hs]

private theorem row_mix (c : ℝ) (z : State m) (x : ℝ × ℝ) (g h : Fin m → ℝ)
    (a b : ℝ) (hab : a+b=1) (p : Coord m) :
    row c z x (fun j => a*g j+b*h j) p = a*row c z x g p+b*row c z x h p := by
  obtain ⟨j,k⟩ := p
  fin_cases k <;> simp [row]
  · linear_combination -(c*max (pre z j x) 0)*hab
  · ring
  · ring

/-- The AD-compatible field contains the convex hull of incident smooth-region
velocities, including at intersections of several grid hyperplanes. -/
def compatibleField (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ) (z : State m) :
    Set (State m) := {v | ∃ g : Fin N → Fin m → ℝ,
      (∀ i j, Admissible (pre z j (x i)) (g i j)) ∧
      v = velocity τ (fun i => row c z (x i) (g i)) (residual x y c z)}

theorem compatibleField_convex (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ) (z : State m) :
    Convex ℝ (compatibleField x y c τ z) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨g,hg,rfl⟩ := hv
  obtain ⟨h,hh,rfl⟩ := hw
  refine ⟨fun i j => a*g i j+b*h i j, fun i j => gate_mix (hg i j) (hh i j) ha hb hab, ?_⟩
  funext p
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,velocity,gradient,row_mix _ _ _ _ _ a b hab,
    mul_add,Finset.sum_add_distrib]
  have move (q : Fin N → Fin m → ℝ) (t : ℝ) :
      (∑ i, residual x y c z i * (t * row c z (x i) (q i) p)) =
      t*∑ i, residual x y c z i * row c z (x i) (q i) p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [move g a, move h b]
  ring

/-- A closed activation cell remembers the sign of each preactivation and permits
both incident choices when that preactivation is zero. -/
def incident (x : Fin N → ℝ × ℝ) (z : State m) (s : Fin N → Fin m → Bool) : Prop :=
  ∀ i j, if s i j then 0 ≤ pre z j (x i) else pre z j (x i) ≤ 0

def branchVelocity (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ)
    (z : State m) (s : Fin N → Fin m → Bool) :=
    velocity τ (fun i => row c z (x i) (fun j => if s i j then 1 else 0)) (residual x y c z)


private theorem strict_feature_differentiable (z : State m) (j : Fin m) (x : ℝ × ℝ)
    (hn : pre z j x ≠ 0) :
    DifferentiableAt ℝ (fun q => max (pre q j x) 0) z := by
  have hp : DifferentiableAt ℝ (fun q : State m => pre q j x) z := by unfold pre; fun_prop
  rcases lt_or_gt_of_ne hn with h|h
  · apply (differentiableAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
    exact (hp.continuousAt.eventually_lt continuousAt_const h).mono fun q hq => max_eq_right hq.le
  · apply hp.congr_of_eventuallyEq
    exact (continuousAt_const.eventually_lt hp.continuousAt h).mono fun q hq => max_eq_left hq.le

/-- On each open activation chamber the branch Jacobian gives the Fréchet
derivative of the actual empirical loss in every parameter direction. -/
theorem strict_loss_fderiv (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c : ℝ)
    (z : State m) (s : Fin N → Fin m → Bool)
    (hs : ∀ i j, if s i j then 0 < pre z j (x i) else pre z j (x i) < 0)
    (v : State m) :
    let J := fun i => row c z (x i) (fun j => if s i j then 1 else 0)
    fderiv ℝ (fun q => loss (residual x y c q)) z v = pair (gradient J (residual x y c z)) v := by
  let g := fun i j => if s i j then (1:ℝ) else 0
  let J := fun i => row c z (x i) (g i)
  let L := fun q : State m => loss (residual x y c q)
  let path := fun t : ℝ => z+t • v
  have p0 : path 0 = z := by simp [path]
  have hp : HasDerivAt path v 0 := by
    simpa [path] using HasDerivAt.const_add z ((hasDerivAt_id (0:ℝ)).smul_const v)
  have hn (i : Fin N) (j : Fin m) : pre z j (x i) ≠ 0 := by
    have h := hs i j
    cases hv : s i j <;> simp [hv] at h <;> linarith
  have hd (i : Fin N) (j : Fin m) := strict_feature_differentiable z j (x i) (hn i j)
  have hL : DifferentiableAt ℝ L z := by
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro i _
    apply DifferentiableAt.pow
    apply DifferentiableAt.sub_const
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.fun_sum
    intro j _
    exact (by fun_prop : DifferentiableAt ℝ (fun q : State m => q (j,0)) z).mul (hd i j)
  have hc (p : Coord m) : HasDerivAt (fun t => path t p) (v p) 0 := by
    simpa [path,Pi.smul_apply] using (HasDerivAt.const_add (z p) ((hasDerivAt_id (0:ℝ)).mul_const (v p)))
  have hg (i : Fin N) (j : Fin m) : Admissible (pre (path 0) j (x i)) (g i j) := by
    rw [p0]
    have h := hs i j
    cases hv : s i j <;> simp [g,hv,Admissible] at h ⊢ <;> linarith
  have hf (i : Fin N) : HasDerivAt (fun t => residual x y c (path t) i) (pair (J i) v) 0 := by
    have hfeat (j : Fin m) : DifferentiableAt ℝ (fun t => max (pre (path t) j (x i)) 0) 0 := by
      have hh := hd i j
      rw [← p0] at hh
      exact hh.comp 0 hp.differentiableAt
    simpa only [p0,residual,J] using! (output_deriv hc hfeat (g i) (hg i)).sub_const (y i)
  have chain := (HasDerivAt.fun_sum (u:=Finset.univ) fun i _ => (hf i).pow 2).const_mul (1/(2*(N:ℝ)))
  have hzd : HasFDerivAt L (fderiv ℝ L z) (path 0) := p0 ▸ hL.hasFDerivAt
  have actual := (hzd.comp_hasDerivAt 0 hp).unique chain
  change fderiv ℝ L z v = pair (gradient J (residual x y c z)) v
  rw [actual,adjoint]
  simp only [p0,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp
  ring

/-- Each coordinate of the strict-chamber branch is the negative
preconditioned partial derivative of the empirical loss. -/
theorem branchVelocity_eq_neg_fderiv (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ)
    (z : State m) (s : Fin N → Fin m → Bool)
    (hs : ∀ i j, if s i j then 0 < pre z j (x i) else pre z j (x i) < 0)
    (p : Coord m) :
    branchVelocity x y c τ z s p =
      -(rate τ p) * fderiv ℝ (fun q => loss (residual x y c q)) z (Pi.single p 1) := by
  rw [strict_loss_fderiv x y c z s hs]
  simp [branchVelocity,velocity,pair,Pi.single_apply]

def incidentField (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ) (z : State m) :
    Set (State m) :=
  convexHull ℝ ((branchVelocity x y c τ z) '' {s | incident x z s})

theorem incidentField_subset (x : Fin N → ℝ × ℝ) (y : Fin N → ℝ) (c τ : ℝ) (z : State m) :
    incidentField x y c τ z ⊆ compatibleField x y c τ z := by
  apply convexHull_min _ (compatibleField_convex x y c τ z)
  rintro _ ⟨s,hs,rfl⟩
  refine ⟨fun i j => if s i j then 1 else 0,?_,rfl⟩
  intro i j
  have hi := hs i j
  cases h : s i j <;> simp [Admissible, h] at hi ⊢ <;> linarith

/-- A concrete hull-valued differential inclusion implies every path estimate
above. One may use a subset of the incident field, in particular the hull of
gradients from full-dimensional activation regions. -/
theorem isFlow_of_incident {z : ℝ → State m} {x : Fin N → ℝ × ℝ} {y : Fin N → ℝ}
    {c τ T : ℝ} (hac : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T)
    (hincl : ∀ᵐ t, t ∈ uIcc 0 T → curveVelocity z t ∈ incidentField x y c τ (z t)) :
    IsFlow x y c τ T z := by
  refine ⟨hac,?_⟩
  have hder : ∀ᵐ t, ∀ p, t ∈ uIcc 0 T → DifferentiableAt ℝ (fun s => z s p) t :=
    ae_all_iff.mpr fun p => (hac p).ae_differentiableAt
  filter_upwards [hder,hincl] with t hd hi
  intro ht
  obtain ⟨g,hg,hv⟩ := incidentField_subset x y c τ (z t) (hi ht)
  refine ⟨g,hg,?_⟩
  intro p
  have hh : HasDerivAt (fun s => z s p) (curveVelocity z t p) t := (hd p ht).hasDerivAt
  rwa [hv] at hh

def circleInput (N : ℕ) (i : Fin N) : ℝ × ℝ :=
  ((CircleEscape.gridPoint N i).re,(CircleEscape.gridPoint N i).im)

def circleLabel (N : ℕ) (i : Fin N) := 1+(circleInput N i).1

theorem circle_teacher_square (hN : 3 ≤ N) :
    (1/(N:ℝ))*∑ i, (circleLabel N i)^2 = 3/2 := by
  have h1 := CircleGridMoments.projection_sum N hN 1
  have h2 := CircleGridMoments.projection_sq_sum N hN 1
  simp [Complex.inner] at h1 h2
  let v := fun i => (CircleEscape.gridPoint N i).re
  change (∑ i, v i) = 0 at h1
  change (∑ i, v i ^ 2) = (N:ℝ)/2 at h2
  have he (i : Fin N) : (circleLabel N i)^2 = 1 + 2*v i + v i^2 := by
    dsimp [circleLabel,circleInput,v]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,h1,h2,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

/-- Simultaneously the model's radial continuation bound and the Euclidean
displacement bound on the normalized circle design, including both layer rates. -/
theorem circle_path_bounds {z : ℝ → State m} {τ T : ℝ} (hN : 3 ≤ N)
    (hτ : 0 < τ) (hcap : τ ≤ 2) (hT : 0 ≤ T)
    (F : IsFlow (circleInput N) (circleLabel N) (1/Real.sqrt m) τ T z) :
    kinetic τ (z T)-kinetic τ (z 0) ≤ 3/2*T ∧
    (∑ p, (z T p-z 0 p)^2) ≤ 2*T*loss (residual (circleInput N) (circleLabel N)
      (1/Real.sqrt m) (z 0)) := by
  constructor
  · have hr := radial_bound hτ hT F
    rw [circle_teacher_square hN,mul_comm T] at hr
    exact hr
  · exact euclidean_displacement hτ hcap hT F

end CircleFlowPath
