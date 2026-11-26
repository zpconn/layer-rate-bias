module

public import CircleLayerRates
public import CircleMoment
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic

/-! Continuous-time path estimates for the paired layer-rate comparison.
The grid Hilbert space can carry its RMS inner product. The results use
absolute continuity and almost-everywhere differential equations, so no
classical differentiability at activation crossings is needed. -/

public section
noncomputable section
namespace CircleFlowTracking
open Real MeasureTheory Set Filter
open scoped RealInnerProductSpace

/-- An AC path with nonpositive derivative almost everywhere cannot increase. -/
theorem ac_endpoint_le {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval f 0 T)
    (h : ∀ᵐ s : ℝ, s ∈ Icc 0 T → deriv f s ≤ 0) : f T ≤ f 0 := by
  have hi := intervalIntegral.integral_mono_ae_restrict hT ac.intervalIntegrable_deriv
    (intervalIntegrable_const (c := (0 : ℝ))) ((ae_restrict_iff' measurableSet_Icc).mpr h)
  rw [ac.integral_deriv_eq_sub] at hi
  simpa using hi

/-- Integrating-factor comparison for an AC path with a nonzero forcing ceiling. -/
theorem damped_comparison {f : ℝ → ℝ} {k M T : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval f 0 T)
    (h : ∀ᵐ s : ℝ, s ∈ Icc 0 T → deriv f s + k * f s ≤ k * M) :
    f T ≤ exp (-(k*T)) * (f 0 - M) + M := by
  let v (s : ℝ) := exp (k*s)*(f s-M)
  have he : ContDiff ℝ 1 (fun s : ℝ => exp (k*s)) := by fun_prop
  have hc : ContDiff ℝ 1 (fun _ : ℝ => M) := contDiff_const
  have av : AbsolutelyContinuousOnInterval v 0 T :=
    he.contDiffOn.absolutelyContinuousOnInterval.fun_mul
      (ac.fun_sub hc.contDiffOn.absolutelyContinuousOnInterval)
  have lower := ac_endpoint_le hT av (by
    filter_upwards [h, ac.ae_differentiableAt] with s hs df hmem
    have d := (df (by simpa [uIcc_of_le hT] using hmem)).hasDerivAt
    have ed := ((hasDerivAt_id s).const_mul k).exp
    have vd := ed.mul (d.sub_const M)
    change deriv (fun t : ℝ => exp (k*t)*(f t-M)) s ≤ 0
    rw [show deriv (fun t : ℝ => exp (k*t)*(f t-M)) s = _ from vd.deriv]
    dsimp
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (exp_pos (k*s)).le
      (sub_nonpos.mpr (hs hmem))])
  change exp (k*T)*(f T-M) ≤ exp (k*0)*(f 0-M) at lower
  simp only [mul_zero, exp_zero, one_mul] at lower
  have hmul := mul_le_mul_of_nonneg_left lower (exp_pos (-(k*T))).le
  rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at hmul
  linarith

/-- Scalar Duhamel estimate with the exponential transient kept exact.
In the grid application, `f` is the constant-mode coordinate, `k` its
population eigenvalue and `C` the force from movement of the tangent kernel. -/
theorem projected_mode_tracking {f : ℝ → ℝ} {k C T : ℝ} (hT : 0 ≤ T)
    (hk : 0 < k) (hC : 0 ≤ C) (ac : AbsolutelyContinuousOnInterval f 0 T)
    (force : ∀ᵐ s : ℝ, s ∈ Icc 0 T → |deriv f s + k*f s| ≤ C) :
    |f T - exp (-(k*T))*f 0| ≤ C / k := by
  have h1 := damped_comparison (k := k) (M := C/k) hT ac (by
    filter_upwards [force] with s hs hm
    simpa only [mul_div_cancel₀ _ hk.ne'] using (le_abs_self _).trans (hs hm))
  have h2 := damped_comparison (k := k) (M := C/k) hT ac.fun_neg (by
    filter_upwards [force, ac.ae_differentiableAt] with s hs hf hm
    rw [show deriv (fun i => -f i) s = -deriv f s from
      ((hf (by simpa [uIcc_of_le hT] using hm)).hasDerivAt.neg).deriv]
    have hh := (abs_le.mp (hs hm)).1
    have eq : k*(C/k)=C := by field_simp
    rw [eq]
    linarith)
  have nonneg := mul_nonneg (exp_pos (-(k*T))).le (div_nonneg hC hk.le)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Energy decay for a nonautonomous grid Gram. It suffices that its lower
Rayleigh bound holds along the actual residual almost everywhere. -/
theorem residual_decay {r : ℝ → V} {A : ℝ → V →L[ℝ] V} {k T : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval (fun s => ‖r s‖^2) 0 T)
    (ode : ∀ᵐ s : ℝ, s ∈ Icc 0 T →
      HasDerivAt r (-A s (r s)) s ∧ k*‖r s‖^2 ≤ inner ℝ (r s) (A s (r s))) :
    ‖r T‖ ≤ exp (-(k*T))*‖r 0‖ := by
  have bound := damped_comparison (k := 2*k) (M := 0) hT ac (by
    filter_upwards [ode] with s hs hm
    obtain ⟨dr,ray⟩ := hs hm
    rw [dr.norm_sq.deriv, inner_neg_right]
    linarith)
  have ex : exp (-(2*k*T)) = exp (-(k*T)) ^ 2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  simp only [ex, sub_zero, add_zero] at bound
  nlinarith [norm_nonneg (r T), mul_nonneg (exp_pos (-(k*T))).le (norm_nonneg (r 0)),
    sq_nonneg (‖r T‖ - exp (-(k*T))*‖r 0‖)]

/-- Event splitting retains the original (unconditional) law in the fourth
moment term. The exceptional contribution is weighted by its own mass. -/
theorem all_seed_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {G : Set Ω} {B : ℝ}
    (hG : MeasurableSet G) (hF : MemLp (fun ω => F ω ^ 2) 2 μ)
    (good : ∀ ω ∈ G, |F ω| ≤ B) :
    ∫ ω, F ω ^ 2 ∂μ ≤ B^2 * μ.real G +
        sqrt (∫ ω, F ω ^ 4 ∂μ) * sqrt (μ.real Gᶜ) := by
  have int := hF.integrable (by norm_num)
  rw [← integral_add_compl hG int]
  apply add_le_add _ (CircleMoment.exceptional_second_moment hF Gᶜ)
  have ongood := setIntegral_mono_on int.integrableOn (integrable_const (B^2)).integrableOn hG
    (fun ω hω => (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (good ω hω) 2))
  simpa [setIntegral_const, smul_eq_mul, mul_comm] using ongood


/-- Integrate an exponentially decaying bound on the velocity of an AC observable.
This also applies to the scalar distance travelled by a single neuron. -/
theorem integrated_velocity {u : ℝ → ℝ} {k C T : ℝ} (hT : 0 ≤ T)
    (hk : 0 < k) (hC : 0 ≤ C) (ac : AbsolutelyContinuousOnInterval u 0 T)
    (speed : ∀ᵐ s : ℝ, s ∈ Icc 0 T → |deriv u s| ≤ C * exp (-(k*s))) :
    |u T-u 0| ≤ C/k := by
  let v (s : ℝ) := C/k*(1-exp (-(k*s)))
  have hv : ContDiff ℝ 1 v := by dsimp [v]; fun_prop
  have vd (s : ℝ) : HasDerivAt v (C*exp (-(k*s))) s := by
    have d := ((((hasDerivAt_id s).const_mul k).neg.exp).const_sub 1).const_mul (C/k)
    convert d using 1
    dsimp [v]
    field_simp
    rfl
  have upper {g : ℝ → ℝ} (ag : AbsolutelyContinuousOnInterval g 0 T)
      (hg : ∀ᵐ s : ℝ, s ∈ Icc 0 T → deriv g s ≤ C * exp (-(k*s))) :
      g T-g 0 ≤ C/k := by
    have diff := ac_endpoint_le hT (ag.fun_sub hv.contDiffOn.absolutelyContinuousOnInterval) (by
      filter_upwards [hg, ag.ae_differentiableAt] with s hs hd hm
      have d := (hd (by simpa [uIcc_of_le hT] using hm)).hasDerivAt.sub (vd s)
      change deriv (fun t => g t-v t) s ≤ 0
      rw [show deriv (fun t => g t-v t) s = _ from d.deriv]
      linarith [hs hm])
    simp [v] at diff
    nlinarith [mul_nonneg (div_nonneg hC hk.le) (exp_pos (-(k*T))).le]
  apply abs_le.mpr
  constructor
  · have hn := upper ac.fun_neg (by
      filter_upwards [speed, ac.ae_differentiableAt] with s hs hf hm
      rw [show deriv (fun i => -u i) s = -deriv u s from
        ((hf (by simpa [uIcc_of_le hT] using hm)).hasDerivAt.neg).deriv]
      linarith [(abs_le.mp (hs hm)).1])
    linarith
  · exact upper ac (by filter_upwards [speed] with s hs hm; exact (le_abs_self _).trans (hs hm))

/-- The projected output telescopes in continuous time. The discrepancy of
the two evolving kernel rows is integrated against the decaying residual. -/
theorem projected_output {r : ℝ → V} {Y : ℝ → ℝ} {A : ℝ → V →L[ℝ] V}
    {g : ℝ → V →L[ℝ] ℝ} (p : V →L[ℝ] ℝ) {k e R T : ℝ}
    (hT : 0 ≤ T) (hk : 0 < k) (he : 0 ≤ e) (hR : 0 ≤ R)
    (ac : AbsolutelyContinuousOnInterval (fun s => Y s - p (r s)) 0 T)
    (ode : ∀ᵐ s : ℝ, s ∈ Icc 0 T →
      HasDerivAt r (-A s (r s)) s ∧ HasDerivAt Y (-g s (r s)) s ∧
      ‖g s - p.comp (A s)‖ ≤ e ∧ ‖r s‖ ≤ R*exp (-(k*s))) :
    |(Y T-p (r T))-(Y 0-p (r 0))| ≤ e*R/k := by
  apply integrated_velocity hT hk (mul_nonneg he hR) ac
  filter_upwards [ode] with s hs hm
  obtain ⟨dr,dY,de,dec⟩ := hs hm
  have diff := dY.sub (p.hasFDerivAt.comp_hasDerivAt s dr)
  rw [show deriv (fun t => Y t - p (r t)) s = _ from diff.deriv]
  simp only [map_neg, sub_neg_eq_add]
  have h := (g s - p.comp (A s)).le_opNorm (r s)
  rw [Real.norm_eq_abs] at h
  simp only [sub_apply, ContinuousLinearMap.comp_apply] at h
  rw [show -g s (r s)+p ((A s) (r s)) = -(g s (r s)-p ((A s) (r s))) by ring, abs_neg]
  exact h.trans ((mul_le_mul de dec (norm_nonneg _) he).trans_eq (by ring))

/-- Population eigenrow and operator perturbation give the forcing input to
the scalar Duhamel estimate for the constant Fourier mode. -/
theorem eigenrow_force {r : ℝ → V} {A : ℝ → V →L[ℝ] V}
    (p : V →L[ℝ] ℝ) (A₀ : V →L[ℝ] V) {s k e R : ℝ}
    (eig : ∀ x, p (A₀ x) = k * p x) (dr : HasDerivAt r (-A s (r s)) s)
    (close : ‖A₀ - A s‖ ≤ e) (small : ‖r s‖ ≤ R) (he : 0 ≤ e) :
    |deriv (fun t => p (r t)) s + k*p (r s)| ≤ ‖p‖*(e*R) := by
  have dp := p.hasFDerivAt.comp_hasDerivAt s dr
  rw [show deriv (fun t => p (r t)) s = _ from dp.deriv, map_neg, ← eig]
  calc
    _ = |p ((A₀-A s) (r s))| := by simp; ring_nf
    _ ≤ ‖p‖*‖(A₀-A s) (r s)‖ := p.le_opNorm _
    _ ≤ _ := mul_le_mul_of_nonneg_left (((A₀-A s).le_opNorm _).trans
      (mul_le_mul close small (norm_nonneg _) he)) (norm_nonneg _)

/-- First-exit argument for a continuous displacement monitor. If every
strictly confined prefix pays for a strict displacement improvement at its
endpoint, no first exit is possible, including at the final time. -/
theorem no_first_exit {d : ℝ → ℝ} {ρ T : ℝ}
    (hd : ContinuousOn d (Icc 0 T))
    (improve : ∀ t ∈ Icc 0 T, (∀ s ∈ Ico 0 t, d s < ρ) → d t < ρ) :
    ∀ t ∈ Icc 0 T, d t < ρ := by
  intro t ht
  by_contra! bad
  let S := Icc 0 T ∩ d ⁻¹' Ici ρ
  have hclosed : IsClosed S := hd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨u, hu, first⟩ := hcompact.exists_isMinOn ⟨t, ht, bad⟩ continuous_id.continuousOn
  have hu' := improve u hu.1 (by
    intro s hs
    by_contra! hds
    exact hs.2.not_ge (isMinOn_iff.mp first s ⟨⟨hs.1, hs.2.le.trans hu.1.2⟩, hds⟩))
  exact hu'.not_ge hu.2

/-- Relative speed on the confined prefix yields a strict improvement in
the circle radius, with the zero-initial-length case separately covered by
the non-strict integrated velocity estimate. -/
theorem relative_displacement {d : ℝ → ℝ} {T ρ k L R W : ℝ}
    (hT : 0 ≤ T) (hk : 0 < k) (small : ρ < 1)
    (hL : 0 < L) (hR : 0 ≤ R) (hW : 0 < W)
    (budget : 2*R/(W*k) ≤ ρ/2) (hρpos : 0 < ρ)
    (ac : AbsolutelyContinuousOnInterval d 0 T) (start : d 0 = 0)
    (speed : ∀ᵐ s : ℝ, s ∈ Icc 0 T →
      |deriv d s| ≤ (2*R/W*((1+ρ)*L))*exp (-(k*s))) : d T < ρ*L := by
  have h := integrated_velocity hT hk (C := 2*R/W*((1+ρ)*L)) (by positivity) ac speed
  rw [start, sub_zero] at h
  calc
    d T ≤ |d T| := le_abs_self _
    _ ≤ _ := h
    _ = (2*R/(W*k))*((1+ρ)*L) := by ring
    _ ≤ (ρ/2)*((1+ρ)*L) := by gcongr
    _ < ρ*L := by nlinarith [mul_pos (mul_pos hρpos hL) (sub_pos.mpr small)]



/-- At the first potential exit of any positive-length neuron, all distances
on the preceding prefix are below their individual radii. On that prefix the
decaying residual and the raw relative speed law pay for a strict improvement
for the exiting neuron. This closes simultaneous confinement for finite width. -/
theorem neuron_tubes {ι : Type*} [Finite ι] (d : ι → ℝ → ℝ) (L : ι → ℝ)
    {q : ℝ → ℝ} {T k ρ R W : ℝ} (hT : 0 ≤ T) (hk : 0 < k) (hρ : 0 < ρ)
    (small : ρ < 1) (hR : 0 ≤ R) (hW : 0 < W) (hL : ∀ i, 0 < L i)
    (budget : 2*R/(W*k) ≤ ρ/2) (ac : ∀ i, AbsolutelyContinuousOnInterval (d i) 0 T)
    (start : ∀ i, d i 0 = 0) (dist : ∀ i s, 0 ≤ d i s)
    (speed : ∀ i, ∀ᵐ s : ℝ, s ∈ Icc 0 T → |deriv (d i) s| ≤ (2*q s/W)*(L i+d i s))
    (decay : ∀ t ∈ Icc 0 T, (∀ s ∈ Ico 0 t, ∀ i, d i s < ρ*L i) →
        ∀ s ∈ Ico 0 t, q s ≤ R*exp (-(k*s))) :
    ∀ t ∈ Icc 0 T, ∀ i, d i t < ρ*L i := by
  let S (i : ι) := Icc 0 T ∩ d i ⁻¹' Ici (ρ*L i)
  have compact (i : ι) : IsCompact (S i) := by
    have cont : ContinuousOn (d i) (Icc 0 T) := by
      simpa [uIcc_of_le hT] using (ac i).continuousOn
    exact isCompact_Icc.of_isClosed_subset
      (cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  intro t ht i
  by_contra! fail
  have ne : (⋃ i, S i).Nonempty := ⟨t, mem_iUnion.mpr ⟨i, ht, fail⟩⟩
  obtain ⟨u, hu, first⟩ := (isCompact_iUnion compact).exists_isMinOn ne continuous_id.continuousOn
  obtain ⟨j, hj⟩ := mem_iUnion.mp hu
  have hu : u ∈ Icc 0 T := hj.1
  have pref (s : ℝ) (hs : s ∈ Ico 0 u) (j : ι) : d j s < ρ*L j := by
    by_contra! nd
    exact hs.2.not_ge (isMinOn_iff.mp first s (mem_iUnion.mpr
      ⟨j, ⟨hs.1, hs.2.le.trans hu.2⟩, nd⟩))
  have acu : AbsolutelyContinuousOnInterval (d j) 0 u := (ac j).mono
    (by rw [uIcc_of_le hT, uIcc_of_le hu.1]; exact Icc_subset_Icc_right hu.2)
  have tight := relative_displacement hu.1 hk small (hL j) hR hW budget hρ acu (start j) (by
    filter_upwards [speed j, volume.ae_ne u] with s hs ne hm
    have hsu : s ∈ Ico 0 u := ⟨hm.1, lt_of_le_of_ne hm.2 ne⟩
    have qbound := decay u hu pref s hsu
    have dbound := pref s hsu j
    calc
      |deriv (d j) s| ≤ _ := hs ⟨hm.1, hm.2.trans hu.2⟩
      _ ≤ (2*(R*exp (-(k*s)))/W)*((1+ρ)*L j) := by
        apply mul_le_mul
        · gcongr
        · linarith
        · linarith [hL j, dist j s]
        · positivity
      _ = _ := by ring)
  exact tight.not_ge hj.2

/-- For a zero-length initial unit a relative-speed law with locally bounded
coefficient keeps its distance at zero. No division by the initial length. -/
theorem zero_unit_fixed {d : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval d 0 T) (start : d 0 = 0) (dist : 0 ≤ d T)
    (speed : ∀ᵐ s : ℝ, s ∈ Icc 0 T → deriv d s ≤ c*d s) : d T = 0 := by
  have h := damped_comparison (k := -c) (M := 0) hT ac (by
    filter_upwards [speed] with s hs hm
    linarith [hs hm])
  simpa [start] using le_antisymm (by simpa [start] using h) dist

/-- Transfer the population Rayleigh lower bound to the moving Gram. This
is the step that pays for residual decay on the confining event. -/
theorem rayleigh_perturbation (A₀ A : V →L[ℝ] V) {lam e : ℝ}
    (population : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A₀ v))
    (close : ‖A₀-A‖ ≤ e) (small : e ≤ lam/2) (v : V) :
    (lam/2)*‖v‖^2 ≤ inner ℝ v (A v) := by
  have op := ((A₀-A).le_opNorm v).trans (mul_le_mul_of_nonneg_right close (norm_nonneg v))
  have cs := (real_inner_le_norm v ((A₀-A) v)).trans
    (mul_le_mul_of_nonneg_left op (norm_nonneg v))
  simp only [sub_apply, inner_sub_right] at cs
  nlinarith [population v, mul_le_mul_of_nonneg_right small (sq_nonneg ‖v‖)]

/-- Deterministic nonlinear tracking at every time in the confining event.
`A` and `g` are the normalized evolving grid and population-mean operators.
Only their distances from the population operators and the residual ODE
are input. Both the decay envelope and constant-mode force are derived. -/
theorem nonlinear_tracking {r : ℝ → V} {Y : ℝ → ℝ} {A : ℝ → V →L[ℝ] V}
    {g : ℝ → V →L[ℝ] ℝ} (p : V →L[ℝ] ℝ) (A₀ : V →L[ℝ] V) {k γ e R T : ℝ}
    (hT : 0 ≤ T) (hk : 0 < k) (hγ : 0 < γ) (he : 0 ≤ e) (hR : 0 ≤ R)
    (init : ‖r 0‖ ≤ R) (eig : ∀ x, p (A₀ x) = γ * p x)
    (population : ∀ v, (2*k)*‖v‖^2 ≤ inner ℝ v (A₀ v)) (small_error : e ≤ k)
    (energy_ac : AbsolutelyContinuousOnInterval (fun s => ‖r s‖^2) 0 T)
    (mode_ac : AbsolutelyContinuousOnInterval (fun s => p (r s)) 0 T)
    (output_ac : AbsolutelyContinuousOnInterval (fun s => Y s-p (r s)) 0 T)
    (flow : ∀ᵐ s : ℝ, s ∈ Icc 0 T →
      HasDerivAt r (-A s (r s)) s ∧ HasDerivAt Y (-g s (r s)) s ∧
      ‖A₀-A s‖ ≤ e ∧ ‖g s-p.comp A₀‖ ≤ e) :
    |Y T - (Y 0-p (r 0)+exp (-(γ*T))*p (r 0))| ≤
      (1+‖p‖)*e*R/k + ‖p‖*(e*R)/γ := by
  have dec (s : ℝ) (hs : s ∈ Icc 0 T) : ‖r s‖ ≤ R*exp (-(k*s)) := by
    have small : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
    have ac : AbsolutelyContinuousOnInterval (fun t => ‖r t‖^2) 0 s := energy_ac.mono (by simpa [uIcc_of_le hT, uIcc_of_le hs.1] using small)
    have h := residual_decay (A := A) (k := k) hs.1 ac (by
      filter_upwards [flow] with x hx hmem
      obtain ⟨dr, _, pert, _⟩ := hx (small hmem)
      refine ⟨dr, ?_⟩
      have damp := rayleigh_perturbation A₀ (A x) population pert (by linarith) (r x)
      convert damp using 1
      ring)
    exact h.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left init (exp_pos (-(k*s))).le)
  have mode := projected_mode_tracking (k := γ) hT hγ (mul_nonneg (norm_nonneg p)
    (mul_nonneg he hR)) mode_ac (by
      filter_upwards [flow] with s hs hm
      obtain ⟨dr, _, pert, _⟩ := hs hm
      have small := (dec s hm).trans (mul_le_of_le_one_right hR
        ((exp_le_one_iff.mpr (by nlinarith [mul_nonneg hk.le hm.1]))))
      exact eigenrow_force p A₀ eig dr pert small he)
  have out := projected_output p (k := k) (e := (1+‖p‖)*e) hT hk (by positivity) hR output_ac (by
    filter_upwards [flow] with s hs hm
    obtain ⟨dr,dy,close,mean⟩ := hs hm
    refine ⟨dr,dy,?_,dec s hm⟩
    have move := (p.opNorm_comp_le (A₀-A s)).trans
      (mul_le_mul_of_nonneg_left close (norm_nonneg _))
    rw [ContinuousLinearMap.comp_sub] at move
    calc
      ‖g s-p.comp (A s)‖ ≤ ‖g s-p.comp A₀‖+‖p.comp A₀-p.comp (A s)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := (add_le_add mean move).trans_eq (by ring))
  have iden : Y T - (Y 0-p (r 0)+exp (-(γ*T))*p (r 0)) =
      ((Y T-p (r T))-(Y 0-p (r 0))) + (p (r T)-exp (-(γ*T))*p (r 0)) := by ring
  rw [iden]
  exact (abs_add_le _ _).trans (add_le_add out mode)

/-- Odd-circle time written with `sqrt (12*N)*N^3` for exact real arithmetic. -/
def horizon (N : ℝ) : ℕ := ⌈2*π^2*N^2 * log (2*sqrt (12*N)*N^3)⌉₊

/-- The initialization radius for d=128 log N fits the polynomial part
of the chosen logarithmic horizon with this explicit sufficient cutoff. -/
theorem radius_for_horizon {N : ℝ} (hN : 65536 ≤ N) :
    2 + sqrt (8*(128*log N)) ≤ 2*sqrt (12*N) := by
  have hn : 0 < N := by linarith
  have hs := log_le_sub_one_of_pos (sqrt_pos.mpr hn)
  rw [log_sqrt hn.le] at hs
  have hb : 256 ≤ sqrt N := le_sqrt_of_sq_le (by linarith)
  have h12 : 2 ≤ sqrt (12*N) := le_sqrt_of_sq_le (by linarith)
  have hh : 8*(128*log N) ≤ 12*N := by
    nlinarith [sq_sqrt hn.le, mul_nonneg (sqrt_nonneg N) (sub_nonneg.mpr hb)]
  linarith [sqrt_le_sqrt hh]

/-- The common physical time reduces the AC residual to the target RMS. -/
theorem fit_at_horizon {N : ℝ} {r : ℝ → V} {A : ℝ → V →L[ℝ] V}
    (hN : 65536 ≤ N) (init : ‖r 0‖ ≤ 2+sqrt (8*(128*log N)))
    (ac : AbsolutelyContinuousOnInterval (fun s => ‖r s‖^2) 0 (horizon N))
    (ode : ∀ᵐ s : ℝ, s ∈ Icc 0 (horizon N : ℝ) →
      HasDerivAt r (-A s (r s)) s ∧ ‖r s‖^2/(2*π^2*N^2) ≤ inner ℝ (r s) (A s (r s))) :
    ‖r (horizon N)‖ ≤ 1/N^3 := by
  have hn : 0 < N := by linarith
  let sec := 2*π^2*N^2
  let scale := 2*sqrt (12*N)*N^3
  have hsec : 0 < sec := by dsimp [sec]; positivity
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have ceilbound : sec * log scale ≤ (horizon N : ℝ) := Nat.le_ceil _
  have delay : log scale ≤ (1/sec)*(horizon N) := by
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hsec).mpr (by simpa [mul_comm] using ceilbound)
  have edec : exp (-((1/sec)*(horizon N))) ≤ 1/scale := by
    calc
      _ ≤ exp (-(log scale)) := exp_le_exp.mpr (neg_le_neg delay)
      _ = _ := by rw [exp_neg, exp_log hscale, one_div]
  have h := residual_decay (A := A) (k := 1/sec) (by positivity : 0 ≤ (horizon N : ℝ)) ac (by
    filter_upwards [ode] with s hs hm
    obtain ⟨a,b⟩ := hs hm
    exact ⟨a, by simpa [sec, div_eq_mul_inv, mul_comm] using b⟩)
  calc
    _ ≤ _ := h
    _ ≤ 1/scale * (2*sqrt (12*N)) := mul_le_mul edec (init.trans (radius_for_horizon hN))
      (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [scale]; field_simp

/-- On the same measurable initialization event both fits hold and their
training predictions differ by at most twice the tolerance. The complement
bound uses the common seed measure and needs no independence assumption. -/
theorem joint_fit_disagreement {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Set Ω} {δ N : ℝ}
    (r : Bool → Ω → ℝ → V) (A : Bool → Ω → ℝ → V →L[ℝ] V)
    (hN : 65536 ≤ N) (tail : μ.real Gᶜ ≤ δ)
    (init : ∀ ω ∈ G, ∀ i, ‖r i ω 0‖ ≤ 2+sqrt (8*(128*log N)))
    (ac : ∀ ω ∈ G, ∀ i, AbsolutelyContinuousOnInterval (fun s => ‖r i ω s‖^2) 0 (horizon N))
    (ode : ∀ ω ∈ G, ∀ i, ∀ᵐ s : ℝ, s ∈ Icc 0 (horizon N : ℝ) →
      HasDerivAt (r i ω) (-A i ω s (r i ω s)) s ∧
      ‖r i ω s‖^2/(2*π^2*N^2) ≤ inner ℝ (r i ω s) (A i ω s (r i ω s))) :
    μ.real {ω | ¬ ((∀ i, ‖r i ω (horizon N)‖ ≤ 1/N^3) ∧
      ‖r false ω (horizon N)-r true ω (horizon N)‖ ≤ 2/N^3)} ≤ δ := by
  apply (measureReal_mono (s₂ := Gᶜ) _).trans tail
  intro ω wrong hG
  have fit (i : Bool) := fit_at_horizon hN (init ω hG i) (ac ω hG i) (ode ω hG i)
  exact wrong ⟨fit, (norm_sub_le _ _).trans ((add_le_add (fit false) (fit true)).trans_eq (by ring))⟩

/-- Both directions and an explicit absolute gap at fixed initial margin.
`B` bounds the two errors together. The input single-run references share
the exact same seed population and grid means. -/
theorem ordered_population_separation {ys yf q grid bs bf B d : ℝ}
    (track : |ys-CircleLayerRates.reference q grid bs|+
      |yf-CircleLayerRates.reference q grid bf| ≤ B)
    (hb : 0 < bs-bf) (hd : 0 < d) (away : d ≤ |1-grid|)
    (budget : B ≤ (bs-bf)*d/2) :
    0 < (1-grid)*(ys-yf) ∧ (bs-bf)*d/2 ≤ |ys-yf| := by
  let zs := CircleLayerRates.reference q grid bs
  let zf := CircleLayerRates.reference q grid bf
  have ids : zs-zf=(bs-bf)*(1-grid) := CircleLayerRates.reference_difference _ _ _ _
  change |ys-zs|+|yf-zf| ≤ B at track
  have lo := (abs_le.mp (le_rfl : |ys-zs| ≤ |ys-zs|)).1
  have hi := (le_abs_self (ys-zs))
  have lo' := (abs_le.mp (le_rfl : |yf-zf| ≤ |yf-zf|)).1
  have hi' := (le_abs_self (yf-zf))
  rcases le_or_gt 0 (1-grid) with plus | minus
  · rw [abs_of_nonneg plus] at away
    have sep := mul_le_mul_of_nonneg_left away hb.le
    have lower : (bs-bf)*d/2 ≤ ys-yf := by linarith
    have pos := lt_of_lt_of_le (half_pos (mul_pos hb hd)) lower
    exact ⟨mul_pos (hd.trans_le away) pos, lower.trans (le_abs_self _)⟩
  · rw [abs_of_neg minus] at away
    have sep := mul_le_mul_of_nonneg_left away hb.le
    have upper : (bs-bf)*d/2 ≤ -(ys-yf) := by linarith
    have neg : ys-yf < 0 := by linarith [half_pos (mul_pos hb hd)]
    exact ⟨mul_pos_of_neg_of_neg minus neg, by simpa [abs_of_neg neg] using upper⟩


/-- Fourth-to-second norm transfer with the quarter power of the failure
probability. Each quantity uses the original probability measure. -/
theorem all_seed_rms {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {G : Set Ω} {B M δ : ℝ}
    (hG : MeasurableSet G) (hF : MemLp (fun ω => F ω ^ 2) 2 μ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (good : ∀ ω ∈ G, |F ω| ≤ B) (tail : μ.real Gᶜ ≤ δ)
    (fourth : (∫ ω, F ω^4 ∂μ) ≤ M^4) :
    sqrt (∫ ω, F ω^2 ∂μ) ≤ B + M*sqrt (sqrt δ) := by
  have bound := all_seed_second_moment hG hF good
  have hfour : sqrt (∫ ω, F ω^4 ∂μ) ≤ M^2 := sqrt_le_iff.mpr ⟨sq_nonneg _, by nlinarith⟩
  have exception := mul_le_mul hfour (sqrt_le_sqrt tail) (sqrt_nonneg _) (sq_nonneg _)
  have paid := (mul_le_mul_of_nonneg_left (measureReal_le_one (μ := μ) (s := G)) (sq_nonneg B))
  have sq : (M*sqrt (sqrt δ))^2 = M^2*sqrt δ := by rw [mul_pow, sq_sqrt (sqrt_nonneg δ)]
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg hB (mul_nonneg hM (sqrt_nonneg (sqrt δ)))]

end CircleFlowTracking
