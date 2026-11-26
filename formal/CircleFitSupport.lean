module

public import CircleConditioning
public import CircleSynchronizedEscape
import all CircleConditioning
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationCheck
public import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic

/-! Conditional support of the ordinary learner on a finite odd circle grid.
A three-neuron perturbation is zero at every grid point and changes the
circle mean by a strictly positive multiple of its common readout scale. -/
public section
noncomputable section
namespace CircleFitSupport
open Real MeasureTheory ProbabilityTheory Set Filter CircleEscape CircleEscapeBridge CircleInitializationCheck
open CircleConditioning
open scoped InnerProductSpace Topology

private def tilt (h : ℝ) : ℂ := ⟨1,h⟩

private theorem blur (N : ℕ) (hn : 0<N) (odd : Odd N) :
    let h := 1/(2*(N:ℝ))
    (∀ i : Fin N, feature (tilt h) (gridPoint N i) + feature (tilt (-h)) (gridPoint N i) =
      2*feature 1 (gridPoint N i)) ∧
    ‖tilt (-h)‖=‖tilt h‖ ∧ 1<‖tilt h‖ := by
  intro h
  have np : 0<(N:ℝ) := Nat.cast_pos.mpr hn
  have hp : 0<h := by dsimp [h];positivity
  have sq (a : ℝ) : ‖tilt a‖^2=1+a^2 := by rw [Complex.sq_norm,Complex.normSq_apply];dsimp [tilt];ring
  refine ⟨?_,?_,?_⟩
  · intro i
    let x := gridPoint N i
    have m := CircleSynchronizedEscape.grid_gate_margin N hn odd i
    have im : |x.im|≤1 := (Complex.abs_im_le_norm x).trans (grid_norm N i).le
    have z : |h*x.im|≤|x.re| := by
      rw [abs_mul,abs_of_pos hp]
      apply (mul_le_mul_of_nonneg_left im hp.le).trans
      rw [mul_one]
      exact (by dsimp [h];gcongr;linarith : h≤1/(N:ℝ)).trans m
    have atilt (a : ℝ) : inner ℝ (tilt a) x=x.re+a*x.im := by
      simp [Complex.inner,Complex.mul_re,tilt,mul_comm]
    have one : inner ℝ (1:ℂ) x=x.re := by simp [Complex.inner]
    change max (inner ℝ (tilt h) x) 0+max (inner ℝ (tilt (-h)) x) 0 = 2*max (inner ℝ (1:ℂ) x) 0
    rw [atilt,atilt,one,neg_mul]
    by_cases p : 0≤x.re
    · rw [abs_of_nonneg p] at z
      have zz := abs_le.mp z
      rw [max_eq_left (by linarith : 0≤x.re+h*x.im),max_eq_left (by linarith : 0≤x.re+ -(h*x.im)),max_eq_left p];ring
    · have n := le_of_not_ge p
      rw [abs_of_nonpos n] at z
      have zz := abs_le.mp z
      rw [max_eq_right (by linarith : x.re+h*x.im≤0),max_eq_right (by linarith : x.re+ -(h*x.im)≤0),max_eq_right n];ring
  · apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [sq,sq];ring
  · have q := sq h
    nlinarith [sq_pos_of_pos hp,norm_nonneg (tilt h)]

/-- Every real circle mean is attained by an exactly interpolating seed at
width N+5 or greater. -/
theorem exact_mean (N m : ℕ) (hn : 3≤N) (odd : Odd N) (width : N+5≤m) (target : ℝ) :
    ∃ ω : Seed m, (∀ i, output (1/sqrt m) (initial ω) (gridPoint N i)=1+(gridPoint N i).re) ∧
      populationMean (1/sqrt m) (initial ω)=target := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le width
  have eq : m=N+(2+(3+k)) := by omega
  clear hk;subst m
  let m := N+(2+(3+k))
  have mp : (0:ℝ)<m := by exact_mod_cast (show 0<m by dsimp [m];omega)
  let s := sqrt (m:ℝ)
  have sp : 0<s := sqrt_pos.mpr mp
  let h := 1/(2*(N:ℝ))
  let W := ‖tilt h‖
  obtain ⟨zeros,eqW,Wbig⟩ := blur N (by omega) odd
  obtain ⟨A,ap,allA⟩ := aligned_sum N (by omega)
  let Q := (target*(s*π)-(N:ℝ)*(s/A))/(2*(W-1))
  have nz : W-1≠0 := ne_of_gt (sub_pos.mpr Wbig)
  have val : (N:ℝ)*(s/A)+Q*(2*(W-1))=target*(s*π) := by
    dsimp [Q];field_simp;ring
  let u : Net ℂ m :=
    ⟨Fin.append (fun _ : Fin N => s/A) (Fin.append ![s,-s] (Fin.append ![Q,Q,-2*Q] (fun _ : Fin k => 0))),
     Fin.append (gridPoint N) (Fin.append ![(1:ℂ),-1] (Fin.append ![tilt h,tilt (-h),1] (fun _ : Fin k => 1)))⟩
  refine ⟨encode u,?_,?_⟩
  · intro i
    rw [initial_encode]
    let x := gridPoint N i
    have rel : feature (1:ℂ) x-feature (-1:ℂ) x=x.re := by
      simp only [feature,Complex.inner,map_one,map_neg,mul_one,mul_neg,Complex.neg_re]
      by_cases p : 0≤x.re <;> grind
    change (1/s)*(∑ j : Fin (N+(2+(3+k))), u.a j*feature (u.w j) (gridPoint N i)) = _
    rw [Fin.sum_univ_add]
    simp only [u,Fin.append_left,Fin.append_right]
    rw [←Finset.mul_sum,allA i,Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,Fin.sum_univ_two]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,zero_mul,Finset.sum_const_zero,add_zero,Fin.sum_univ_three]
    change (1/s)*(s/A*A+(s*feature 1 x+(-s)*feature (-1) x+
      (Q*feature (tilt h) x+Q*feature (tilt (-h)) x+(-2*Q)*feature 1 x)))=1+x.re
    have z := zeros i
    change feature (tilt h) x+feature (tilt (-h)) x=2*feature 1 x at z
    have sumz : Q*feature (tilt h) x+Q*feature (tilt (-h)) x+(-2*Q)*feature 1 x=0 := by linear_combination Q*z
    rw [sumz,add_zero,div_mul_cancel₀ _ ap.ne',←rel]
    field_simp;ring
  · rw [initial_encode]
    change (1/s/π)*(∑ j : Fin (N+(2+(3+k))),u.a j*‖u.w j‖)=target
    rw [Fin.sum_univ_add]
    simp only [u,Fin.append_left,Fin.append_right,grid_norm,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,Fin.sum_univ_two]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,Fin.sum_univ_three,zero_mul,Finset.sum_const_zero,add_zero]
    change (1/s/π)*((N:ℝ)*(s/A)+(s*‖(1:ℂ)‖+(-s)*‖(-1:ℂ)‖+
      (Q*‖tilt h‖+Q*‖tilt (-h)‖+(-2*Q)*‖(1:ℂ)‖)))=target
    rw [eqW];simp only [norm_neg,norm_one,mul_one,add_neg_cancel]
    change (1/s/π)*((N:ℝ)*(s/A)+(0+(Q*W+Q*W+(-2*Q))))=target
    rw [show (N:ℝ)*(s/A)+(0+(Q*W+Q*W+(-2*Q)))=(N:ℝ)*(s/A)+Q*(2*(W-1)) by ring,val]
    field_simp



/-- At an exact fit, a finite update sequence is continuous in the seed,
including at gate boundaries. This holds for any fixed scalar step. -/
private theorem stationary_continuity (N m : ℕ) (η : ℝ) (ω : Seed m)
    (fit : ∀ i, output (1/sqrt m) (initial ω) (gridPoint N i)=label N i) (t : ℕ) :
    ∀ j, Tendsto (fun ξ => (train N m η (initial ξ) t).a j) (𝓝 ω) (𝓝 ((initial ω).a j)) ∧
      Tendsto (fun ξ => (train N m η (initial ξ) t).w j) (𝓝 ω) (𝓝 ((initial ω).w j)) := by
  induction t with
  | zero =>
    have hx (i : Fin N) (j : Fin m) :
        (output (1/sqrt m) (initial ω) (gridPoint N i)-label N i)*feature ((initial ω).w j) (gridPoint N i)=0 ∧
        (initial ω).a j*(output (1/sqrt m) (initial ω) (gridPoint N i)-label N i)=0 := by rw [fit i,sub_self,zero_mul,mul_zero];exact ⟨rfl,rfl⟩
    exact stationary_stability N m ω hx 0
  | succ t ih =>
    let u := fun ξ => train N m η (initial ξ) t
    let k := η/(N*sqrt m)
    let r := fun i ξ => output (1/sqrt m) (u ξ) (gridPoint N i)-label N i
    have hr (i : Fin N) : Tendsto (r i) (𝓝 ω) (𝓝 0) := by
      simpa only [fit,sub_self] using (output_tendsto ih (gridPoint N i)).sub (tendsto_const_nhds (x:=label N i))
    intro j
    have ar (i : Fin N) : Tendsto (fun ξ => r i ξ*feature ((u ξ).w j) (gridPoint N i)) (𝓝 ω) (𝓝 0) := by
      have f : Tendsto (fun ξ => feature ((u ξ).w j) (gridPoint N i)) (𝓝 ω) (𝓝 (feature ((initial ω).w j) (gridPoint N i))) :=
        ((ih j).2.inner (tendsto_const_nhds (x:=gridPoint N i))).max (tendsto_const_nhds (x:= (0:ℝ)))
      simpa only [zero_mul] using (hr i).mul f
    have wr (i : Fin N) : Tendsto (fun ξ => r i ξ*gate ((u ξ).w j) (gridPoint N i)) (𝓝 ω) (𝓝 0) := by
      apply (hr i).zero_mul_isBoundedUnder_le
      apply isBoundedUnder_of_eventually_le (a:=1)
      exact Eventually.of_forall (fun ξ => by change ‖gate ((u ξ).w j) (gridPoint N i)‖≤1;unfold gate;split <;> norm_num)
    have da := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => ar i)
    have dw := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => (wr i).smul (tendsto_const_nhds (x:=gridPoint N i)))
    simp only [Finset.sum_const_zero,zero_smul] at da dw
    constructor
    · change Tendsto (fun ξ => (u ξ).a j-k*∑ i, r i ξ*feature ((u ξ).w j) (gridPoint N i)) _ _
      simpa only [mul_zero,sub_zero] using (ih j).1.sub ((tendsto_const_nhds (x:=k)).mul da)
    · change Tendsto (fun ξ => (u ξ).w j-(k*(u ξ).a j) • ∑ i, (r i ξ*gate ((u ξ).w j) (gridPoint N i)) • gridPoint N i) _ _
      simpa only [smul_zero,sub_zero] using (ih j).2.sub (((tendsto_const_nhds (x:=k)).mul (ih j).1).smul dw)

/-- A positive-probability set of Gaussian seeds fits at every update up to
H and keeps the population mean in any prescribed nonempty open ball. -/
theorem trajectory_ball_pos (N m H : ℕ) (hn : 3≤N) (odd : Odd N) (width : N+5≤m)
    (η tol target ε : ℝ) (htol : 0<tol) (ep : 0<ε) :
    0 < (seedLaw m).real {ω | ∀ t≤H, let u := train N m η (initial ω) t
      gridRms N m u<tol ∧ populationMean (1/sqrt m) u ∈ Metric.ball target ε} := by
  obtain ⟨ω,fit,mean⟩ := exact_mean N m hn odd width target
  have near (t : ℕ) : ∀ᶠ ξ in 𝓝 ω, let u := train N m η (initial ξ) t
      gridRms N m u<tol ∧ populationMean (1/sqrt m) u ∈ Metric.ball target ε := by
    have coords := stationary_continuity N m η ω fit t
    let r := fun i (ξ : Seed m) => output (1/sqrt m) (train N m η (initial ξ) t) (gridPoint N i)-(1+(gridPoint N i).re)
    have hr (i : Fin N) : Tendsto (r i) (𝓝 ω) (𝓝 0) := by
      simpa only [fit,sub_self] using (output_tendsto coords (gridPoint N i)).sub (tendsto_const_nhds (x:=1+(gridPoint N i).re))
    have z := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => (hr i).pow 2)
    simp only [zero_pow (by decide : 2≠0),Finset.sum_const_zero] at z
    have y := Real.continuous_sqrt.continuousAt.tendsto.comp (z.div_const (N:ℝ))
    rw [zero_div,sqrt_zero] at y
    have mu : Tendsto (fun ξ => populationMean (1/sqrt m) (train N m η (initial ξ) t)) (𝓝 ω) (𝓝 target) := by
      rw [←mean]
      exact tendsto_const_nhds.mul (tendsto_finsetSum _ (fun j _ => (coords j).1.mul (coords j).2.norm))
    exact (y.eventually_lt tendsto_const_nhds htol).and (mu (Metric.ball_mem_nhds _ ep))
  apply seed_neighborhood_pos (ω:=ω)
  filter_upwards [(Finset.range (H+1)).eventually_all.mpr (fun t _ => near t)] with ξ hξ
  exact fun t ht => hξ t (Finset.mem_range.mpr (by omega))

private theorem support_of_positive_balls {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (mE : MeasurableSet E)
    (Y : Ω → ℝ) (ym : Measurable Y)
    (joint : ∀ target ε : ℝ, 0<ε → 0<μ.real (E ∩ Y ⁻¹' Metric.ball target ε)) :
    ((cond μ E).map Y).support=univ := by
  apply Set.eq_univ_iff_forall.mpr;intro target
  apply (Measure.mem_support_iff_forall _).mpr
  intro U nh
  obtain ⟨ε,ep,sub⟩ := Metric.mem_nhds_iff.mp nh
  apply lt_of_lt_of_le _ (measure_mono sub)
  rw [Measure.map_apply ym Metric.isOpen_ball.measurableSet,cond_apply mE μ]
  have pos := joint target ε ep
  have nz : μ (E ∩ Y ⁻¹' Metric.ball target ε) ≠ 0 := by
    intro e;rw [Measure.real,e,ENNReal.toReal_zero] at pos;exact (lt_irrefl _ pos)
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) nz

private theorem select_measurable {Ω : Type*} [MeasurableSpace Ω] (f : ℕ → Ω → ℝ)
    (mf : ∀ t, Measurable (f t)) (stop : Ω→ℕ) (ms : Measurable stop) :
    Measurable (fun ω => f (stop ω) ω) := by
  let g := fun u : Ω × ℕ => f u.2 u.1
  have m : Measurable g := measurable_from_prod_countable_left mf
  exact m.comp (measurable_id.prodMk ms)

/-- Condition on the grid fit observed at any bounded measurable update
(including the fixed cap or first hit). The actual conditional population
mean has support the whole real line. -/
theorem conditional_support (N m H : ℕ) (hn : 3≤N) (odd : Odd N) (width : N+5≤m)
    (η tol : ℝ) (htol : 0<tol) (stop : Seed m → ℕ) (ms : Measurable stop) (hs : ∀ ω, stop ω≤H) :
    let u := fun ω => train N m η (initial ω) (stop ω)
    let E := {ω | gridRms N m (u ω)≤tol}
    let Y := fun ω => populationMean (1/sqrt m) (u ω)
    ((cond (seedLaw m) E).map Y).support=univ := by
  intro u E Y
  have stat := random_rate_statistics N m (fun _ => η) measurable_const
  have rm := select_measurable (fun t ω => gridRms N m (train N m η (initial ω) t)) (fun t => (stat t).1) stop ms
  have ym := select_measurable (fun t ω => populationMean (1/sqrt m) (train N m η (initial ω) t)) (fun t => (stat t).2) stop ms
  have mE : MeasurableSet E := measurableSet_le rm measurable_const
  apply support_of_positive_balls (seedLaw m) E mE Y ym
  intro target ε ep
  have hit := trajectory_ball_pos N m H hn odd width η tol target ε htol ep
  apply hit.trans_le
  exact measureReal_mono (fun ω every => ⟨(every (stop ω) (hs ω)).1.le,(every (stop ω) (hs ω)).2⟩) (measure_ne_top _ _)

theorem stationary_fit (N m : ℕ) (η : ℝ) (u : Net ℂ m)
    (fit : ∀ i, output (1/sqrt m) u (gridPoint N i) = 1+(gridPoint N i).re) (t : ℕ) :
    train N m η u t=u := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [train,ih]
    cases u
    simp only [step,fit,sub_self,zero_mul,zero_smul,Finset.sum_const_zero,mul_zero,smul_zero,sub_zero]

theorem fixed_cap_support (N m H : ℕ) (hn : 3≤N) (odd : Odd N) (width : N+5≤m)
    (η tol : ℝ) (htol : 0<tol) :
    let u := fun ω => train N m η (initial ω) H
    let E := {ω | gridRms N m (u ω)≤tol}
    let Y := fun ω => populationMean (1/sqrt m) (u ω)
    ((cond (seedLaw m) E).map Y).support=univ :=
  conditional_support N m H hn odd width η tol htol (fun _ => H) measurable_const (fun _ => le_rfl)

theorem first_hit_support (N m H : ℕ) (hn : 3≤N) (odd : Odd N) (width : N+5≤m)
    (η tol : ℝ) (htol : 0<tol) :
    let r := fun t (ω : Seed m) => gridRms N m (train N m η (initial ω) t)
    let stop := fun ω => firstHit H (fun t => r t ω≤tol)
    let E := {ω | r (stop ω) ω≤tol}
    let Y := fun ω => populationMean (1/sqrt m) (train N m η (initial ω) (stop ω))
    ((cond (seedLaw m) E).map Y).support=univ := by
  intro r stop E Y
  have rms (t : ℕ) : Measurable (r t) := (random_rate_statistics N m (fun _ => η) measurable_const t).1
  have meas : Measurable stop := firstHit_measurable H (fun ω t => r t ω≤tol) (fun t => measurableSet_le (rms t) measurable_const)
  exact conditional_support N m H hn odd width η tol htol stop meas (fun ω => (firstHit_spec (H:=H) (hit:=fun t => r t ω≤tol)).1)

end CircleFitSupport
