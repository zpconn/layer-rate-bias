module

public import CircleEulerLimits
import all CircleEulerLimits
import all CircleFlowTracking
public import CircleDiscreteMoments
import all CircleDiscreteMoments
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleFlowPath
public import Channel
public import CircleCapMoments
import all CircleGridEscape
import all CircleGridMargin
import all CircleCapMoments
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleEscape
import all CircleInitializationCheck
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Conditioning and first-hit observations for training algorithms on one seed space. -/

public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory Topology
namespace CircleConditioning
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Conditioning the Gaussian seed (or any probability law) changes it in
probability total variation by precisely the rejected mass. -/
theorem seed_tv (μ : Measure X) [IsProbabilityMeasure μ] {E : Set X}
    (hE : MeasurableSet E) (hp : μ E ≠ 0) :
    tvDist μ (ProbabilityTheory.cond μ E) / 2 = μ.real Eᶜ := by
  let := cond_isProbabilityMeasure hp
  have lower := TrainingLaws.event_gap_le μ (cond μ E) hE
  have hone : (cond μ E).real E = 1 := by simp [Measure.real, cond_apply_self hp]
  have hu := measureReal_mono (μ := μ) (subset_univ E)
  rw [probReal_univ] at hu
  have hρ : μ.restrict E ≤ cond μ E := by
    intro s
    change _ ≤ (μ E)⁻¹ * μ.restrict E s
    exact le_mul_of_one_le_left' (by simpa using (prob_le_one (μ := μ) (s := E)) : 1 ≤ (μ E)⁻¹)
  have upper := tvDist_triangle μ (μ.restrict E) (cond μ E)
  rw [tvDist_of_ge Measure.restrict_le_self, tvDist_of_le hρ] at upper
  simp only [probReal_univ, measureReal_restrict_apply_univ] at upper
  rw [hone, abs_of_nonpos (sub_nonpos.mpr hu)] at lower
  rw [measureReal_compl hE, probReal_univ]
  linarith

theorem conditional_output_tv (μ : Measure X) [IsProbabilityMeasure μ]
    {E : Set X} (hE : MeasurableSet E) (hp : μ E ≠ 0)
    (f : X → Y) (hf : Measurable f) :
    tvDist (μ.map f) ((cond μ E).map f) / 2 ≤ μ.real Eᶜ := by
  let := cond_isProbabilityMeasure hp
  rw [← seed_tv μ hE hp]
  exact div_le_div_of_nonneg_right (TrainingLaws.tvDist_map f hf _ _) (by norm_num)

/-- Two algorithms agreeing on the same accepted seeds differ in output TV by at
most the probability of rejection, regardless of their outputs on that event. -/
theorem coupled_output_tv (μ : Measure X) [IsProbabilityMeasure μ]
    {E : Set X} (hE : MeasurableSet E) {f g : X → Y}
    (hf : Measurable f) (hg : Measurable g) (agree : EqOn f g E) :
    tvDist (μ.map f) (μ.map g) / 2 ≤ μ.real Eᶜ := by
  have equal : (μ.restrict E).map f = (μ.restrict E).map g :=
    Measure.map_congr ((ae_restrict_iff' hE).mpr (Eventually.of_forall agree))
  have hf' := Measure.map_mono (μ := μ.restrict E) (ν := μ) Measure.restrict_le_self hf
  have hg' := Measure.map_mono (μ := μ.restrict E) (ν := μ) Measure.restrict_le_self hg
  rw [← equal] at hg'
  have tv := tvDist_triangle (μ.map f) ((μ.restrict E).map f) (μ.map g)
  rw [tvDist_of_ge hf', tvDist_of_le hg'] at tv
  simp only [Measure.real, Measure.map_apply hf MeasurableSet.univ, Measure.map_apply hg
    MeasurableSet.univ, preimage_univ, measure_univ, ENNReal.toReal_one,
    Measure.restrict_apply_univ] at tv
  rw [measureReal_compl hE, probReal_univ]
  exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by simp only [Measure.real]; linarith)

/-- The first iterate meeting tolerance up to a deterministic cap H. On failure
the returned index is H, and fit at that index still distinguishes success. -/
def firstHit (H : ℕ) (hit : ℕ → Prop) [DecidablePred hit] : ℕ :=
  if ex : ∃ t ≤ H, hit t then Nat.find ex else H

theorem firstHit_spec {H : ℕ} {hit : ℕ → Prop} [DecidablePred hit] :
    firstHit H hit ≤ H ∧ (hit (firstHit H hit) ↔ ∃ t ≤ H, hit t) ∧
    ∀ t < firstHit H hit, ¬hit t := by
  unfold firstHit
  split_ifs with ex
  · obtain ⟨hcap, hhit⟩ := Nat.find_spec ex
    exact ⟨hcap, ⟨fun _ => ex, fun _ => hhit⟩, fun t ht h => Nat.find_min ex ht ⟨ht.le.trans hcap, h⟩⟩
  · exact ⟨le_rfl, ⟨fun h => ⟨H, le_rfl, h⟩, fun h => (ex h).elim⟩,
      fun t ht h => ex ⟨t, ht.le, h⟩⟩

/-- The exact criterion at a successful endpoint. Each N can have its own
seed space, event, and observation. The known contribution is the unnormalized
accepted-and-fitted MSE. The remaining term is the rejected-and-fitted MSE. -/
theorem conditional_mse_iff {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (E F : (n : ℕ) → Set (Ω n)) (D : (n : ℕ) → Ω n → ℝ)
    (hE : ∀ n, MeasurableSet (E n)) (hF : ∀ n, MeasurableSet (F n))
    (hD : ∀ n, Integrable (fun ω => D n ω ^ 2) (μ n))
    (fit : Tendsto (fun n => (μ n).real (F n)) atTop (𝓝 1))
    (accepted : Tendsto
      (fun n : ℕ => (n:ℝ)^4 * ∫ ω in F n ∩ E n, D n ω ^ 2 ∂μ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)^4 * ∫ ω, D n ω ^ 2 ∂cond (μ n) (F n)) atTop (𝓝 0) ↔
    Tendsto (fun n : ℕ => (n:ℝ)^4 * ∫ ω in F n \ E n, D n ω ^ 2 ∂μ n) atTop (𝓝 0) := by
  let A (n : ℕ) := (n:ℝ)^4 * ∫ ω in F n ∩ E n, D n ω ^ 2 ∂μ n
  let R (n : ℕ) := (n:ℝ)^4 * ∫ ω in F n \ E n, D n ω ^ 2 ∂μ n
  let p (n : ℕ) := (μ n).real (F n)
  have ha : Tendsto A atTop (𝓝 0) := accepted
  have hp : Tendsto p atTop (𝓝 1) := fit
  have eqn (n : ℕ) : (n:ℝ)^4 * (∫ ω, D n ω ^ 2 ∂cond (μ n) (F n)) = (A n + R n)/p n := by
    have un : (F n ∩ E n) ∪ (F n \ E n) = F n := by ext; simp
    have d : Disjoint (F n ∩ E n) (F n \ E n) := disjoint_left.mpr fun _ h h' => h'.2 h.2
    have split := setIntegral_union d ((hF n).diff (hE n))
      ((hD n).integrableOn (s := F n ∩ E n)) ((hD n).integrableOn (s := F n \ E n))
    rw [un] at split
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, split]
    dsimp [A,R,p,Measure.real]
    ring
  simp_rw [eqn]
  change Tendsto (fun n => (A n+R n)/p n) atTop (𝓝 0) ↔ Tendsto R atTop (𝓝 0)
  constructor
  · intro h
    have hpos : ∀ᶠ n in atTop, p n ≠ 0 := hp.eventually_ne (by norm_num)
    have lim := (h.mul hp).sub ha
    simp only [zero_mul,sub_zero] at lim
    apply lim.congr'
    filter_upwards [hpos] with n hn
    field_simp
    ring
  · intro h
    have u := (ha.add h).div hp (by norm_num : (1:ℝ) ≠ 0)
    simp only [zero_add,zero_div] at u
    exact u.congr (fun _ => rfl)

open CircleEscape CircleEscapeBridge CircleCapMoments CircleInitializationCheck CircleCapInduction

/-- At any common update count, the laws of the two observables have TV
at most the rejection probability, even if their moments are very different. -/
theorem capped_output_tv (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m) :
    tvDist ((seedLaw m).map (trainedMean (CircleSeedIntegrability.path N m 1) t))
      ((seedLaw m).map (cappedY N m t)) / 2 ≤ Real.exp (-(m:ℝ)/240) := by
  have hf : Measurable (trainedMean (CircleSeedIntegrability.path N m 1) t) := by
    unfold trainedMean populationMean
    apply measurable_const.mul
    exact Finset.measurable_fun_sum _ fun j _ =>
      ((CircleSeedIntegrability.parameter_measurable N m 1 t j).1).mul
      (CircleSeedIntegrability.parameter_measurable N m 1 t j).2.norm
  have eqs : EqOn (trainedMean (CircleSeedIntegrability.path N m 1) t) (cappedY N m t)
      (screen N m) := by
    intro ω pass
    simp only [trainedMean, CircleSeedIntegrability.path, cappedY, rate,
      trajectory_on_check N m _ pass (initial ω)]
  apply (coupled_output_tv (seedLaw m) (screen_measurable N m (by omega) odd hm) hf
    (cappedY_measurable N m t (by omega) odd hm) eqs).trans
  simpa [screen,compl_ofPred] using reject_probability N m hN odd hm

/-- A bounded first-hit index is a measurable function of the seed when
the per-step tests are Borel. Treating the cap as an automatic hit only in
the auxiliary minimization handles misses and actual hits at the last step. -/
theorem firstHit_measurable (H : ℕ) (hit : X → ℕ → Prop) [∀ ω, DecidablePred (hit ω)]
    (meas : ∀ t, MeasurableSet {ω | hit ω t}) :
    Measurable (fun ω => firstHit H (hit ω)) := by
  classical
  let p := fun (ω : X) (t : ℕ) => t = H ∨ hit ω t
  have ex (ω : X) : ∃ t, p ω t := ⟨H, Or.inl rfl⟩
  have h : Measurable (fun ω => Nat.find (ex ω)) := measurable_find ex (by
    intro t
    by_cases eq : t = H <;> simp [p,eq,meas])
  suffices eq : (fun ω => Nat.find (ex ω)) = (fun ω => firstHit H (hit ω)) by rwa [← eq]
  funext ω
  obtain ⟨bound,succ,prev⟩ := @firstHit_spec H (hit ω) _
  have spec := Nat.find_spec (ex ω)
  have cap := Nat.find_min' (ex ω) (Or.inl rfl : p ω H)
  apply le_antisymm
  · apply Nat.find_min'
    by_cases hh : firstHit H (hit ω) = H
    · exact Or.inl hh
    · apply Or.inr
      apply succ.mpr
      by_contra hn
      have eq := show firstHit H (hit ω) = H by simp [firstHit,hn]
      contradiction
  · by_contra! lt
    rcases spec with eq|yes
    · omega
    · exact prev _ lt yes

/-- The physical residual used for stopping the discrete circle learner. -/
noncomputable def gridRms (N m : ℕ) (u : Net ℂ m) : ℝ :=
  Real.sqrt ((∑ i, (output (1/Real.sqrt m) u (gridPoint N i) - (1+(gridPoint N i).re))^2)/N)

/-- The returned index, monitored residual, and observation all refer to the
same update. The convention therefore distinguishes a last-step hit from a
miss by its reported residual even though both return index H. -/
noncomputable def stoppedTriple (H : ℕ) (tol : ℝ) (r y : ℕ → X → ℝ) (ω : X) : ℕ × ℝ × ℝ :=
  let t := firstHit H (fun s => r s ω ≤ tol)
  (t,r t ω,y t ω)

theorem stoppedTriple_measurable (H : ℕ) (tol : ℝ) (r y : ℕ → X → ℝ)
    (hr : ∀ s, Measurable (r s)) (hy : ∀ s, Measurable (y s)) :
    Measurable (stoppedTriple H tol r y) := by
  let t := fun ω => firstHit H (fun s => r s ω ≤ tol)
  have time : Measurable t := firstHit_measurable H (fun ω s => r s ω ≤ tol)
    (fun s => measurableSet_le (hr s) measurable_const)
  have f : Measurable (fun p : X × ℕ => (r p.2 p.1,y p.2 p.1)) :=
    measurable_from_prod_countable_left (fun s => (hr s).prodMk (hy s))
  exact time.prodMk (f.comp (measurable_id.prodMk time))

/-- Jointly record count, grid RMS and whole-circle mean under ordinary or
capped GD. -/
noncomputable def stoppedObservation (N m H : ℕ) (tol : ℝ) (η : Seed m → ℝ) :=
  stoppedTriple H tol (fun s ω => gridRms N m (train N m (η ω) (initial ω) s))
    (fun s ω => populationMean (1/Real.sqrt m) (train N m (η ω) (initial ω) s))

private theorem random_rate_parameters (N m : ℕ) (η : Seed m → ℝ) (hη : Measurable η) (t : ℕ) :
    ∀ j, Measurable (fun ω => (train N m (η ω) (initial ω) t).a j) ∧
      Measurable (fun ω => (train N m (η ω) (initial ω) t).w j) := by
  let u := fun t (ω : Seed m) => train N m (η ω) (initial ω) t
  change ∀ j, Measurable (fun ω => (u t ω).a j) ∧ Measurable (fun ω => (u t ω).w j)
  induction t with
    | zero => exact CircleSeedIntegrability.parameter_measurable N m 1 0
    | succ s ih =>
      let r := fun ω (i : Fin N) => output (1/Real.sqrt m) (u s ω) (gridPoint N i)-(1+(gridPoint N i).re)
      have res i : Measurable (fun ω => r ω i) := (CircleSeedIntegrability.output_meas (u s)
        (fun j => (ih j).1) (fun j => (ih j).2) _ _).sub measurable_const
      intro j
      constructor
      · apply (ih j).1.sub
        apply (hη.div measurable_const).mul
        exact Finset.measurable_fun_sum _ fun i _ => (res i).mul
          (CircleSeedIntegrability.feature_meas (ih j).2 _)
      · apply (ih j).2.sub
        apply ((hη.div measurable_const).mul (ih j).1).smul
        exact Finset.measurable_fun_sum _ fun i _ => ((res i).mul
          (CircleSeedIntegrability.gate_meas (ih j).2 _)).smul measurable_const

private theorem random_rate_statistics (N m : ℕ) (η : Seed m → ℝ) (hη : Measurable η) (t : ℕ) :
    Measurable (fun ω => gridRms N m (train N m (η ω) (initial ω) t)) ∧
      Measurable (fun ω => populationMean (1/Real.sqrt m) (train N m (η ω) (initial ω) t)) := by
  let u := fun s (ω : Seed m) => train N m (η ω) (initial ω) s
  have coord := random_rate_parameters N m η hη
  have rms t : Measurable (fun ω => gridRms N m (u t ω)) := by
    apply Real.continuous_sqrt.measurable.comp
    apply Measurable.div_const
    exact Finset.measurable_fun_sum _ (fun i _ =>
      ((CircleSeedIntegrability.output_meas (u t) (fun j => (coord t j).1)
        (fun j => (coord t j).2) _ (gridPoint N i)).sub measurable_const).pow_const 2)
  have mean t : Measurable (fun ω => populationMean (1/Real.sqrt m) (u t ω)) := by
    apply measurable_const.mul
    exact Finset.measurable_fun_sum _ (fun j _ => (coord t j).1.mul (coord t j).2.norm)
  exact ⟨rms t,mean t⟩

theorem stoppedObservation_measurable (N m H : ℕ) (tol : ℝ) (η : Seed m → ℝ)
    (hη : Measurable η) : Measurable (stoppedObservation N m H tol η) := by
  exact stoppedTriple_measurable H tol _ _ (fun s => (random_rate_statistics N m η hη s).1)
    (fun s => (random_rate_statistics N m η hη s).2)

theorem stopped_agreement (N m H : ℕ) (tol : ℝ) :
    EqOn (stoppedObservation N m H tol (fun _ => 1))
      (stoppedObservation N m H tol (rate N m)) (screen N m) := by
  intro ω pass
  simp only [stoppedObservation,stoppedTriple, rate, trajectory_on_check N m _ pass (initial ω)]

/-- The stopped joint law (count, residual and mean) changes in probability
total variation by at most the rejection probability. This applies to every
tolerance and every finite cap, without any moment hypothesis. -/
theorem firstHit_output_tv (N m H : ℕ) (tol : ℝ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m) :
    tvDist ((seedLaw m).map (stoppedObservation N m H tol (fun _ => 1)))
      ((seedLaw m).map (stoppedObservation N m H tol (rate N m))) / 2 ≤ Real.exp (-(m:ℝ)/240) := by
  have rr : Measurable (rate N m) := measurable_const.div
    (measurable_const.max (curvature_measurable N m (by omega) odd hm))
  apply (coupled_output_tv (seedLaw m) (screen_measurable N m (by omega) odd hm)
    (stoppedObservation_measurable N m H tol _ measurable_const)
    (stoppedObservation_measurable N m H tol _ rr) (stopped_agreement N m H tol)).trans
  simpa [screen,compl_ofPred] using reject_probability N m hN odd hm

/-- One grid error of magnitude at least one already rules out the physical
N⁻³ RMS tolerance for every N ≥ 3. -/
theorem one_sample_miss (N m : ℕ) (hN : 3 ≤ N) (u : Net ℂ m) (i : Fin N)
    (bad : 1 ≤ |output (1/Real.sqrt m) u (gridPoint N i)-(1+(gridPoint N i).re)|) :
    1/(N:ℝ)^3 < gridRms N m u := by
  let r := fun j => output (1/Real.sqrt m) u (gridPoint N j)-(1+(gridPoint N j).re)
  have n : 1 < (N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have rr : 1 ≤ (r i)^2 := by nlinarith only [pow_le_pow_left₀ zero_le_one bad 2,sq_abs (r i)]
  have sq : 1 ≤ ∑ j, (r j)^2 := rr.trans (Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_univ i))
  change 1/(N:ℝ)^3 < Real.sqrt ((∑ j, (r j)^2)/N)
  apply (Real.lt_sqrt (by positivity)).mpr
  have lt : 1 < (N:ℝ)^5 := one_lt_pow₀ n (by decide)
  have cmp : (1/(N:ℝ)^3)^2 < 1/(N:ℝ) := by
    rw [div_pow,one_pow,← pow_mul,show 3*2=5+1 by decide,pow_succ]
    exact one_div_lt_one_div_of_lt (by linarith) (by nlinarith only [mul_lt_mul_of_pos_right lt (lt_trans zero_lt_one n)])
  exact cmp.trans_le (div_le_div_of_nonneg_right sq (by linarith))

/-- Both of the actual signed escape boxes miss the RMS tolerance at every
ordinary GD update, including time zero. In particular they contribute no
seeds to any finite first-hit or fixed-cap success event. -/
theorem signed_boxes_never_hit (N m : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (η L : ℝ)
    (hη : 0 < η) (hcap : η ≤ 1) (hL : 0 < L) (hscale : L^2 = 64*m/η)
    (negative : Bool) (ω : Seed m) (boxω : ω ∈ box m L negative) (t : ℕ) :
    1/(N:ℝ)^3 < gridRms N m (train N m η (initial ω) t) := by
  let σ : ℝ := if negative then -1 else 1
  let u := train N m η (initial ω)
  have sign : |σ| = 1 := by cases negative <;> norm_num [σ]
  have st : Cone (u 0) σ (2*L) := by
    intro j
    cases negative
    · exact ⟨by simpa [σ,u,train,initial] using (boxω (j,0) (mem_univ _)).1,
        ((boxω (j,1) (mem_univ _)).1 : 2*L ≤ ((initial ω).w j).re).trans (Complex.re_le_norm ((initial ω).w j))⟩
    · exact ⟨by simpa [σ,u,train,initial] using (boxω (j,0) (mem_univ _)).1,
        ((boxω (j,1) (mem_univ _)).1 : 2*L ≤ ((initial ω).w j).re).trans (Complex.re_le_norm ((initial ω).w j))⟩
  have np : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have mp : (0:ℝ) < m := by exact_mod_cast (show 0<m by omega)
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
    have h := Complex.abs_re_le_norm (gridPoint N i)
    rw [grid_norm] at h
    apply (abs_add_le _ _).trans
    rw [abs_one]
    linarith
  have cone := CircleGridEscape.iterate_cone (gridPoint N) _ _ _ _ (one_div_pos.mpr ms)
    (by positivity) hL (fun i => (grid_norm N i).le)
    (fun w => (CircleGridMargin.grid_relu_sum_bounds N hN w).2) lab scale noise u (fun _ => rfl) σ sign st t
  let j : Fin m := ⟨0,by omega⟩
  let s := (-1:ℝ)^t*σ
  obtain ⟨i,fi⟩ := grid_coverage N hN ((u t).w j)
  have low := CircleEscape.floor_large L hL.le t
  have a (k : Fin m) : 2*L ≤ s*(u t).a k := low.trans (cone k).1
  have w := low.trans (cone j).2
  have hi : L ≤ feature ((u t).w j) (gridPoint N i) := by linarith
  have ss : |s|=1 := by simp [s,abs_mul,abs_pow,sign]
  have fj (k : Fin m) : 0 ≤ feature ((u t).w k) (gridPoint N i) := le_max_right _ _
  have term := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun k => (s*(u t).a k)*feature ((u t).w k) (gridPoint N i))
    (fun k _ => mul_nonneg (by linarith [a k]) (fj k)) (Finset.mem_univ j)
  have out : (1/Real.sqrt m)*((2*L)*L) ≤ s*output (1/Real.sqrt m) (u t) (gridPoint N i) := by
    apply (mul_le_mul_of_nonneg_left ((mul_le_mul (a j) hi hL.le (by linarith [a j])).trans term) (by positivity)).trans_eq
    simp only [output,mul_assoc,← Finset.mul_sum]
    ring
  have ao : 32 ≤ |output (1/Real.sqrt m) (u t) (gridPoint N i)| := by
    have h := out.trans (le_abs_self _)
    rw [abs_mul,ss,one_mul] at h
    nlinarith only [noise,h]
  apply one_sample_miss N m hN (u t) i
  have r := abs_sub_abs_le_abs_sub (output (1/Real.sqrt m) (u t) (gridPoint N i)) (1+(gridPoint N i).re)
  linarith [lab i]

private theorem seed_neighborhood_pos {m : ℕ} {ω : Seed m} {S : Set (Seed m)}
    (h : S ∈ 𝓝 ω) : 0 < (seedLaw m).real S := by
  let : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    ⟨fun U ho ne he => ho.measure_ne_zero volume ne ((gaussianReal_absolutelyContinuous' 0 (by norm_num)) he)⟩
  let : Measure.IsOpenPosMeasure (seedLaw m) := by unfold seedLaw; infer_instance
  exact ENNReal.toReal_pos ((seedLaw m).measure_pos_of_mem_nhds h).ne' (measure_ne_top _ _)

private noncomputable def label (N : ℕ) (i : Fin N) : ℝ := 1+(gridPoint N i).re

private theorem output_tendsto {m : ℕ} {u : Seed m → Net ℂ m} {v : Net ℂ m} {ω : Seed m}
    (h : ∀ j, Tendsto (fun ξ => (u ξ).a j) (𝓝 ω) (𝓝 (v.a j)) ∧
      Tendsto (fun ξ => (u ξ).w j) (𝓝 ω) (𝓝 (v.w j)))
    (x : ℂ) : Tendsto (fun ξ => output (1/Real.sqrt m) (u ξ) x) (𝓝 ω) (𝓝 (output (1/Real.sqrt m) v x)) := by
  apply tendsto_const_nhds.mul
  exact tendsto_finsetSum _ (fun j _ => (h j).1.mul (((h j).2.inner tendsto_const_nhds).max tendsto_const_nhds))

/-- At exact interpolants and at the all-zero seed the ordinary finite
iterations are continuous even if a grid gate changes at the seed. The
possibly discontinuous gate is multiplied by a factor tending to zero. -/
private theorem stationary_stability (N m : ℕ) (ω : Seed m)
    (hx : ∀ i j,
      (output (1/Real.sqrt m) (initial ω) (gridPoint N i)-label N i)*feature ((initial ω).w j) (gridPoint N i) = 0 ∧
      (initial ω).a j*(output (1/Real.sqrt m) (initial ω) (gridPoint N i)-label N i) = 0)
    (t : ℕ) : ∀ j,
      Tendsto (fun ξ => (train N m 1 (initial ξ) t).a j) (𝓝 ω) (𝓝 ((initial ω).a j)) ∧
      Tendsto (fun ξ => (train N m 1 (initial ξ) t).w j) (𝓝 ω) (𝓝 ((initial ω).w j)) := by
  induction t with
  | zero =>
    intro j
    refine ⟨(continuous_apply (j,0)).tendsto _,?_⟩
    have h : Continuous (fun ξ : Seed m => (ξ (j,1),ξ (j,2))) :=
      (continuous_apply _).prodMk (continuous_apply _)
    exact (Complex.equivRealProdCLM.symm.continuous.comp h).tendsto ω
  | succ t ih =>
    let u := fun ξ => train N m 1 (initial ξ) t
    let x := gridPoint N
    let k : ℝ := 1/(N*Real.sqrt m)
    let r := fun i ξ => output (1/Real.sqrt m) (u ξ) (x i)-label N i
    let r₀ := fun i => output (1/Real.sqrt m) (initial ω) (x i)-label N i
    have hr i : Tendsto (r i) (𝓝 ω) (𝓝 (r₀ i)) := (output_tendsto ih (x i)).sub tendsto_const_nhds
    intro j
    have ar (i : Fin N) : Tendsto (fun ξ => r i ξ*feature ((u ξ).w j) (x i)) (𝓝 ω) (𝓝 0) := by
      have f : Tendsto (fun ξ => feature ((u ξ).w j) (x i)) (𝓝 ω) (𝓝 (feature ((initial ω).w j) (x i))) :=
        ((ih j).2.inner (tendsto_const_nhds (x:= x i))).max (tendsto_const_nhds (x:= (0:ℝ)))
      have a := (hr i).mul f
      rwa [show r₀ i*feature ((initial ω).w j) (x i)=0 from (hx i j).1] at a
    have wr (i : Fin N) : Tendsto (fun ξ => (u ξ).a j*r i ξ*gate ((u ξ).w j) (x i)) (𝓝 ω) (𝓝 0) := by
      have first := (ih j).1.mul (hr i)
      change Tendsto _ _ (𝓝 ((initial ω).a j*(output (1/Real.sqrt m) (initial ω) (gridPoint N i)-label N i))) at first
      rw [(hx i j).2] at first
      apply first.zero_mul_isBoundedUnder_le
      apply isBoundedUnder_of_eventually_le (a:=1)
      exact Eventually.of_forall (fun ξ => by change ‖gate ((u ξ).w j) (x i)‖ ≤ 1; unfold gate; split <;> norm_num)
    have da := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => ar i)
    have dw := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => (wr i).smul (tendsto_const_nhds (x:=x i)))
    simp only [Finset.sum_const_zero,zero_smul] at da dw
    constructor
    · change Tendsto (fun ξ => (u ξ).a j-k*∑ i, r i ξ*feature ((u ξ).w j) (x i)) _ _
      simpa only [mul_zero,sub_zero] using (ih j).1.sub ((tendsto_const_nhds (x:=k)).mul da)
    · have res := (ih j).2.sub ((tendsto_const_nhds (x:=k)).smul dw)
      change Tendsto (fun ξ => (u ξ).w j-(k*(u ξ).a j) • ∑ i, (r i ξ * gate ((u ξ).w j) (x i)) • x i) _ _
      simpa only [Finset.smul_sum,smul_smul,mul_assoc,smul_zero,sub_zero] using res

/-- There is positive standard-Gaussian probability of passing the initial
screen and missing every training fit through any given finite cap. -/
theorem accepted_misses_pos (N m H : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m) :
    0 < (seedLaw m).real {ω | ω ∈ screen N m ∧ ∀ t ≤ H,
      1/(N:ℝ)^3 < gridRms N m (train N m 1 (initial ω) t)} := by
  let o : Seed m := 0
  have hx (i : Fin N) (j : Fin m) :
      (output (1/Real.sqrt m) (initial o) (gridPoint N i)-label N i)*feature ((initial o).w j) (gridPoint N i) = 0 ∧
      (initial o).a j*(output (1/Real.sqrt m) (initial o) (gridPoint N i)-label N i) = 0 := by
    simp [o,initial,feature]
  have en (ξ : Seed m) : energy (initial ξ) = (∑ i, (ξ i)^2)/m := by
    rw [energy,initial_energy_coordinates]
  have energyNear : Tendsto (fun ξ : Seed m => C N * energy (initial ξ)) (𝓝 o) (𝓝 0) := by
    simp_rw [en]
    have h : Continuous (fun ξ : Seed m => C N*((∑ i, (ξ i)^2)/m)) := by fun_prop
    simpa only [o,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero,zero_div,mul_zero] using h.tendsto o
  have pass : ∀ᶠ ξ in 𝓝 o, ξ ∈ screen N m :=
    (energyNear.eventually_lt tendsto_const_nhds zero_lt_one).mono (fun ξ h =>
      ((CircleCapMoments.initial_top N m hN odd hm (initial ξ)).2.trans h.le))
  let i : Fin N := ⟨0,by omega⟩
  have miss (t : ℕ) : ∀ᶠ ξ in 𝓝 o, 1/(N:ℝ)^3 < gridRms N m (train N m 1 (initial ξ) t) := by
    have small := output_tendsto (stationary_stability N m o hx t) (gridPoint N i)
    have z : output (1/Real.sqrt m) (initial o) (gridPoint N i) = 0 := by simp [o,initial,output]
    rw [z] at small
    filter_upwards [small.eventually_lt tendsto_const_nhds zero_lt_one] with ξ hξ
    apply one_sample_miss N m hN _ i
    have x : (gridPoint N i).re = 1 := by simp [i,gridPoint]
    rw [x,abs_of_nonpos (by linarith)]
    linarith
  apply seed_neighborhood_pos (ω:=o)
  filter_upwards [pass,(Finset.range (H+1)).eventually_all.mpr (fun t _ => miss t)] with ξ p q
  exact ⟨p,fun t ht => q t (Finset.mem_range.mpr (by omega))⟩

/-- The constant-vector Rayleigh test restricted to one readout column
certifies rejection from the size of a single hidden vector. This holds at
every parameter value, including configurations with zero hidden vectors. -/
theorem single_hidden_lower (N m : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m)
    (u : Net ℂ m) (j : Fin m) :
    ‖u.w j‖^2 ≤ 16*m*curvature (gridPoint N) u := by
  let L := curvature (gridPoint N) u
  have np : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have up := ((CircleCapMoments.initial_top N m hN odd hm u).1).1 (fun _ => 1)
  have one := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun l : Fin m => (∑ i, feature (u.w l) (gridPoint N i))^2+
      (u.a l)^2*‖∑ i, gate (u.w l) (gridPoint N i) • gridPoint N i‖^2)
    (fun l _ => by positivity) (Finset.mem_univ j)
  simp only [jacSq,one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at up
  have quad := (CircleGridMargin.grid_relu_sum_bounds N hN (u.w j)).1
  have lower := pow_le_pow_left₀ (by positivity) quad 2
  have extra : 0 ≤ (u.a j)^2*‖∑ i, gate (u.w j) (gridPoint N i) • gridPoint N i‖^2 := by positivity
  apply le_of_mul_le_mul_left (a:=(N:ℝ)^2)
  · nlinarith only [lower,one.trans up,extra]
  · positivity

private theorem aligned_sum (N : ℕ) (hN : 0<N) :
    ∃ A : ℝ, 0 < A ∧ ∀ i : Fin N, ∑ j : Fin N, feature (gridPoint N j) (gridPoint N i) = A := by
  let : NeZero N := ⟨hN.ne'⟩
  let d := 2*Real.pi/(N:ℝ)
  let h := fun j : Fin N => max (Real.cos (d*(j:ℕ))) 0
  have point (i j : Fin N) : feature (gridPoint N j) (gridPoint N i) = h (j-i) := by
    have realSub : ((j-i:Fin N).val:ℝ)=(j.val:ℝ)-i.val+((if i≤j then 0 else N : ℕ):ℝ) := by
      exact_mod_cast Fin.intCast_val_sub_eq_sub_add_ite j i
    have innerEq : inner ℝ (gridPoint N j) (gridPoint N i) = Real.cos (d*(j.val:ℝ)-d*i.val) := by
      rw [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,Real.cos_sub]
      dsimp [gridPoint,d]
      ring
    unfold feature h
    rw [innerEq,realSub]
    by_cases ij : i≤j
    · simp only [ite_eq_left ij,Nat.cast_zero,add_zero,mul_sub]
    · simp only [ite_eq_right ij,mul_add,mul_sub]
      rw [show d*(N:ℝ)=2*Real.pi by dsimp [d]; field_simp,Real.cos_add_two_pi]
  refine ⟨∑ j, h j,?_,?_⟩
  · have a := Finset.single_le_sum (s:=Finset.univ) (f:=h) (fun _ _ => le_max_right _ _) (Finset.mem_univ (0:Fin N))
    have one : h (0:Fin N)=1 := by simp [h]
    linarith
  · intro i
    simp_rw [point i]
    exact (Equiv.subRight i).sum_comp h

private noncomputable def encode {m : ℕ} (u : Net ℂ m) : Seed m :=
  fun p => ![u.a p.1, (u.w p.1).re, (u.w p.1).im] p.2

private theorem initial_encode {m : ℕ} (u : Net ℂ m) : initial (encode u) = u := by
  cases u
  rfl

/-- Exact interpolation is possible on every finite grid, with a designated
unused readout and arbitrarily large associated hidden vector. -/
private theorem high_curvature_interpolant (N m : ℕ) (hN : 0 < N) (width : N+3 ≤ m) :
    ∃ ω : Seed m, (∀ i : Fin N, output (1/Real.sqrt m) (initial ω) (gridPoint N i) = label N i) ∧
      ∃ j : Fin m, 16*m < ‖(initial ω).w j‖^2 := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le width
  have eq : m=N+(2+(k+1)) := by omega
  clear hk
  subst m
  let m := N+(2+(k+1))
  have mp : (0:ℝ)<m := by exact_mod_cast (show 0<m by dsimp [m]; omega)
  let s := Real.sqrt m
  have sp : 0 < s := Real.sqrt_pos.mpr mp
  have sq : s^2 = m := Real.sq_sqrt mp.le
  obtain ⟨A,ap,allA⟩ := aligned_sum N hN
  let u : Net ℂ m :=
    ⟨Fin.append (fun _ : Fin N => s/A) (Fin.append ![s,-s] (fun _ : Fin (k+1) => 0)),
     Fin.append (gridPoint N) (Fin.append ![(1:ℂ),-1] (fun _ : Fin (k+1) => ((8*s:ℝ):ℂ)))⟩
  refine ⟨encode u,?_,?_⟩
  · intro i
    rw [initial_encode]
    change (1/s)*(∑ j : Fin (N+(2+(k+1))), u.a j*feature (u.w j) (gridPoint N i)) = _
    rw [Fin.sum_univ_add]
    simp only [u,Fin.append_left,Fin.append_right]
    rw [← Finset.mul_sum,allA i,Fin.sum_univ_add]
    simp only [Fin.append_left,Fin.append_right,zero_mul,Finset.sum_const_zero,add_zero,Fin.sum_univ_two]
    let x := gridPoint N i
    have rel : feature (1:ℂ) x-feature (-1:ℂ) x=x.re := by
      simp only [feature,Complex.inner,map_one,map_neg,mul_one,mul_neg,Complex.neg_re]
      by_cases p : 0 ≤ x.re <;> grind
    change (1/s)*(s/A*A+(s*feature 1 x+(-s)*feature (-1) x)) = 1+x.re
    field_simp
    linear_combination rel
  · rw [initial_encode]
    refine ⟨Fin.natAdd N (Fin.natAdd 2 (0:Fin (k+1))),?_⟩
    change 16*(m:ℝ) < ‖u.w (Fin.natAdd N (Fin.natAdd 2 (0:Fin (k+1))))‖^2
    simp only [u,Fin.append_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<8*s)]
    nlinarith only [sq,mp]

/-- Every sufficiently wide finite design gives a positive-probability
set of rejected ordinary-GD runs which fit throughout the finite horizon,
including their initial state and the deterministic cap. -/
theorem rejected_fits_pos (N m H : ℕ) (hN : 3 ≤ N) (odd : Odd N) (width : N+3 ≤ m) (tol : ℝ) (htol : 0 < tol) :
    0 < (seedLaw m).real {ξ | ξ ∉ screen N m ∧ ∀ t ≤ H, gridRms N m (train N m 1 (initial ξ) t) < tol} := by
  have hm : 0 < m := by omega
  obtain ⟨ω,exactFit,j,large⟩ := high_curvature_interpolant N m (by omega) width
  have hx (i : Fin N) (l : Fin m) :
      (output (1/Real.sqrt m) (initial ω) (gridPoint N i)-label N i)*feature ((initial ω).w l) (gridPoint N i) = 0 ∧
      (initial ω).a l*(output (1/Real.sqrt m) (initial ω) (gridPoint N i)-label N i) = 0 := by rw [exactFit i,sub_self,zero_mul,mul_zero]; exact ⟨rfl,rfl⟩
  have hw : Continuous (fun ξ : Seed m => (ξ (j,1),ξ (j,2))) := (continuous_apply _).prodMk (continuous_apply _)
  have wr : Continuous (fun ξ : Seed m => ‖(initial ξ).w j‖^2) :=
    ((Complex.equivRealProdCLM.symm.continuous.comp hw).norm).pow 2
  have rejs : ∀ᶠ ξ in 𝓝 ω, ξ ∉ screen N m :=
    (tendsto_const_nhds.eventually_lt (wr.tendsto ω) large).mono (fun ξ high pass => by
      have b := single_hidden_lower N m hN odd hm (initial ξ) j
      have p : curvature (gridPoint N) (initial ξ) ≤ 1 := pass
      have cap := mul_le_mul_of_nonneg_left p (by positivity : 0 ≤ 16*(m:ℝ))
      linarith)
  have near (t : ℕ) : ∀ᶠ ξ in 𝓝 ω, gridRms N m (train N m 1 (initial ξ) t) < tol := by
    let r := fun i (ξ : Seed m) => output (1/Real.sqrt m) (train N m 1 (initial ξ) t) (gridPoint N i)-label N i
    have h (i : Fin N) : Tendsto (r i) (𝓝 ω) (𝓝 0) := by
      have w := (output_tendsto (stationary_stability N m ω hx t) (gridPoint N i)).sub (tendsto_const_nhds (x:=label N i))
      rwa [exactFit i,sub_self] at w
    have z := tendsto_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => (h i).pow 2)
    simp only [zero_pow (by decide : 2≠0),Finset.sum_const_zero] at z
    have y := Real.continuous_sqrt.continuousAt.tendsto.comp (z.div_const (N:ℝ))
    rw [zero_div,Real.sqrt_zero] at y
    exact y.eventually_lt tendsto_const_nhds htol
  apply seed_neighborhood_pos (ω:=ω)
  filter_upwards [rejs,(Finset.range (H+1)).eventually_all.mpr (fun t _ => near t)] with ξ a b
  exact ⟨a,fun t ht => b t (Finset.mem_range.mpr (by omega))⟩

/-- Exceptional paired MSE at a measurable seed-dependent update, with the
same bound as for fixed counts. The energy envelope is uniform over all
updates through the cap. -/
theorem bounded_stop_exception (N m H : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (hH : 200*H ≤ m) (t : Seed m → ℕ) (mt : Measurable t) (ht : ∀ ω, t ω ≤ H)
    (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) (B : Set (Seed m)) :
    let F := fun ω => cappedY N m (t ω) ω-reference N m b ω
    Integrable (fun ω => (F ω)^2) (seedLaw m) ∧
      (∫ ω in B, (F ω)^2 ∂seedLaw m) ≤ 1044*m*Real.sqrt ((seedLaw m).real B) := by
  intro F
  have Y : Measurable (fun p : Seed m × ℕ => cappedY N m p.2 p.1) :=
    measurable_from_prod_countable_left (fun s => cappedY_measurable N m s (by omega) odd hm)
  have mf : Measurable F := (Y.comp (measurable_id.prodMk mt)).sub (reference_measurable N m b)
  have env : ∀ᵐ ω ∂seedLaw m, |F ω/4| ≤ Real.sqrt m*(energy (initial ω)+1)/2 := by
    filter_upwards [endpoint_envelope N m H hN odd hm hH] with ω h
    have z := reference_envelope N m (by omega) hm b hb hb' ω
    have f := (abs_sub _ _).trans (add_le_add (h (t ω) (ht ω)) z)
    have root : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
    have pe : 0 ≤ energy (initial ω) := div_nonneg (Finset.sum_nonneg fun j _ =>
      add_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg m)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    dsimp [F]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m:ℝ)) pe]
  obtain ⟨inte,bd⟩ := CircleCapMoments.envelope_fourth m hm _ (mf.div_const 4) env
  have rat (ω : Seed m) : (F ω)^4 = 256*(F ω/4)^4 := by ring
  have four : Integrable (fun ω => (F ω)^4) (seedLaw m) := by simp_rw [rat]; exact inte.const_mul _
  have mem : MemLp (fun ω => (F ω)^2) 2 (seedLaw m) :=
    (memLp_two_iff_integrable_sq (mf.pow_const 2).aestronglyMeasurable).2 (by simpa only [←pow_mul] using four)
  refine ⟨mem.integrable one_le_two,(CircleMoment.exceptional_second_moment mem B).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_left (by positivity)).mpr
  simp_rw [rat]
  rw [integral_const_mul]
  rw [gaussian_eighth] at bd
  nlinarith [sq_nonneg (m:ℝ)]

private theorem ordinary_gridRms (N m t : ℕ) (ω : Seed m) :
    gridRms N m (train N m 1 (initial ω) t) =
      ‖CircleActualTracking.gridR N (CircleDiscreteTracking.iterate N ω t)‖ := by
  rw [←CircleDiscreteTracking.iterate_eq_train]
  rw [←Real.sqrt_sq (norm_nonneg _),CircleActualTracking.gridR,CircleTangentDrift.rmsCoordinates_norm_sq]
  unfold gridRms
  simp only [CircleDiscreteTracking.output_complex]
  rfl

/-- At the actual first fit by H (using H if there is no hit), the whole
unrestricted capped law and the unnormalized accepted part of ordinary GD
have paired MSE of order N⁻⁶ relative to the same infinite-time reference.
The learner checks the grid at every iterate, including zero and H. -/
theorem firstHit_paired_mse (n : ℕ) (hN : 12000000 ≤ n+1) (odd : Odd (n+1)) :
    let N := n+1
    let m := N^32
    let H := CircleFlowTracking.horizon (N:ℝ)
    let tol := 1/(N:ℝ)^3
    let b := CircleSpectrum.weight 1 n
    let S := fun (η : Seed m → ℝ) (ω : Seed m) =>
      ((stoppedObservation N m H tol η ω).2.2-reference N m b ω)^2
    let K := (1+2*66*66*385:ℝ)^2+1044*Real.sqrt 13
    (∫ ω, S (rate N m) ω ∂seedLaw m) ≤ K/(N:ℝ)^6 ∧
      (∫ ω in screen N m, S (fun _ => 1) ω ∂seedLaw m) ≤ K/(N:ℝ)^6 := by
  intro N m H tol b S K
  let μ := seedLaw m
  let A := screen N m
  let yc := stoppedObservation N m H tol (rate N m)
  let yf := stoppedObservation N m H tol (fun _ => 1)
  let tc := fun ω => (yc ω).1
  let tf := fun ω => (yf ω).1
  have nn : 0<N := Nat.succ_pos _
  have hm : 0<m := pow_pos nn 32
  have np : (0:ℝ)<N := Nat.cast_pos.mpr nn
  have one : (1:ℝ) ≤ N := by exact_mod_cast nn
  have hlarge : 12000000 ≤ N := hN
  have RR : Measurable (rate N m) := measurable_const.div
    (measurable_const.max (curvature_measurable N m (by omega) odd hm))
  have mt : Measurable tc := (stoppedObservation_measurable N m H tol _ RR).fst
  have ht (ω) : tc ω ≤ H := (@firstHit_spec H (fun s => gridRms N m (train N m (rate N m ω) (initial ω) s) ≤ tol) _).1
  have time : (H:ℝ) ≤ 385*(N:ℝ)^3 := CircleGaussianTracking.horizon_le_cubic one
  have Hcap : 200*H ≤ m := CircleDiscreteMoments.cap_steps hlarge (by exact_mod_cast time)
  have mA : MeasurableSet A := screen_measurable _ _ (by omega) odd hm
  obtain ⟨G,mg,prob,good⟩ := CircleDiscreteMoments.design_event N 158 (by omega) (by omega)
  have fail : μ.real (G∩A)ᶜ ≤ 13/(N:ℝ)^158 := by
    rw [compl_inter]
    exact ((measureReal_union_le _ _).trans (add_le_add prob (CircleDiscreteMoments.reject_pow N hlarge odd))).trans_eq (by ring)
  have wt := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  obtain ⟨int,bad⟩ := bounded_stop_exception N m H (by omega) odd hm Hcap tc mt ht b wt.1 wt.2 (G∩A)ᶜ
  change Integrable (S (rate N m)) μ at int
  change (∫ ω in (G∩A)ᶜ, S (rate N m) ω ∂μ) ≤ _ at bad
  have tail := bad.trans (CircleDiscreteMoments.cap_tail_arithmetic nn fail)
  let B := (1+2*66*66*385:ℝ)/(N:ℝ)^3
  have grid (ω) (s : ℕ) := ordinary_gridRms N m s ω
  have pass (ω : Seed m) (hw : ω∈G∩A) : S (rate N m) ω ≤ B^2 := by
    have same : yf ω = yc ω := stopped_agreement N m H tol hw.2
    have equal : S (rate N m) ω = S (fun _ => 1) ω :=
      congrArg (fun q : ℕ × ℝ × ℝ => (q.2.2-reference N m b ω)^2) same.symm
    rw [equal]
    obtain ⟨g,R,R0⟩ := good ω hw.1
    have tr := CircleDiscreteTracking.design_trajectory (N:=N) (by omega) odd ω g R0
    have hs := @firstHit_spec H (fun s => gridRms N m (train N m 1 (initial ω) s) ≤ tol) _
    have hitH : gridRms N m (train N m 1 (initial ω) H) ≤ tol := by rw [grid]; exact tr.2.1
    have stop := hs.2.1.mpr ⟨H,le_rfl,hitH⟩
    change gridRms N m (train N m 1 (initial ω) (tf ω)) ≤ tol at stop
    rw [grid] at stop
    have time' : (tf ω : ℝ) ≤ 385*(N:ℝ)^3 := (Nat.cast_le.mpr (show tf ω ≤ H from hs.1)).trans time
    have close := CircleDiscreteTracking.terminal_tracking n (by omega) odd ω
      (by simpa [N] using g) (by simpa [N] using R0) (tf ω)
    change |trainedMean (CircleSeedIntegrability.path N m 1) (tf ω) ω-reference N m b ω| ≤
      ‖CircleActualTracking.gridR N (CircleDiscreteTracking.iterate N ω (tf ω))‖+
        2*(66/(N:ℝ)^7)*‖CircleActualTracking.gridR N ω‖*(tf ω) at close
    have bd : |trainedMean (CircleSeedIntegrability.path N m 1) (tf ω) ω-reference N m b ω| ≤ B :=
      close.trans ((add_le_add stop (mul_le_mul (mul_le_mul_of_nonneg_left R (by positivity : 0≤2*(66/(N:ℝ)^7)))
        time' (Nat.cast_nonneg _) (by positivity))).trans_eq (by dsimp [B,tol]; field_simp))
    exact (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) bd 2)
  have small := setIntegral_mono_on int.integrableOn (integrable_const (B^2)).integrableOn (mg.inter mA) pass
  have inside : (∫ ω in G∩A, S (rate N m) ω ∂μ) ≤ B^2 := small.trans (by
    simpa [setIntegral_const,smul_eq_mul] using mul_le_of_le_one_left (sq_nonneg B) (measureReal_le_one (μ:=μ) (s:=G∩A)))
  have main : (∫ ω, S (rate N m) ω ∂μ) ≤ K/(N:ℝ)^6 := by
    rw [← integral_add_compl (mg.inter mA) int]
    exact (add_le_add inside tail).trans_eq (by dsimp [B,K];field_simp)
  refine ⟨main,?_⟩
  have agree : EqOn (S (fun _ => 1)) (S (rate N m)) A := fun ω h =>
    congrArg (fun q : ℕ × ℝ × ℝ => (q.2.2-reference N m b ω)^2) (stopped_agreement N m H tol h)
  rw [setIntegral_congr_fun mA agree]
  exact (setIntegral_le_integral int (ae_of_all _ (fun _ => sq_nonneg _))).trans main

private theorem ordinary_stop_integrable (N m H : ℕ) (tol b : ℝ) :
    Integrable (fun ω => ((stoppedObservation N m H tol (fun _ => 1) ω).2.2-reference N m b ω)^2) (seedLaw m) := by
  let S := fun t ω => (trainedMean (CircleSeedIntegrability.path N m 1) t ω-reference N m b ω)^2
  have h (t : ℕ) : Integrable (S t) (seedLaw m) :=
    ((CircleSeedIntegrability.trained_memLp N m t 1 2 (by norm_num)).sub
      (CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num))).integrable_sq
  have all := integrable_finsetSum (Finset.range (H+1)) (fun t _ => h t)
  have meas := (((stoppedObservation_measurable N m H tol (fun _ => 1) measurable_const).snd.snd.sub
    (reference_measurable N m b)).pow_const 2).aestronglyMeasurable (μ:=seedLaw m)
  apply all.mono' meas (ae_of_all _ ?_)
  intro ω
  let t := firstHit H (fun s => gridRms N m (train N m 1 (initial ω) s) ≤ tol)
  have ht : t ≤ H := (@firstHit_spec H (fun s => gridRms N m (train N m 1 (initial ω) s) ≤ tol) _).1
  change ‖S t ω‖ ≤ ∑ i ∈ Finset.range (H+1), S i ω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (s:=Finset.range (H+1)) (f:=fun i => S i ω) (fun i _ => sq_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))

/-- Finite-design first-hit reduction for the actual ordinary learner.
The calibrated miss probability tends to zero, and multiplying the
conditional MSE by its success probability recovers the rejected-successful
contribution with a one-sided O(N⁻⁶) remainder. -/
theorem firstHit_conditional_reduction (n : ℕ) (hN : 12000000 ≤ n+1) (odd : Odd (n+1)) :
    let N := n+1
    let m := N^32
    let μ := seedLaw m
    let H := CircleFlowTracking.horizon (N:ℝ)
    let tol := 1/(N:ℝ)^3
    let b := CircleSpectrum.weight 1 n
    let v := stoppedObservation N m H tol (fun _ => 1)
    let F := {ω | (v ω).2.1 ≤ tol}
    let D := fun ω => ((v ω).2.2-reference N m b ω)^2
    let K := (1+2*66*66*385:ℝ)^2+1044*Real.sqrt 13
    MeasurableSet F ∧ μ.real Fᶜ ≤ 12/(N:ℝ)^158 ∧
      0 ≤ μ.real F*(∫ ω, D ω ∂cond μ F)-(∫ ω in F \ screen N m, D ω ∂μ) ∧
      μ.real F*(∫ ω, D ω ∂cond μ F)-(∫ ω in F \ screen N m, D ω ∂μ) ≤ K/(N:ℝ)^6 := by
  intro N m μ H tol b v F D K
  have nn : 0<N := Nat.succ_pos _
  have hm : 0<m := pow_pos nn 32
  have nh : 12000000 ≤ N := hN
  have np : (0:ℝ)<N := Nat.cast_pos.mpr nn
  have nr : (12000000:ℝ) ≤ N := by exact_mod_cast nh
  have mF : MeasurableSet F := measurableSet_le
    (stoppedObservation_measurable N m H tol _ measurable_const).snd.fst measurable_const
  have failure : μ.real Fᶜ ≤ 12/(N:ℝ)^158 := by
    have L := CircleDiscreteMoments.gaussian_horizon_fit N 158 (by omega) (by omega) odd
    apply (measureReal_mono (μ:=μ) (s₂:={ω | 1/(N:ℝ)^3 < ‖CircleActualTracking.gridR N (CircleDiscreteTracking.iterate N ω H)‖}) ?_).trans L
    intro ω nope
    change 1/(N:ℝ)^3 < ‖CircleActualTracking.gridR N (CircleDiscreteTracking.iterate N ω H)‖
    by_contra! good
    have ok : gridRms N m (train N m 1 (initial ω) H) ≤ tol := (ordinary_gridRms N m H ω).le.trans good
    exact nope ((@firstHit_spec H (fun s => gridRms N m (train N m 1 (initial ω) s) ≤ tol) _).2.1.mpr ⟨H,le_rfl,ok⟩)
  have less : 12/(N:ℝ)^158 < 1 := by
    rw [div_lt_one (by positivity)]
    exact (by linarith : (12:ℝ)<N).trans_le (by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1:ℝ)≤N) (by decide : 1≤158))
  have positive : 0 < μ.real F := by
    have h := failure.trans_lt less
    rw [measureReal_compl mF,probReal_univ] at h
    linarith
  let E := screen N m
  have mE : MeasurableSet E := screen_measurable _ _ (by omega) odd hm
  have int : Integrable D μ := ordinary_stop_integrable N m H tol b
  have eq : μ.real F*(∫ ω, D ω ∂cond μ F) = ∫ ω in F, D ω ∂μ := by
    rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul]
    change μ.real F*((μ.real F)⁻¹*_) = _
    rw [←mul_assoc,mul_inv_cancel₀ positive.ne',one_mul]
  have un : (F∩E) ∪ (F \ E) = F := by ext; simp
  have dis : Disjoint (F∩E) (F \ E) := Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂.2 h₁.2)
  have split := setIntegral_union (f:=D) dis (mF.diff mE) int.integrableOn int.integrableOn
  rw [un] at split
  have mass := (firstHit_paired_mse n hN odd).2
  refine ⟨mF,failure,?_,?_⟩
  · rw [eq,split,add_sub_cancel_right]
    exact setIntegral_nonneg (mF.inter mE) (fun _ _ => sq_nonneg _)
  · rw [eq,split,add_sub_cancel_right]
    exact (setIntegral_mono_set int.integrableOn (ae_of_all _ (fun _ => sq_nonneg _))
      (Set.inter_subset_right (s:=F) (t:=E)).eventuallySubset).trans mass

/-- Ordinary GD's first-hit mean, including unsuccessful runs returned at
the cap. -/
noncomputable def firstHitMean (N m H : ℕ) (ω : Seed m) : ℝ :=
  (stoppedObservation N m H (1/(N:ℝ)^3) (fun _ => 1) ω).2.2

private theorem firstHit_variance_paired_lower (N m T : ℕ) (hN : 3 ≤ N) (hm : 1 ≤ m) (ht : 2 ≤ T)
    (b : ℝ) (hb : 0≤b) (hb' : b≤1) :
    CircleEulerLimits.unitBound m T ≤ variance (firstHitMean N m T) (seedLaw m) ∧
    CircleEulerLimits.unitBound m T / 4 ≤
      ∫ ω, (firstHitMean N m T ω-reference N m b ω)^2 ∂seedLaw m := by
  let L := Real.sqrt (64*(m:ℝ))
  let A := amplitude m T L
  let p := Real.exp (-896*(m:ℝ)^2/1)
  let tol := 1/(N:ℝ)^3
  let F := firstHitMean N m T
  let Z := reference N m b
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have lp : 0<L := Real.sqrt_pos.mpr (by positivity)
  have sc : L^2 = 64*(m:ℝ) := Real.sq_sqrt (by positivity)
  have sc' : L^2 = 64*(m:ℝ)/1 := by simpa using sc
  have mass (neg : Bool) : p ≤ (seedLaw m).real (box m L neg) := by
    have h := exponential_mass 4 m (by decide) hm 1 L (by norm_num) (by norm_num) lp
      (by convert sc' using 1; norm_num)
    have eq : -896*(m:ℝ)^2/1 = -14*m*L^2 := by rw [sc]; ring
    exact (show p≤_ by simpa only [p,eq] using h).trans (signed_gaussian_mass m L lp.le neg)
  have bound (neg : Bool) (ω : Seed m) (hw : ω∈box m L neg) :
      A ≤ ((-1:ℝ)^T*(if neg then -1 else 1))*F ω := by
    let u := train N m 1 (initial ω)
    let σ : ℝ := if neg then -1 else 1
    have sgn : |σ|=1 := by cases neg <;> norm_num [σ]
    have start (j : Fin m) : 2*L ≤ σ*(u 0).a j ∧ 2*L ≤ ((u 0).w j).re := by
      cases neg
      · exact ⟨by simpa [σ,u,train,initial] using (hw (j,0) (mem_univ _)).1,(hw (j,1) (mem_univ _)).1⟩
      · exact ⟨by simpa [σ,u,train,initial] using (hw (j,0) (mem_univ _)).1,(hw (j,1) (mem_univ _)).1⟩
    have never : ¬∃ s≤T, gridRms N m (u s) ≤ tol := by
      rintro ⟨s,_,yes⟩
      exact (signed_boxes_never_hit N m hN hm 1 L (by norm_num) (by norm_num) lp sc' neg ω hw s).not_ge yes
    have last : firstHit T (fun s => gridRms N m (u s) ≤ tol) = T := by simp [firstHit,never]
    change A ≤ ((-1:ℝ)^T*σ)*populationMean (1/Real.sqrt m) (u (firstHit T (fun s => gridRms N m (u s) ≤ tol)))
    rw [last]
    exact CircleGridEscape.circle_escape_uniform N m hN hm 1 L σ (by norm_num) (by norm_num) lp sc' u (fun _ => rfl) sgn start T
  have hF : MemLp F 2 (seedLaw m) := by
    have hZ := CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num)
    have mf : Measurable F := (stoppedObservation_measurable N m T tol (fun _ => 1) measurable_const).snd.snd
    have d : MemLp (F-Z) 2 (seedLaw m) := (memLp_two_iff_integrable_sq
      (mf.sub (reference_measurable N m b)).aestronglyMeasurable).2 (ordinary_stop_integrable N m T tol b)
    change MemLp Z 2 (seedLaw m) at hZ
    simpa using d.add hZ
  have pos (ω : Seed m) (hw : ω∈box m L false) : A ≤ (-1:ℝ)^T*F ω := by simpa using bound false ω hw
  have neg (ω : Seed m) (hw : ω∈box m L true) : A ≤ -((-1:ℝ)^T*F ω) := by simpa [neg_mul] using bound true ω hw
  have an : 0≤A := by dsimp [A,amplitude];positivity
  have beq : p*A^2 = CircleEulerLimits.unitBound m T := CircleEulerLimits.mass_amplitude_eq_unitBound m T sc
  constructor
  · rw [←beq]
    rcases Nat.even_or_odd T with ev|od
    · apply CircleTails.variance_of_opposite_tails hF (measurable_box m L false) (measurable_box m L true) an (mass false) (mass true)
      · simpa only [ev.neg_one_pow,one_mul] using pos
      · intro ω hω; have h := neg ω hω; rw [ev.neg_one_pow,one_mul] at h; linarith
    · apply CircleTails.variance_of_opposite_tails hF (measurable_box m L true) (measurable_box m L false) an (mass true) (mass false)
      · simpa only [od.neg_one_pow,neg_one_mul,neg_neg] using neg
      · intro ω hω; have h := pos ω hω; rw [od.neg_one_pow,neg_one_mul] at h; linarith
  · have LB := CircleEscapeMoment.paired_second_moment_of_escape hF
      (CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num)) (measurable_box m L false) (mass false)
      (fun ω hw => (pos ω hw).trans (by simpa [abs_mul,abs_pow] using le_abs_self ((-1:ℝ)^T*F ω)))
      (reference_on_box N m (by omega) hm L b lp.le hb hb')
    have ref := CircleEulerLimits.half_amplitude m T hm ht (L:=L) (by rw [sc]; linarith [show (1:ℝ)≤m by exact_mod_cast hm])
    have hle : A/2 ≤ max (A-referenceCap m L) 0 := (by linarith : A/2 ≤ A-referenceCap m L).trans (le_max_left ..)
    rw [←beq]
    calc
      _ = p*(A/2)^2 := by ring
      _ ≤ p*(max (A-referenceCap m L) 0)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith) hle 2) (Real.exp_pos _).le
      _ ≤ _ := LB

/-- Returning the final iterate on a miss retains divergence of both the
unconditional variance and the unconditional paired squared error. The
signed escape boxes always miss, so first-hit selection never removes them.
This covers the original middle and long caps. -/
theorem firstHit_unconditional_diverges (T : ℕ → ℕ)
    (time : ∀ᶠ N : ℕ in atTop, 60*Real.log N ≤ (T N:ℝ))
    (b : ℕ → ℝ) (hb : ∀ N, 0 ≤ b N ∧ b N ≤ 1) :
    Tendsto (fun N : ℕ => variance (firstHitMean N (N^32) (T N)) (seedLaw (N^32))) atTop atTop ∧
    Tendsto (fun N : ℕ => ∫ ω, (firstHitMean N (N^32) (T N) ω-reference N (N^32) (b N) ω)^2 ∂seedLaw (N^32)) atTop atTop := by
  have all := CircleEulerLimits.unitBound_growing_tendsto T 60 (by linarith [Real.log_three_gt_d9]) time
  have eventual : ∀ᶠ N : ℕ in atTop, 3≤N ∧ 2≤T N := by
    filter_upwards [eventually_ge_atTop 3,time] with N hn ht
    have lo : (3:ℝ)≤N := by exact_mod_cast hn
    have h := Real.log_le_log (by norm_num : (0:ℝ)<3) lo
    have tt : (2:ℝ)≤T N := by linarith [Real.log_three_gt_d9]
    exact ⟨hn,by exact_mod_cast tt⟩
  have bound := eventual.mono (fun N h => firstHit_variance_paired_lower N (N^32) (T N) h.1
    (one_le_pow₀ (by omega)) h.2 (b N) (hb N).1 (hb N).2)
  exact ⟨tendsto_atTop_mono' atTop (bound.mono (fun _ h => h.1)) all,
    tendsto_atTop_mono' atTop (bound.mono (fun _ h => h.2)) (by
      simpa only [div_eq_mul_inv] using all.atTop_mul_const (by norm_num : 0 < (4:ℝ)⁻¹))⟩

/-- In particular the fallback at the original physical design horizon H
gives two divergent unconditional moments even though the success-conditioned
paired square still has the separate reduction above. -/
theorem firstHit_horizon_diverges (b : ℕ → ℝ) (hb : ∀ N, 0≤b N ∧ b N≤1) :
    let T := fun N : ℕ => CircleFlowTracking.horizon (N:ℝ)
    Tendsto (fun N : ℕ => variance (firstHitMean N (N^32) (T N)) (seedLaw (N^32))) atTop atTop ∧
    Tendsto (fun N : ℕ => ∫ ω, (firstHitMean N (N^32) (T N) ω-reference N (N^32) (b N) ω)^2 ∂seedLaw (N^32)) atTop atTop := by
  intro T
  apply firstHit_unconditional_diverges T _ b hb
  filter_upwards [eventually_ge_atTop 3] with N hn
  have n3 : (3:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have n1 : (1:ℝ)≤N := by linarith
  have p3 : (N:ℝ)≤(N:ℝ)^3 := by simpa only [pow_one] using pow_le_pow_right₀ n1 (by decide : 1≤3)
  have r := Real.one_le_sqrt.mpr (by linarith : (1:ℝ)≤12*N)
  have big := p3.trans (le_mul_of_one_le_left (by positivity : 0≤(N:ℝ)^3)
    (by linarith : 1≤2*Real.sqrt (12*N)))
  have factor : (60:ℝ) ≤ 2*Real.pi^2*(N:ℝ)^2 := by
    calc _ ≤ 2*(3:ℝ)^2*(3:ℝ)^2 := by norm_num
         _ ≤ _ := by gcongr; exact Real.pi_gt_three.le
  apply (mul_le_mul factor (Real.log_le_log np big) (Real.log_nonneg n1) (by positivity)).trans
  exact Nat.le_ceil _

end CircleConditioning
