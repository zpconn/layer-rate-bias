module

public import CircleConditioning
public import CircleRateTrajectory
import all CircleNarrowConditioning
import all CircleWidthTracking
import all CircleRateTrajectory
import all CircleGDLimits
import all CircleComparison
import all CircleSeedIntegrability
import all CircleEscapeBridge
import all CircleConditioning
import all CircleDiscreteTracking
import all CircleActualTracking
import all CircleSharpEvent
import all CircleSharpInitialization
import all CircleCapMoments
import all CircleGaussianTracking
import all CircleKernelGD
import Mathlib.Tactic


/-! Fit-conditioned moments for any positive learning rate at most one.
The same Gaussian event controls every rate, and the original discrete
learner returns at the explicitly rounded reciprocal-rate horizon. -/
public section
noncomputable section
namespace CircleRateConditioning
open Real MeasureTheory ProbabilityTheory Set Finset CircleEscapeBridge CircleFlowPath
  CircleTangentDrift CircleActualTracking CircleGridSpectrum CircleSpectrum
  CircleCapMoments CircleGaussianTracking CircleWidthTracking CircleRateTrajectory
open CircleNarrowConditioning (FitTest Endpoint Certificate envelopeConstant mseConstant)
variable {N m : ℕ}
variable (η : ℝ)

private theorem rms_eq (N m t : ℕ) (z : Seed m) :
    CircleConditioning.gridRms N m (CircleInitializationCheck.train N m η (initial z) t) = rms η N z t := by
  rw [←iterateAt_eq_train]
  rw [rms,←Real.sqrt_sq (norm_nonneg _),gridR,rmsCoordinates_norm_sq]
  unfold CircleConditioning.gridRms
  simp only [CircleDiscreteTracking.output_complex]
  rfl

private theorem meas_rms (N m t : ℕ) : Measurable (fun z : Seed m => rms η N z t) := by
  have h := (CircleConditioning.random_rate_statistics N m (fun _ => η) measurable_const t).1
  simpa only [rms_eq,rms] using h

private theorem mean_eq (N : ℕ) (z : Seed m) (t : ℕ) :
    learnerMean η N z t = trainedMean (CircleSeedIntegrability.path N m η) t z :=
  congrArg (CircleEscape.populationMean (1/sqrt (m:ℝ))) (iterateAt_eq_train N η z t)

private theorem meas_mean (N m t : ℕ) : Measurable (fun z : Seed m => learnerMean η N z t) := by
  simpa only [mean_eq,trainedMean,CircleSeedIntegrability.path] using (CircleConditioning.random_rate_statistics N m (fun _ => η) measurable_const t).2

private theorem meas_energy (N m t : ℕ) : Measurable (fun z : Seed m => meanEnergy (iterateAt N η z t)) := by
  simp only [CircleNarrowConditioning.energy_eq,iterateAt_eq_train,CircleCapInduction.energy,CircleCapInduction.rawEnergy]
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro j _
  have h := CircleConditioning.random_rate_parameters N m (fun _ => η) measurable_const t j
  exact (h.1.pow_const 2).add (h.2.norm.pow_const 2)

private theorem meas_budget (N m t : ℕ) : Measurable (fun z : Seed m => budget η N z t) :=
  measurable_const.mul (Finset.measurable_fun_sum _ (fun j _ => meas_rms η N m j))

/-- Fourth moment on any measurable observable certificate, including rare
fits outside the initialization event. Either the returned energy or the
entire cumulative residual can certify an individual fit. -/
private theorem exceptional (hη : 0≤η) {N m : ℕ} (hn : 0<N) (hm : 0<m) (t : Seed m → ℕ) (mt : Measurable t)
    {A : Set (Seed m)} (ma : MeasurableSet A)
    (guard : ∀ z ∈ A, meanEnergy (iterateAt N η z (t z))≤5 ∨ budget η N z (t z)≤sqrt m)
    (b : ℝ) (hb : 0≤b) (hb' : b≤1) (G : Set (Seed m)) :
    let D := fun z => CircleNarrowConditioning.filled A (fun w => learnerMean η N w (t w)) z-reference N m b z
    Integrable (fun z => (D z)^2) (seedLaw m) ∧
      (∫ z in G, (D z)^2 ∂seedLaw m) ≤ (100*envelopeConstant^2)*m*sqrt ((seedLaw m).real G) := by
  intro D
  have md : Measurable D := (CircleNarrowConditioning.filled_meas ma (CircleNarrowConditioning.meas_stop mt (meas_mean η N m))).sub (reference_measurable N m b)
  have c : 0<envelopeConstant := by unfold envelopeConstant;positivity
  have env : ∀ᵐ z ∂seedLaw m, |D z/envelopeConstant| ≤ sqrt m*(CircleCapInduction.energy (initial z)+1)/2 := by
    filter_upwards with z
    let E := CircleCapInduction.energy (initial z)
    have en : 0≤E := by change 0≤CircleCapInduction.energy (initial z);rw [←CircleNarrowConditioning.energy_eq];unfold meanEnergy;positivity
    have root : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
    have re := reference_envelope N m hn hm b hb hb' z
    change |reference N m b z| ≤ 1+sqrt m*E at re
    rw [abs_div,abs_of_pos c,div_le_iff₀ c]
    by_cases h : z∈A
    · have actual := mean_le_energy m hm (initial (iterateAt N η z (t z)))
      change |learnerMean η N z (t z)|≤sqrt m*CircleCapInduction.energy (initial (iterateAt N η z (t z)))/2 at actual
      rw [←CircleNarrowConditioning.energy_eq] at actual
      have bnd : meanEnergy (iterateAt N η z (t z)) ≤ 5+(exp 8)^2*E := by
        rcases guard z h with h'|h'
        · exact h'.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) en))
        · exact (budget_energy hη hn hm z _ h').trans (by rw [CircleNarrowConditioning.energy_eq];linarith)
      have f := (mul_le_mul_of_nonneg_left bnd (sqrt_nonneg (m:ℝ)))
      simp only [D,CircleNarrowConditioning.filled,ite_eq_left h]
      apply (abs_sub ..).trans ((add_le_add actual re).trans ?_)
      change _≤sqrt m*(E+1)/2*envelopeConstant
      unfold envelopeConstant
      nlinarith only [f,root,mul_nonneg (sqrt_nonneg (m:ℝ)) en,
        mul_nonneg (sqrt_nonneg (m:ℝ)) (sq_nonneg (exp 8)),
        mul_nonneg (mul_nonneg (sqrt_nonneg (m:ℝ)) en) (sq_nonneg (exp 8))]
    · simp only [D,CircleNarrowConditioning.filled,ite_eq_right h]
      apply (abs_sub ..).trans ((add_le_add (le_refl _) re).trans ?_)
      change |(1:ℝ)| + (1+sqrt m*E) ≤ sqrt m*(E+1)/2*envelopeConstant
      rw [abs_one];unfold envelopeConstant
      nlinarith only [root,mul_nonneg (sqrt_nonneg (m:ℝ)) en,
        mul_nonneg (sqrt_nonneg (m:ℝ)) (sq_nonneg (exp 8)),
        mul_nonneg (mul_nonneg (sqrt_nonneg (m:ℝ)) en) (sq_nonneg (exp 8))]
  obtain ⟨i,bound⟩ := CircleCapMoments.envelope_fourth m hm _ (md.div_const _) env
  have eq (z) : (D z)^4 = envelopeConstant^4*(D z/envelopeConstant)^4 := by field_simp
  have four : Integrable (fun z => (D z)^4) (seedLaw m) := by simp_rw [eq];exact i.const_mul _
  have mem : MemLp (fun z => (D z)^2) 2 (seedLaw m) :=
    (memLp_two_iff_integrable_sq (md.pow_const 2).aestronglyMeasurable).2 (by simpa only [←pow_mul] using four)
  refine ⟨mem.integrable one_le_two,(CircleMoment.exceptional_second_moment mem G).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg _)
  apply (sqrt_le_left (by positivity)).mpr
  simp_rw [eq]; rw [integral_const_mul,gaussian_eighth] at *
  exact (mul_le_mul_of_nonneg_left bound (pow_nonneg c.le 4)).trans (by
    nlinarith only [mul_nonneg (pow_nonneg c.le 4) (sq_nonneg (m:ℝ))])


def trainingResidual (N : ℕ) (z : Seed m) (t : ℕ) (i : Fin N) : ℝ :=
  CircleEscape.output (1/sqrt m) (CircleInitializationCheck.train N m η (initial z) t)
    (CircleEscape.gridPoint N i) - (1+(CircleEscape.gridPoint N i).re)

def hits (test : FitTest) (N : ℕ) (z : Seed m) (t : ℕ) : Prop :=
  match test with
  | .rms => rms η N z t ≤ 1/(N:ℝ)^3
  | .maxResidual => ∀ i, |trainingResidual η N z t i| ≤ 1/(N:ℝ)^3

def returned (stop : Endpoint) (test : FitTest) (N : ℕ) (z : Seed m) : ℕ :=
  match stop with
  | .cap => CircleRateTrajectory.horizon η N
  | .firstHit => @CircleConditioning.firstHit (CircleRateTrajectory.horizon η N) (hits η test N z) (Classical.decPred _)

def certified (cert : Certificate) (N : ℕ) (z : Seed m) (t : ℕ) : Prop :=
  match cert with
  | .budget => budget η N z t ≤ sqrt m
  | .energy => meanEnergy (iterateAt N η z t) ≤ 5
  | .either => budget η N z t ≤ sqrt m ∨ meanEnergy (iterateAt N η z t) ≤ 5

def accepted (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) : Set (Seed m) :=
  {z | hits η test N z (returned η stop test N z) ∧ certified η cert N z (returned η stop test N z)}

private theorem rms_sq (N : ℕ) (z : Seed m) (t : ℕ) :
    (rms η N z t)^2 = (∑ i, (trainingResidual η N z t i)^2)/N := by
  rw [←rms_eq,CircleConditioning.gridRms,sq_sqrt (by positivity)]
  rfl

private theorem hit_sandwich (test : FitTest) {N : ℕ} (hn : 0<N) (z : Seed m) (t : ℕ) :
    (sqrt N*rms η N z t ≤ 1/(N:ℝ)^3 → hits η test N z t) ∧
      (hits η test N z t → rms η N z t ≤ 1/(N:ℝ)^3) := by
  have mp : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have sq := rms_sq η N z t
  have all : (∑ i, (trainingResidual η N z t i)^2)=(N:ℝ)*(rms η N z t)^2 :=
    (by have h := (eq_div_iff mp.ne').mp sq;linarith)
  have non : 0≤rms η N z t := norm_nonneg _
  cases test with
  | rms =>
    exact ⟨fun h => (le_mul_of_one_le_left non (one_le_sqrt.mpr (by exact_mod_cast hn))).trans h,id⟩
  | maxResidual =>
    constructor
    · intro h i
      apply le_trans _ h
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (sqrt_nonneg _) non)).mp
      rw [sq_abs,mul_pow,sq_sqrt mp.le,←all]
      exact Finset.single_le_sum (f:=fun i => trainingResidual η N z t i ^2) (fun _ _ => sq_nonneg _) (mem_univ i)
    · intro h
      apply (sq_le_sq₀ non (by positivity)).mp
      rw [sq,div_le_iff₀ mp]
      have hsum := Finset.sum_le_sum (s:=univ) (g:=fun _ : Fin N => (1/(N:ℝ)^3)^2)
        (fun i _ => (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (h i) 2))
      simpa [mul_comm] using hsum

private theorem meas_hit (test : FitTest) (N m : ℕ) (t : Seed m→ℕ) (mt : Measurable t) :
    MeasurableSet {z | hits η test N z (t z)} := by
  classical
  cases test with
  | rms => exact measurableSet_le (CircleNarrowConditioning.meas_stop mt (meas_rms η N m)) measurable_const
  | maxResidual =>
    change MeasurableSet {z : Seed m | ∀ i, |trainingResidual η N z (t z) i| ≤ 1/(N:ℝ)^3}
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    apply continuous_abs.measurable.comp
    apply CircleNarrowConditioning.meas_stop (f:=fun z t => trainingResidual η N z t i) mt
    intro k
    let u := fun z : Seed m => CircleInitializationCheck.train N m η (initial z) k
    have h := CircleConditioning.random_rate_parameters N m (fun _ => η) measurable_const k
    exact (CircleSeedIntegrability.output_meas u (fun j => (h j).1) (fun j => (h j).2) _ _).sub measurable_const

private theorem meas_returned (stop : Endpoint) (test : FitTest) (N m : ℕ) :
    Measurable (returned η (m:=m) stop test N) := by
  classical
  cases stop with
  | cap => exact measurable_const
  | firstHit =>
    apply CircleConditioning.firstHit_measurable
    exact fun t => meas_hit η test N m (fun _ => t) measurable_const

theorem measurable_accepted (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) :
    MeasurableSet (accepted η stop test cert N m) := by
  let t := returned η (m:=m) stop test N
  have mt := meas_returned η stop test N m
  have a := meas_hit η test N m t mt
  have eb := measurableSet_le (CircleNarrowConditioning.meas_stop mt (meas_energy η N m)) (measurable_const (a:=(5:ℝ)))
  have bb := measurableSet_le (CircleNarrowConditioning.meas_stop mt (meas_budget η N m)) (measurable_const (a:=sqrt (m:ℝ)))
  cases cert with
  | budget => exact a.inter bb
  | energy => exact a.inter eb
  | either => exact a.inter (bb.union eb)

def completedMean (stop : Endpoint) (test : FitTest) (cert : Certificate) (N m : ℕ) :=
  CircleNarrowConditioning.filled (accepted η stop test cert N m) (fun z => learnerMean η N z (returned η stop test N z))

/-- Conditional paired second moment at width N¹⁶ with actual Gaussian
initialization, ordinary fixed steps and the archived horizon. All combinations
of fixed cap or first hit, RMS or max-residual fit, and either observable
certificate are covered. -/
theorem conditional_mse (hη : 0<η) (hc : η≤1) (n : ℕ) (hN : 10000000000≤n+1) (odd : Odd (n+1))
    (stop : Endpoint) (test : FitTest) (cert : Certificate) :
    let N := n+1
    let m := N^16
    let μ := seedLaw m
    let A := accepted η stop test cert N m
    let t := returned η (m:=m) stop test N
    1-12/(N:ℝ)^98 ≤ μ.real A ∧
      MemLp (completedMean η stop test cert N m) 2 μ ∧
      (∫ z, (completedMean η stop test cert N m z-reference N m (weight 1 n) z)^2 ∂μ) ≤ mseConstant/(N:ℝ)^6 ∧
      (∫ z, (learnerMean η N z (t z)-reference N m (weight 1 n) z)^2 ∂cond μ A) ≤ mseConstant/(N:ℝ)^6 := by
  classical
  intro N m μ A t
  have nn : 0<N := Nat.succ_pos _
  have hm : 0<m := pow_pos nn _
  have np : (0:ℝ)<N := Nat.cast_pos.mpr nn
  have one : (1:ℝ)≤N := by exact_mod_cast nn
  have large : (10000000000:ℝ)≤N := by exact_mod_cast hN
  have ma := measurable_accepted η stop test cert N m
  have mt := meas_returned η stop test N m
  obtain ⟨G,mg,pr,good⟩ := CircleNarrowConditioning.gaussian_event N hN
  let Y := fun z => learnerMean η N z (t z)-reference N m (weight 1 n) z
  let W := completedMean η stop test cert N m
  let D := fun z => W z-reference N m (weight 1 n) z
  have cap (z : Seed m) (hz : z∈G) := trajectory η hη hc n hN odd z (good z hz).1 (good z hz).2
  have gh (z : Seed m) (hz : z∈G) : hits η test N z (t z) := by
    have Hcap := (hit_sandwich η test nn z _).1 (cap z hz).1
    cases stop with
    | cap => exact Hcap
    | firstHit =>
      apply (@CircleConditioning.firstHit_spec (CircleRateTrajectory.horizon η N) (hits η test N z) _).2.1.mpr
      exact ⟨_,le_rfl,Hcap⟩
  have ga : G⊆A := by
    intro z hz
    refine ⟨gh z hz,?_⟩
    have h := (cap z hz).2 (t z)
    cases cert with
    | budget => exact h.1
    | energy => exact h.2.1
    | either => exact Or.inl h.1
  have prA : 1-12/(N:ℝ)^98 ≤ μ.real A := by
    have h := measureReal_mono (μ:=μ) ga
    have pr' : μ.real Gᶜ ≤ 12/(N:ℝ)^98 := pr
    rw [measureReal_compl mg,probReal_univ] at pr'
    linarith
  have guard (z : Seed m) (hz : z∈A) : meanEnergy (iterateAt N η z (t z))≤5 ∨ budget η N z (t z)≤sqrt m := by
    have h := hz.2
    cases cert with
    | budget => exact Or.inr h
    | energy => exact Or.inl h
    | either => exact h.symm
  have wt := CircleGaussianTracking.weight_bounds n (τ:=1) (by norm_num)
  obtain ⟨inte,tail⟩ := exceptional η hη.le nn hm t mt ma guard (weight 1 n) wt.1 wt.2 Gᶜ
  change Integrable (fun z => (D z)^2) μ at inte
  change (∫ z in Gᶜ, (D z)^2 ∂μ) ≤ 100*envelopeConstant^2*(m:ℝ)*sqrt (μ.real Gᶜ) at tail
  have root : sqrt (μ.real Gᶜ) ≤ 4/(N:ℝ)^49 := by
    apply (sqrt_le_iff).mpr ⟨by positivity,pr.trans ?_⟩
    rw [div_pow,←pow_mul];norm_num;gcongr;norm_num
  have bad := tail.trans (mul_le_mul_of_nonneg_left root (by positivity))
  have small : 100*envelopeConstant^2*(m:ℝ)*(4/(N:ℝ)^49) ≤ 400*envelopeConstant^2/(N:ℝ)^6 := by
    dsimp only [m];push_cast
    calc
      _ = 400*envelopeConstant^2/(N:ℝ)^33 := by field_simp;ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ one (by decide : 6≤33))
  let B := (1+CircleNarrowConditioning.discrepancyConstant)/(N:ℝ)^3
  have val (z) (hz : z∈G) : |D z|≤B := by
    have h : z∈accepted η stop test cert N m := ga hz
    simp only [D,W,completedMean,CircleNarrowConditioning.filled,ite_eq_left h]
    apply ((cap z hz).2 (t z)).2.2.trans
    calc
      _ ≤ 1/(N:ℝ)^3+CircleNarrowConditioning.discrepancyConstant/(N:ℝ)^3 := add_le_add ((hit_sandwich η test nn z (t z)).2 (gh z hz)) le_rfl
      _ = B := by unfold B;ring
  have goodInt : (∫ z in G, (D z)^2 ∂μ) ≤ B^2 := by
    have bound := setIntegral_mono_on inte.integrableOn (integrable_const (B^2)) mg (fun z hz =>
      (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (val z hz) 2))
    exact bound.trans (by rw [setIntegral_const,smul_eq_mul];exact (mul_le_mul_of_nonneg_right (measureReal_le_one (μ:=μ) (s:=G)) (sq_nonneg B)).trans_eq (one_mul _))
  let C := (1+CircleNarrowConditioning.discrepancyConstant)^2+400*envelopeConstant^2
  have all : (∫ z, (D z)^2 ∂μ) ≤ C/(N:ℝ)^6 := by
    rw [←integral_add_compl mg inte]
    exact (add_le_add goodInt (bad.trans small)).trans_eq (by dsimp [B,C];ring)
  have half : 1/2 ≤ μ.real A := by
    have ge : (24:ℝ) ≤ (N:ℝ)^98 := (by linarith only [large] : 24≤(N:ℝ)).trans (by simpa using pow_le_pow_right₀ one (by decide : 1≤98))
    have le : 12/(N:ℝ)^98 ≤1/2 := (div_le_div_iff₀ (by positivity) (by norm_num)).2 (by linarith)
    linarith only [prA,le]
  have cp : 0≤C/(N:ℝ)^6 := by dsimp [C];positivity
  have wm : Measurable W := CircleNarrowConditioning.filled_meas ma (CircleNarrowConditioning.meas_stop mt (meas_mean η N m))
  have zm := CircleSeedIntegrability.reference_memLp N m (weight 1 n) 2 (by norm_num)
  have dm : MemLp D 2 μ := (memLp_two_iff_integrable_sq (wm.sub (reference_measurable N m (weight 1 n))).aestronglyMeasurable).2 inte
  have wl : MemLp W 2 μ := by
    have h := dm.add zm
    simpa only [Pi.add_def,D,sub_add_cancel] using h
  have eq : (∫ z in A, (Y z)^2 ∂μ) = ∫ z in A, (D z)^2 ∂μ := by
    apply setIntegral_congr_fun ma
    intro z hz
    change z∈accepted η stop test cert N m at hz
    simp only [D,W,completedMean,CircleNarrowConditioning.filled,ite_eq_left hz,Y,t]
  have on := eq.le.trans ((setIntegral_le_integral inte (ae_of_all _ fun z => sq_nonneg (D z))).trans all)
  refine ⟨prA,wl,all.trans (by change C/(N:ℝ)^6≤2*C/(N:ℝ)^6;linarith only [cp,show 2*C/(N:ℝ)^6=2*(C/(N:ℝ)^6) by ring]),?_⟩
  change (∫ z, (Y z)^2 ∂cond μ A) ≤ _
  rw [ProbabilityTheory.cond,integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul,←div_eq_inv_mul]
  apply (div_le_iff₀ (by change 0<μ.real A;linarith only [half])).mpr
  apply on.trans
  change C/(N:ℝ)^6 ≤ (2*C/(N:ℝ)^6)*μ.real A
  nlinarith only [mul_le_mul_of_nonneg_left half cp, show 2*C/(N:ℝ)^6*(μ.real A) =2*(C/(N:ℝ)^6)*(μ.real A) by ring]


open Filter Topology

set_option maxHeartbeats 900000 in
/-- The fit-conditioned signed bias and variance at width N¹⁶ converge to
the original Gaussian-reference constants after either observable trajectory
certificate. The scope includes the weaker disjunction of the two checks. -/
theorem conditional_limits (rates : ℕ→ℝ) (hp : ∀ i, 0<rates i) (hc : ∀ i, rates i≤1) (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 10000000000≤n i+1) (odd : ∀ i, Odd (n i+1))
    (stop : Endpoint) (test : FitTest) (cert : Certificate) :
    let N := fun i => n i+1
    let m := fun i => (N i)^16
    let ν := fun i => cond (seedLaw (m i)) (accepted (rates i) stop test cert (N i) (m i))
    let Y := fun i (z : Seed (m i)) => learnerMean (rates i) (N i) z (returned (rates i) stop test (N i) z)
    Tendsto (fun i => ((n i:ℝ)+1)^2*((∫ z, Y i z ∂ν i)-1)) atTop (𝓝 (-(π^2/36))) ∧
      Tendsto (fun i => ((n i:ℝ)+1)^4*ProbabilityTheory.variance (Y i) (ν i)) atTop (𝓝 (7*π^2/1620)) := by
  intro N m ν Y
  let x (i : ℕ) := (n i:ℝ)+1
  let μ (i : ℕ) := seedLaw (m i)
  let A (i : ℕ) := accepted (rates i) stop test cert (N i) (m i)
  let W (i : ℕ) := completedMean (rates i) stop test cert (N i) (m i)
  let b := -(π^2/36)
  let v := 7*π^2/1620
  let p (i : ℕ) := (μ i).real (A i)
  have ma (i : ℕ) : MeasurableSet (A i) := measurable_accepted (rates i) .. 
  have data (i : ℕ) := conditional_mse (rates i) (hp i) (hc i) (n i) (hn i) (odd i) stop test cert
  have prob (i : ℕ) : 1-12/(x i)^98≤p i := by
    simpa only [x,Nat.cast_add,Nat.cast_one] using (data i).1
  have wm (i : ℕ) : MemLp (W i) 2 (μ i) := (data i).2.1
  have cpos : 0≤mseConstant := by unfold mseConstant;positivity
  have all := CircleComparison.gaussian_reference_transfer n m grow (fun i => by have := hn i;omega)
    odd (fun i => pow_pos (Nat.succ_pos _) _) (τ:=1) (by norm_num) W wm
    (CircleGDLimits.scaled_rms n grow cpos (fun i => by
      simpa only [Nat.cast_add,Nat.cast_one] using (data i).2.2.1))
  have fullBias : Tendsto (fun i => (x i)^2*((∫ z, W i z ∂μ i)-1)) atTop (𝓝 b) := by
    convert all.1.neg using 2 with i <;> dsimp [x,b,μ] <;> ring
  have fullVar : Tendsto (fun i => (x i)^4*ProbabilityTheory.variance (W i) (μ i)) atTop (𝓝 v) := by
    convert all.2 using 2; ring
  have nz (i : ℕ) : μ i (A i)≠0 := by
    intro h
    have hp : p i=0 := by change (μ i (A i)).toReal=0;rw [h,ENNReal.toReal_zero]
    have one : 1≤x i := by dsimp [x];linarith only [Nat.cast_nonneg (α:=ℝ) (n i)]
    have hi : 10000000000≤x i := by dsimp [x];exact_mod_cast hn i
    have pos : 12/(x i)^98 < 1 := (div_lt_one (by positivity)).mpr ((by linarith only [hi] : (12:ℝ)<x i).trans_le
      (by simpa using pow_le_pow_right₀ one (by decide : 1≤98)))
    linarith only [prob i,hp,pos]
  let probLaw (i : ℕ) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (nz i)
  have ym (i : ℕ) : MemLp (Y i) 2 (ν i) := by
    have wi : MemLp (W i) 2 (ν i) := ((wm i).restrict (s:=A i)).smul_measure (by simpa using nz i)
    apply wi.ae_eq
    apply Measure.ae_smul_measure
    apply (ae_restrict_iff' (ma i)).mpr
    exact ae_of_all _ fun z hz => by change CircleNarrowConditioning.filled (A i) (Y i) z=Y i z;simp [CircleNarrowConditioning.filled,hz]
  have pl : Tendsto p atTop (𝓝 1) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp grow).pow 98
    have lo : Tendsto (fun i => 1-12/(x i)^98) atTop (𝓝 1) := by
      simpa [x,div_pow,div_eq_mul_inv] using (tendsto_const_nhds (x:=(1:ℝ))).sub (h.const_mul 12)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le lo tendsto_const_nhds prob (fun _ => measureReal_le_one)
  have fullRisk : Tendsto (fun i => (x i)^4*∫ z, (W i z-1)^2 ∂μ i) atTop (𝓝 (v+b^2)) := by
    convert fullVar.add (fullBias.pow 2) using 2 with i
    rw [CircleStats.mse_decomposition (wm i) 1];ring
  have bias : Tendsto (fun i => (x i)^2*((∫ z, Y i z ∂ν i)-1)) atTop (𝓝 b) := by
    convert fullBias.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := CircleNarrowConditioning.centered_integral (μ i) (ma i) (Y i) (W i) (fun y => y-1) (by norm_num) rfl
      change (∫ z, Y i z-1 ∂ν i) = (∫ z, W i z-1 ∂μ i)/p i at h
      rw [integral_sub ((ym i).integrable one_le_two) (integrable_const _),
        integral_sub ((wm i).integrable one_le_two) (integrable_const _),integral_const,integral_const,
        probReal_univ,probReal_univ,one_smul] at h
      rw [h,Pi.div_apply];ring
    · ring
  have risk : Tendsto (fun i => (x i)^4*∫ z, (Y i z-1)^2 ∂ν i) atTop (𝓝 (v+b^2)) := by
    convert fullRisk.div pl (by norm_num : (1:ℝ)≠0) using 2 with i
    · have h := CircleNarrowConditioning.centered_integral (μ i) (ma i) (Y i) (W i) (fun y => (y-1)^2) (by norm_num) rfl
      change (∫ z, (Y i z-1)^2 ∂ν i) = (∫ z, (W i z-1)^2 ∂μ i)/p i at h
      rw [h,Pi.div_apply];ring
    · ring
  refine ⟨bias,?_⟩
  convert risk.sub (bias.pow 2) using 2 with i
  · rw [CircleStats.mse_decomposition (ym i) 1];ring
  · ring

end CircleRateConditioning
