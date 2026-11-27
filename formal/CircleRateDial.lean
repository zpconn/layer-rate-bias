module
public import CircleSharpMoments
public import CirclePositiveSchedule
public import CircleComparison
public import CirclePairedCoefficient
public import CircleFiniteCoefficient
import all CirclePositiveSchedule
import all CirclePositiveWidth
import all CircleFiniteSchedule
import all CircleComparison
import all CirclePairedCoefficient
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Common-seed comparisons for two chosen hidden-layer multipliers. -/
@[expose] public section
noncomputable section
namespace CircleRateDial
open Real MeasureTheory Filter Topology CircleEscapeBridge CircleFlowPath CircleSpectrum
  CircleWeightedStep CircleWeightedDynamics CirclePositiveSchedule CirclePairedCoefficient

def coefficient (n : ℕ) (τ σ : ℝ) := ((n:ℝ)+1)^2 * (weight τ n - weight σ n)

theorem coefficient_pos (n : ℕ) {τ σ : ℝ} (hτ : 0 ≤ τ) (h : τ < σ) :
    0 < coefficient n τ σ :=
  mul_pos (by positivity) (sub_pos.mpr (CircleFiniteCoefficient.weight_strict_decrease hτ h n))

theorem coefficient_limit {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) :
    Tendsto (fun n => coefficient n τ σ) atTop (𝓝 (π^2/12*(σ/(2+σ)-τ/(2+τ)))) := by
  convert (bias_limit σ hσ).sub (bias_limit τ hτ) using 1
  · ext n; unfold coefficient; ring
  · congr 1; field_simp

private theorem design_bound (n : ℕ) (hn : 3≤n+1) {τ : ℝ} (hp : 0<τ) :
    let N := n+1
    let δ := 1/(N:ℝ)
    CirclePositiveWidth.width τ n δ δ ≤ sqrt (designWidth τ N : ℝ) := by
  intro N δ
  have d : 0<δ := by dsimp [δ,N]; positivity
  have fit := CircleFiniteSchedule.width_bound n hn
  change CircleFiniteWidth.width n δ δ≤sqrt (CircleFiniteSchedule.designWidth N:ℝ) at fit
  apply (width_compare n hn hp d d).trans
  apply (mul_le_mul_of_nonneg_left fit (show 0≤3*(stretch τ)^2 by positivity)).trans
  dsimp only [designWidth,CircleFiniteSchedule.designWidth]
  push_cast
  rw [sqrt_sq (by positivity),sqrt_sq (by positivity)]
  convert mul_le_mul_of_nonneg_right (Nat.le_ceil (300000000*(stretch τ)^2))
    (show 0≤(N:ℝ)^8 by positivity) using 1
  ring

/-- All later common steps work on one event at any width above both designs.
The two trajectories start at the same sampled initial parameters. -/
theorem paired_gd (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {τ σ η : ℝ}
    (hp : 0<τ) (order : τ<σ) (step : 0<η) (stable : η*(1+σ)≤2)
    (width : max (designWidth τ (n+1)) (designWidth σ (n+1)) ≤ m) :
    let N := n+1
    let δ := 1/(N:ℝ)
    let T := max (CirclePositiveWidth.cap τ N η δ δ) (CirclePositiveWidth.cap σ N η δ δ)
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ ≤ 2/(N:ℝ) ∧ ∀ z∈E, ∀ t ≥ T,
      rms τ η N z t ≤ 1/(N:ℝ)^3 ∧ rms σ η N z t ≤ 1/(N:ℝ)^3 ∧
      |(N:ℝ)^2*(learnerMean τ η N z t - learnerMean σ η N z t) -
        coefficient n τ σ * score N m z| ≤ 2/(N:ℝ) := by
  intro N δ T
  have pos : 0<(N:ℝ) := by dsimp [N]; positivity
  have d : 0<δ := one_div_pos.mpr pos
  have d1 : δ<1 := (div_lt_one pos).mpr (by exact_mod_cast (show 1<N by omega))
  have single (r : ℝ) (hr : 0<r) (st : η*(1+r)≤2) (size : designWidth r N ≤ m) :=
    CirclePositiveWidth.finite_width_after n m hn odd hr step st d d1 d
      ((design_bound n hn hr).trans (sqrt_le_sqrt (by exact_mod_cast size)))
  obtain ⟨A,mA,pA,a⟩ := single τ hp (by nlinarith [mul_lt_mul_of_pos_left order step])
    ((le_max_left ..).trans width)
  obtain ⟨B,mB,pB,b⟩ := single σ (hp.trans order) stable ((le_max_right ..).trans width)
  refine ⟨A ∩ B,mA.inter mB,?_,?_⟩
  · rw [Set.compl_inter]
    exact ((measureReal_union_le _ _).trans (add_le_add pA pB)).trans_eq (by dsimp [δ];ring)
  · intro z hz t after
    obtain ⟨fitA,errA⟩ := (a z hz.1).1 t ((le_max_left ..).trans after)
    obtain ⟨fitB,errB⟩ := (b z hz.2).1 t ((le_max_right ..).trans after)
    refine ⟨fitA,fitB,?_⟩
    let e r := learnerMean r η N z t - reference N m (weight r n) z
    have identity : (N:ℝ)^2*(learnerMean τ η N z t - learnerMean σ η N z t) -
        coefficient n τ σ * score N m z = (N:ℝ)^2*(e τ-e σ) := by
      simp only [e,coefficient,score,reference,N,Nat.cast_add,Nat.cast_one]
      ring
    rw [identity,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add errA errB))
      (sq_nonneg _)).trans_eq (by dsimp only [δ];field_simp;ring)

open CircleComparison

/-- RMS control of the scaled predictor at the common flow horizon.
In particular its error tends to zero in probability along growing odd grids. -/
theorem paired_flow (n : ℕ) (hn : 32≤n+1) (odd : Odd (n+1)) {τ σ : ℝ}
    (lo : 1/2≤τ) (order : τ<σ) (hi : σ≤2) (F : Benchmark n τ) (G : Benchmark n σ) :
    let N := n+1
    sqrt (∫ z, ((N:ℝ)^2*(trained n F z-trained n G z) -
      coefficient n τ σ * score N (N^32) z)^2 ∂seedLaw (N^32)) ≤ 2*oneRateConstant/sqrt N := by
  intro N
  apply (triangle n lo order hi F G).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add (one_rate_tracking n hn odd lo (order.le.trans hi) F)
    (one_rate_tracking n hn odd (lo.trans order.le) hi G)) (sq_nonneg _)).trans_eq
  simp only [N,Nat.cast_add,Nat.cast_one]
  have p : 0<(n:ℝ)+1 := by positivity
  field_simp
  ring
where
  triangle (n : ℕ) {τ σ : ℝ} (lo : 1/2≤τ) (order : τ<σ) (hi : σ≤2)
      (F : Benchmark n τ) (G : Benchmark n σ) :
      let N := n+1
      sqrt (∫ z, ((N:ℝ)^2*(trained n F z-trained n G z) -
        coefficient n τ σ * score N (N^32) z)^2 ∂seedLaw (N^32)) ≤
        (N:ℝ)^2*(discrepancyRms n F + discrepancyRms n G) := by
    intro N
    let μ := seedLaw (N^32)
    let u := trained n F - matched n τ
    let v := trained n G - matched n σ
    let a := (N:ℝ)^2
    have hF := CircleComparison.integrable_pair n (by linarith : 0<τ) (order.le.trans hi) F
    have hG := CircleComparison.integrable_pair n (by linarith : 0<σ) hi G
    have hu : MemLp u 2 μ := hF.1.sub hF.2
    have hv : MemLp v 2 μ := hG.1.sub hG.2
    have eq (z : Seed (N^32)) : a*(trained n F z-trained n G z)-coefficient n τ σ*score N (N^32) z =
        (a • (u-v)) z := by
      simp only [u,v,matched,a,coefficient,score,reference,N,Pi.sub_apply,Pi.smul_apply,
        smul_eq_mul,Nat.cast_add,Nat.cast_one]
      ring
    change sqrt (∫ z, (a*(trained n F z-trained n G z)-coefficient n τ σ*score N (N^32) z)^2 ∂μ) ≤ _
    simp_rw [eq]
    rw [CirclePairedCoefficient.rms_of_mem _ ((hu.sub hv).const_smul a), lpNorm_const_smul]
    change |a| *lpNorm (u-v) 2 μ ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    apply (mul_le_mul_of_nonneg_left (lpNorm_sub_le hu (by norm_num)) (sq_nonneg _)).trans
    rw [←CirclePairedCoefficient.rms_of_mem _ hu,←CirclePairedCoefficient.rms_of_mem _ hv]
    rfl

/-- At the larger sharp-tracking threshold the scaled paired RMS error is O(N⁻¹³)
for every choice of two rates in the compact interval. -/
theorem paired_flow_sharp (n : ℕ) (hn : 36864≤n+1) (odd : Odd (n+1)) {τ σ : ℝ}
    (lo : 1/2≤τ) (order : τ<σ) (hi : σ≤2) (F : Benchmark n τ) (G : Benchmark n σ) :
    let N := n+1
    sqrt (∫ z, ((N:ℝ)^2*(trained n F z-trained n G z) -
      coefficient n τ σ * score N (N^32) z)^2 ∂seedLaw (N^32)) ≤
        2*CircleSharpMoments.trackingConstant/(N:ℝ)^13 := by
  intro N
  apply (paired_flow.triangle n lo order hi F G).trans
  apply (mul_le_mul_of_nonneg_left (add_le_add
    (CircleSharpMoments.sharp_tracking n hn odd lo (order.le.trans hi) F)
    (CircleSharpMoments.sharp_tracking n hn odd (lo.trans order.le) hi G)) (sq_nonneg _)).trans_eq
  simp only [N,Nat.cast_add,Nat.cast_one]
  have p : 0<(n:ℝ)+1 := by positivity
  field_simp
  ring

open Set CircleFlowTracking CircleActualTracking CircleGaussianTracking CircleTangentDrift

/-- One measurable event fits both chosen rates, uniformly over compatible paths
and with polynomial exceptional probability of every fixed order. -/
theorem paired_flow_fit (n k : ℕ) (hN : 36864 ≤ n+1)
    (hk : k+17 ≤ n+1) (ho : Odd (n+1)) {r s : ℝ}
    (lo : 1/2≤r) (order : r<s) (hi : s≤2) :
    ∃ G : Set (State ((n+1)^32)), MeasurableSet G ∧
      (CircleEscapeBridge.seedLaw ((n+1)^32)).real Gᶜ ≤ 34/((n:ℝ)+1)^k ∧
      ∀ ω ∈ G, ∀ τ : ℝ, (τ = r ∨ τ = s) →
        ∀ z : ℝ → State ((n+1)^32), z 0 = ω →
          IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
            (CircleFlowTracking.horizon ((n:ℝ)+1)) z →
          ‖gridR (n+1) (z (CircleFlowTracking.horizon ((n:ℝ)+1)))‖ ≤ 1/((n:ℝ)+1)^3 ∧
          |CircleFlowMoments.mean (z (CircleFlowTracking.horizon ((n:ℝ)+1))) -
            CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) ω| ≤
            (1+176*π^2)/((n:ℝ)+1)^3 := by
  let μ := CircleEscapeBridge.seedLaw ((n+1)^32)
  let D := (n:ℝ)+1
  let I (τ : ℝ) := {ω : State ((n+1)^32) | ¬GoodInit τ (designRadius D) (designTolerance D)
    (CircleGridSpectrum.sampledMatrix τ) (fun _ : Fin (n+1) => CircleSpectrum.k0 τ) ω}
  obtain ⟨G₀,_,mass,inside⟩ := CircleSharpEvent.design_event (n+1) k hN hk (τ:=1) (by norm_num)
  let B := (G₀ᶜ ∪ I r) ∪ I s
  have h32 : 32 ≤ n+1 := by omega
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast h32
  have rp : 0 ≤ designRadius D := by dsimp [designRadius,D]; positivity
  have ri := (design_bounds d).1
  have tail (τ : ℝ) (hτ : |τ| ≤ 2) : μ.real (I τ) ≤ 10/D^k := by
    simpa only [I,D,μ,designTolerance,Nat.cast_add,Nat.cast_one] using
      CircleSharpEvent.initialization_power (n+1) k hN (by omega) hτ rp ri
  have m0 : μ.real G₀ᶜ ≤ 14/D^k := by simpa only [μ,D,Nat.cast_add,Nat.cast_one] using mass
  refine ⟨(toMeasurable μ B)ᶜ,(measurableSet_toMeasurable μ B).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ B)ᶜ)ᶜ ≤ 34/D^k
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    have h1 := (measureReal_union_le (μ:=μ) G₀ᶜ (I r)).trans
      (add_le_add m0 (tail r (by rw [abs_of_pos (by linarith : 0<r)]; linarith)))
    exact ((measureReal_union_le (μ:=μ) (G₀ᶜ ∪ I r) (I s)).trans
      (add_le_add h1 (tail s (by rw [abs_of_pos (by linarith : 0<s)]; exact hi)))).trans_eq (by ring)
  · intro ω hg τ allowed z start F
    have hb : ω ∉ B := fun h => hg (subset_toMeasurable μ B h)
    have h : ω ∈ G₀ ∧ ω ∉ I r ∧ ω ∉ I s := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not,and_assoc] using hb
    obtain ⟨nz,_,rd,_,_⟩ := inside ω h.1
    have hi : ω ∉ I τ := by
      rcases allowed with rfl|rfl
      · exact h.2.1
      · exact h.2.2
    have ok : GoodInit τ (designRadius D) (designTolerance D)
        (CircleGridSpectrum.sampledMatrix τ) (fun _ : Fin (n+1) => CircleSpectrum.k0 τ) ω :=
      not_not.mp hi
    have bounds : 1/2 ≤ τ ∧ τ ≤ 2 := by rcases allowed with rfl|rfl <;> constructor <;> linarith
    subst ω
    exact design_endpoint n h32 ho τ bounds.1 bounds.2 z F ok
      (by simpa only [gridR,CircleGaussianTracking.initialRms,Nat.cast_add,Nat.cast_one] using rd) nz

end CircleRateDial
