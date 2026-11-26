module
public import CirclePairedOrdering
public import CircleMarginMass
public import CircleCoefficientRemainder
public import CirclePairedSecondOrder
import all CirclePairedOrdering
import all CirclePairedCoefficient
import all CircleComparison
import all CircleGaussianTracking
import all CircleSharpTracking
import all CircleMarginMass
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-! Simultaneous finite-design conclusions for the two actual same-seed circle flows. -/
@[expose] public section
noncomputable section
namespace CirclePairedTheorem
open Real Filter Topology Set MeasureTheory ProbabilityTheory CircleComparison CircleGaussianTracking
  CirclePairedOrdering CirclePairedCoefficient CircleFlowTracking CircleEscapeBridge CircleActualTracking
  CircleSharpTracking CircleMarginMass

abbrev Width (n : ℕ) := (n+1)^32
abbrev Rates (n : ℕ) := ∀ q, Benchmark n (benchmarkRate q)

def errorCap (n : ℕ) := (2*confidenceConstant 158)*(1+log ((n:ℝ)+1))/((n:ℝ)+1)^13

def margin (n : ℕ) (γ : ℝ) : Set (Seed (Width n)) := {z | γ ≤ |score (n+1) (Width n) z|}

/-- The same seed fits each training grid, the two prediction vectors agree in
grid RMS, and their signed population-mean difference tracks the initial score. -/
structure PairedBounds (n : ℕ) (F : Rates n) (z : Seed (Width n)) : Prop where
  fit : ∀ q, ‖gridR (n+1) ((F q).path z (horizon ((n:ℝ)+1)))‖ ≤ 1/((n:ℝ)+1)^3
  grid_disagreement :
    ‖gridR (n+1) ((F false).path z (horizon ((n:ℝ)+1))) -
     gridR (n+1) ((F true).path z (horizon ((n:ℝ)+1)))‖ ≤ 2/((n:ℝ)+1)^3
  paired_error :
    |difference n (paths n F) z - coefficient n * score (n+1) (Width n) z| ≤ errorCap n

/-- A single Borel set certifies all three conclusions with explicit constants. -/
theorem common_event (n : ℕ) (hn : 36864≤n+1) (ho : Odd (n+1)) (F : Rates n) :
    ∃ E : Set (Seed (Width n)), MeasurableSet E ∧
      (seedLaw (Width n)).real Eᶜ ≤ 96/((n:ℝ)+1)^158 ∧ ∀ z∈E, PairedBounds n F z := by
  obtain ⟨A,ma,pa,track⟩ := paired_likely_cap n 158 hn (by omega) ho F
  obtain ⟨B,mb,pb,fit⟩ := joint_fit_original_horizon n 158 hn (by omega) ho
  refine ⟨A∩B,ma.inter mb,?_,?_⟩
  · rw [compl_inter]
    exact (measureReal_union_le _ _).trans ((add_le_add pa pb).trans_eq (by ring))
  · intro z hz
    have f (q : Bool) := (fit z hz.2 _ (show benchmarkRate q=1/2 ∨ benchmarkRate q=1 ∨ benchmarkRate q=2 by
      cases q <;> norm_num [benchmarkRate]) ((F q).path z) ((F q).start z) ((F q).flow _ (Nat.cast_nonneg _) z)).1
    refine ⟨f,(norm_sub_le _ _).trans ((add_le_add (f false) (f true)).trans_eq (by ring)),?_⟩
    rw [identity,abs_mul,abs_of_nonneg (sq_nonneg _)]
    have b := endpointCap_le (n+1) 158 (by omega)
    push_cast at b
    have le := (abs_sub _ _).trans (add_le_add ((track z hz.1 false).trans b) ((track z hz.1 true).trans b))
    apply (mul_le_mul_of_nonneg_left le (sq_nonneg ((n:ℝ)+1))).trans_eq
    unfold errorCap
    field_simp; ring

/-- On the prescribed score margin, an error smaller than half the predicted
separation gives strict ordering and a lower bound on the unscaled means. -/
theorem PairedBounds.separates {n : ℕ} {F : Rates n} {z : Seed (Width n)} (h : PairedBounds n F z)
    {γ : ℝ} (hγ : 0<γ) (small : errorCap n ≤ coefficient n*γ/2) (hm : z∈margin n γ) :
    0 < difference n (paths n F) z * score (n+1) (Width n) z ∧
    coefficient n*γ/(2*((n:ℝ)+1)^2) ≤ |endpoint n (paths n F) false z-endpoint n (paths n F) true z| := by
  let D := difference n (paths n F) z
  let X := score (n+1) (Width n) z
  let c := coefficient n
  have hc : 0<c := coefficient_pos _
  have mg : γ≤|X| := hm
  have cg : 0<c*γ := mul_pos hc hγ
  have e : |D-c*X|≤c*γ/2 := h.paired_error.trans small
  constructor
  · by_contra! w
    have w' : c*|X|≤|D-c*X| := wrong_forces_error hc w
    linarith [mul_le_mul_of_nonneg_left mg hc.le]
  · have tri := abs_add_le (c*X-D) D
    rw [sub_add_cancel,abs_mul,abs_of_pos hc,abs_sub_comm (c*X) D] at tri
    have d : c*γ/2≤|D| := by linarith [mul_le_mul_of_nonneg_left mg hc.le]
    change c*γ/2 ≤ |((n:ℝ)+1)^2*(_-_)| at d
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)] at d
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [d]

/-- A fixed upper score bound also bounds the same population separation above. -/
theorem PairedBounds.band_upper {n : ℕ} {F : Rates n} {z : Seed (Width n)} (h : PairedBounds n F z)
    {γ B : ℝ} (small : errorCap n ≤ coefficient n*γ/2) (upper : |score (n+1) (Width n) z|≤B) :
    |endpoint n (paths n F) false z-endpoint n (paths n F) true z| ≤
      coefficient n*(B+γ/2)/((n:ℝ)+1)^2 := by
  let D := difference n (paths n F) z
  let X := score (n+1) (Width n) z
  let c := coefficient n
  have tri := abs_add_le (D-c*X) (c*X)
  rw [sub_add_cancel,abs_mul,abs_of_pos (coefficient_pos n)] at tri
  have e : |D-c*X| ≤ c*γ/2 := h.paired_error.trans small
  have up : |D|≤c*(B+γ/2) := by linarith [mul_le_mul_of_nonneg_left upper (coefficient_pos n).le]
  change |((n:ℝ)+1)^2*(_-_)| ≤ _ at up
  rw [abs_mul,abs_of_nonneg (sq_nonneg _),mul_comm] at up
  exact (le_div_iff₀ (by positivity)).2 up

private theorem cap_small {γ : ℝ} (hg : 0<γ) :
    ∀ᶠ n : ℕ in atTop, errorCap n ≤ coefficient n*γ/2 := by
  let C := |2*confidenceConstant 158|
  have grow : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have lim : Tendsto (fun n : ℕ => C/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp grow).const_mul C
  have s := lim.eventually (eventually_le_nhds (show (0:ℝ)<(π^2/80)*γ/2 by positivity))
  filter_upwards [s,coefficient_eventually] with n hn hc
  apply le_trans _ (hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hg.le) (by norm_num)))
  let x := (n:ℝ)+1
  have x1 : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have xp : 0<x := zero_lt_one.trans_le x1
  have logb : 1+log x≤x := by linarith [log_le_sub_one_of_pos xp]
  change (2*confidenceConstant 158)*(1+log x)/x^13≤C/x
  rw [div_le_div_iff₀ (by positivity) xp]
  calc
    _ ≤ (C*x)*x := mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) logb
      (by linarith [log_nonneg x1]) (abs_nonneg _)) xp.le
    _ ≤ _ := by
      rw [mul_assoc,←sq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ x1 (by norm_num : 2≤13)) (abs_nonneg _)

private theorem margin_meas (n : ℕ) (γ : ℝ) : MeasurableSet (margin n γ) :=
  measurableSet_le measurable_const (continuous_abs.measurable.comp (score_measurable _ _))

private theorem conditional_good {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A E : Set Ω} (ma : MeasurableSet A) (me : MeasurableSet E) {p e : ℝ}
    (hp : 0<p) (ha : p≤μ.real A) (he : μ.real Eᶜ≤e) :
    1-e/p ≤ (cond μ A).real E := by
  have a0 : 0<μ.real A := hp.trans_le ha
  have an : μ A≠0 := (ENNReal.toReal_pos_iff.mp a0).1.ne'
  let := cond_isProbabilityMeasure (μ:=μ) an
  have hb : (cond μ A).real Eᶜ ≤ e/p := by
    rw [measureReal_def,cond_apply ma,ENNReal.toReal_mul,ENNReal.toReal_inv,←measureReal_def,←measureReal_def]
    rw [←div_eq_inv_mul]
    exact div_le_div₀ (measureReal_nonneg.trans he) ((measureReal_mono inter_subset_right).trans he) hp ha
  rw [probReal_compl_eq_one_sub me] at hb
  linarith

/-- At every fixed positive margin, the same Borel event has conditional mass
at least 1−96/(pγ N¹⁵⁸), where pγ is an explicit positive Gaussian tail.
Every seed of the event in that margin has both grid conclusions, the stated
scaled error, strict ordering, and population-mean separation. -/
theorem fixed_margin_complete {γ : ℝ} (hg : 0<γ) :
    0<marginFloor γ ∧ ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : Rates n,
      marginFloor γ ≤ (seedLaw (Width n)).real (margin n γ) ∧
      ∃ E : Set (Seed (Width n)), MeasurableSet E ∧
        (seedLaw (Width n)).real Eᶜ ≤ 96/((n:ℝ)+1)^158 ∧
        1-96/(marginFloor γ*((n:ℝ)+1)^158) ≤ (cond (seedLaw (Width n)) (margin n γ)).real E ∧
        (∀ z∈E, PairedBounds n F z) ∧
        ∀ z∈E, z∈margin n γ →
          0<difference n (paths n F) z * score (n+1) (Width n) z ∧
          coefficient n*γ/(2*((n:ℝ)+1)^2) ≤
            |endpoint n (paths n F) false z-endpoint n (paths n F) true z| := by
  refine ⟨marginFloor_pos _,?_⟩
  filter_upwards [cap_small hg,schedule_mass hg.le,eventually_ge_atTop 36864] with n small mass hn ho F
  obtain ⟨E,me,prob,inside⟩ := common_event n (by omega) ho F
  refine ⟨mass ho,E,me,prob,?_,inside,fun z hz hm => (inside z hz).separates hg small hm⟩
  have h := conditional_good (seedLaw (Width n)) (margin_meas n γ) me (marginFloor_pos _) (mass ho) prob
  have swap (p x : ℝ) : 96/(p*x)=(96/x)/p := by ring
  rw [swap]
  exact h
/-- The normalized conditional probability applies to the actual claims about
the trained pair, on a measurable subevent contained in the prescribed margin. -/
theorem conditional_success {γ : ℝ} (hg : 0<γ) :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : Rates n,
      ∃ E : Set (Seed (Width n)), MeasurableSet E ∧ E ⊆ margin n γ ∧
      1-96/(marginFloor γ*((n:ℝ)+1)^158) ≤ (cond (seedLaw (Width n)) (margin n γ)).real E ∧
      ∀ z∈E, PairedBounds n F z ∧ 0<difference n (paths n F) z*score (n+1) (Width n) z ∧
        coefficient n*γ/(2*((n:ℝ)+1)^2) ≤ |endpoint n (paths n F) false z-endpoint n (paths n F) true z| := by
  filter_upwards [(fixed_margin_complete hg).2] with n h ho F
  obtain ⟨_,E,me,_,mass,inside,sep⟩ := h ho F
  let M := margin n γ
  let μ := seedLaw (Width n)
  have mm : MeasurableSet M := margin_meas n γ
  have same : (cond μ M).real (M∩E) = (cond μ M).real E := by
    rw [measureReal_def,measureReal_def,cond_apply mm,cond_apply mm]
    simp [←Set.inter_assoc]
  exact ⟨M∩E,mm.inter me,inter_subset_left,same.symm ▸ mass,fun z hz => ⟨inside z hz.2,sep z hz.2 hz.1⟩⟩

/-- On a fixed score band, the same event bounds the absolute population
difference above and below by explicit positive multiples of N⁻². -/
theorem fixed_band {γ B : ℝ} (hg : 0<γ) (hB : γ≤B) :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : Rates n,
      ∃ E : Set (Seed (Width n)), MeasurableSet E ∧ (seedLaw (Width n)).real Eᶜ≤96/((n:ℝ)+1)^158 ∧
        (∀ z∈E, PairedBounds n F z) ∧
        ∀ z∈E, z∈margin n γ → |score (n+1) (Width n) z|≤B →
          |endpoint n (paths n F) false z-endpoint n (paths n F) true z| ∈
            Icc ((π^2/160)*γ/((n:ℝ)+1)^2) ((π^2/20)*(B+γ/2)/((n:ℝ)+1)^2) := by
  have top := CircleLayerRates.coefficient_limit.eventually (eventually_le_nhds
    (show π^2/40<π^2/20 by nlinarith [sq_pos_of_pos pi_pos]))
  filter_upwards [cap_small hg,coefficient_eventually,top,eventually_ge_atTop 36864] with n small lo hi hn ho F
  obtain ⟨E,me,prob,inside⟩ := common_event n (by omega) ho F
  refine ⟨E,me,prob,inside,?_⟩
  intro z hz hm hb
  have f := inside z hz
  constructor
  · apply le_trans _ (f.separates hg small hm).2
    rw [show coefficient n*γ/(2*((n:ℝ)+1)^2)=(coefficient n*γ/2)/((n:ℝ)+1)^2 by field_simp]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith only [mul_le_mul_of_nonneg_right lo hg.le]
  · apply (f.band_upper small hb).trans
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hi (by linarith)) (sq_nonneg _)

/-- The all-seed conclusions accompanying the high-probability event. Ties
are included in the miss probability. All constants apply to every Borel choice. -/
theorem all_seed_bounds :
    ∀ᶠ n : ℕ in atTop, ∀ _ho : Odd (n+1), ∀ F : Rates n,
      0<coefficient n ∧
      |coefficient n-(π^2/40-π^4/(1600*((n:ℝ)+1)^2))|≤400/((n:ℝ)+1)^4 ∧
      sqrt (∫ z, (difference n (paths n F) z-coefficient n*score (n+1) (Width n) z)^2 ∂seedLaw (Width n))
        ≤ 2*CircleSharpMoments.trackingConstant/((n:ℝ)+1)^13 ∧
      (seedLaw (Width n)).real (miss n (paths n F)) ≤ (28+8*angularConstant/(π^2/80))/((n:ℝ)+1)^13 := by
  filter_upwards [eventually_ge_atTop 36864,actual_wrong_eventually] with n hn missb ho F
  exact ⟨coefficient_pos _,CircleCoefficientRemainder.uniform_remainder n,actual_scaled_rms n (by omega) ho F,missb ho F⟩

/-- Replacing the exact slope by its limiting value still predicts the trained
difference in RMS along every growing sequence of odd grids and selected flows. -/
theorem limiting_prediction (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 36864≤n i+1) (ho : ∀ i, Odd (n i+1)) (F : ∀ i, Rates (n i)) :
    Tendsto (fun i => sqrt (∫ z, pairedError (n i) (paths (n i) (F i)) z^2 ∂seedLaw (Width (n i)))) atTop (𝓝 0) := by
  have lead := CirclePairedSecondOrder.leading_rms n grow hn ho F
  have inv := (tendsto_inv_atTop_zero.comp (CircleComparison.grown n grow)).pow 2
  have mul := lead.mul inv
  simp only [zero_pow (by norm_num : 2≠0),mul_zero] at mul
  apply mul.congr (fun i => ?_)
  change ((n i:ℝ)+1)^2*_ * (((n i:ℝ)+1)⁻¹)^2 = _
  field_simp

/-- The expected unscaled difference between the two trained population means
tracks the exact finite-grid coefficient divided by the squared grid size. -/
theorem signed_mean_finite (n : ℕ) (hn : 36864 ≤ n+1) (ho : Odd (n+1)) (F : Rates n) :
    |(∫ z, trained n (F false) z - trained n (F true) z ∂seedLaw (Width n)) -
      coefficient n / ((n:ℝ)+1)^2| ≤ 2*CircleSharpMoments.trackingConstant / ((n:ℝ)+1)^15 := by
  let μ := seedLaw (Width n)
  let N := (n:ℝ)+1
  have hN : N ≠ 0 := by dsimp [N]; positivity
  have rates (q : Bool) : 1/2 ≤ benchmarkRate q ∧ benchmarkRate q ≤ 2 := by
    cases q <;> norm_num [benchmarkRate]
  have pair (q : Bool) := CircleComparison.integrable_pair n
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (rates q).1) (rates q).2 (F q)
  have one (q : Bool) : |(∫ z, trained n (F q) z ∂μ) - CircleSpectrum.weight (benchmarkRate q) n| ≤
      CircleSharpMoments.trackingConstant/N^15 := by
    have refMean := (CircleReferenceMoments.weighted_reference_moments n (Width n)
      (by omega) ho (pow_pos (Nat.succ_pos n) _) (benchmarkRate q)).1
    change (∫ z, matched n (benchmarkRate q) z ∂μ) = _ at refMean
    rw [← refMean]
    exact (CircleComparison.mean_transfer (pair q).1 (pair q).2).trans
      (CircleSharpMoments.sharp_tracking n hn ho (rates q).1 (rates q).2 (F q))
  rw [integral_sub ((pair false).1.integrable (by norm_num)) ((pair true).1.integrable (by norm_num))]
  have coeff : coefficient n / N^2 = CircleSpectrum.weight (benchmarkRate false) n -
      CircleSpectrum.weight (benchmarkRate true) n := by
    change (N^2 * _) / N^2 = _
    field_simp [hN]
    rfl
  change |((_ : ℝ)-_) - coefficient n / N^2| ≤ 2*CircleSharpMoments.trackingConstant/N^15
  rw [coeff,show ∀ a b c d : ℝ, (a-b)-(c-d)=(a-c)-(b-d) by intros; ring]
  exact (abs_sub _ _).trans ((add_le_add (one false) (one true)).trans_eq (by ring))

/-- The signed expected shift has leading term π²/(40N²) and second term
−π⁴/(1600N⁴), uniformly over measurable selections of the two flows. -/
theorem signed_mean_expansion (n : ℕ) (hn : 36864 ≤ n+1) (ho : Odd (n+1)) (F : Rates n) :
    let N := (n:ℝ)+1
    |(∫ z, trained n (F false) z - trained n (F true) z ∂seedLaw (Width n)) -
      (π^2/(40*N^2)-π^4/(1600*N^4))| ≤
      2*CircleSharpMoments.trackingConstant/N^15 + 400/N^6 := by
  intro N
  have hN : 0 < N := by dsimp [N]; positivity
  have coeff := div_le_div_of_nonneg_right (CircleCoefficientRemainder.uniform_remainder n)
    (sq_nonneg N)
  change |coefficient n - (π^2/40-π^4/(1600*N^2))| / N^2 ≤ 400/N^4/N^2 at coeff
  have bound : |(coefficient n-(π^2/40-π^4/(1600*N^2)))/N^2| ≤ 400/N^6 := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hN)]
    exact coeff.trans_eq (by ring)
  let M := ∫ z, trained n (F false) z - trained n (F true) z ∂seedLaw (Width n)
  calc
    |M-(π^2/(40*N^2)-π^4/(1600*N^4))| =
      |(M-coefficient n/N^2)+(coefficient n-(π^2/40-π^4/(1600*N^2)))/N^2| := by
        congr 1
        field_simp
        ring
    _ ≤ _ := (abs_add_le ..).trans (add_le_add (signed_mean_finite n hn ho F)
      bound)

end CirclePairedTheorem
