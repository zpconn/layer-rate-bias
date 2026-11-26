module

import all CircleSpectrum
public import CircleActualTracking
import all CircleActualTracking
public import CircleFlowConstruction
public import CircleFlowMoments
public import CircleFlowTracking
public import CircleTangentDrift
import all CircleFlowMoments
import all CircleFlowTracking
import all CircleTangentDrift
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-! Quantitative Gaussian moment transfer for the true weighted flow at the
odd-circle horizon and width N^32. Constants are independent of N and of the
chosen measurable solution. -/
@[expose] public section
noncomputable section
namespace CircleGaussianTracking
open CircleFlowPath CircleFlowMoments CircleFlowTracking CircleTangentDrift CircleEscapeBridge
open Real MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology NNReal
variable {N m : ℕ}

private theorem fourth_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (h : MemLp f 4 μ) : ∫ ω, f ω^4 ∂μ = (lpNorm f 4 μ)^4 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) h.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,Real.norm_eq_abs,(by decide : Even 4).pow_abs]
  simpa only [one_div] using (Real.rpow_inv_natCast_pow (integral_nonneg (μ:=μ) (show ∀ ω : Ω, 0 ≤ f ω^4 from fun ω => by positivity)) (by decide : 4 ≠ 0)).symm

private theorem square_mem {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (h : MemLp f 4 μ) : MemLp (fun ω => f ω^2) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num⟩
  simpa [Pi.mul_def,pow_two] using (h.mul h : MemLp _ 2 _)

/-- RMS norm of the initial grid residual in the same coordinates as the
dynamical contraction and fitting estimates. -/
def initialRms (N m : ℕ) (z : Seed m) :=
  ‖rmsCoordinates (residual (circleInput N) (circleLabel N) (1/sqrt m) z)‖

theorem initialRms_sq (N m : ℕ) (z : Seed m) :
    (initialRms N m z)^2 = 2*initialLoss N m z := by
  rw [initialRms,rmsCoordinates_norm_sq]
  unfold initialLoss loss
  ring

theorem initialRms_measurable (N m : ℕ) : Measurable (initialRms N m) := by
  have e : initialRms N m = fun ω => sqrt (2*initialLoss N m ω) := by
    funext ω
    rw [← initialRms_sq,Real.sqrt_sq (show 0 ≤ initialRms N m ω from norm_nonneg _)]
  rw [e]
  unfold initialLoss loss CircleFlowPath.residual output pre
  fun_prop

/-- On the full original Gaussian law, every positive threshold satisfies
the uniform eighth-power tail bound for the initial RMS residual. -/
theorem initialRms_tail (hN : 0 < N) (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    (seedLaw m).real {ω | a < initialRms N m ω} ≤ (2*lossConstant)^4/a^8 := by
  have h := initial_loss_fourth hN hm
  let L := initialLoss N m
  have hL : ∀ ω, 0 ≤ L ω := by intro ω; dsimp [L,initialLoss,loss]; positivity
  have h4 : Integrable (fun ω => L ω^4) (seedLaw m) := by
    have hf : MemLp L (4:ℕ) (seedLaw m) := h.1
    simpa [Real.norm_eq_abs,(by decide : Even 4).pow_abs] using hf.integrable_norm_pow'
  have bound := mul_meas_ge_le_integral_of_nonneg (f:=fun ω => L ω^4)
    (ae_of_all _ fun _ => by positivity) h4 ((a^2/2)^4)
  have sub : {ω | a < initialRms N m ω} ⊆ {ω | (a^2/2)^4 ≤ L ω^4} := by
    intro ω hω
    have hsq := pow_le_pow_left₀ ha.le (show a ≤ initialRms N m ω from le_of_lt hω) 2
    rw [initialRms_sq] at hsq
    change (a^2/2)^4 ≤ (L ω)^4
    have ht : a^2/2 ≤ L ω := by change _ ≤ initialLoss N m ω; linarith
    exact pow_le_pow_left₀ (by positivity) ht 4
  have le := (mul_le_mul_of_nonneg_left (measureReal_mono sub) (show 0 ≤ (a^2/2)^4 by positivity)).trans bound
  rw [fourth_integral h.1] at le
  have hh := le.trans (pow_le_pow_left₀ lpNorm_nonneg h.2 4)
  rw [le_div_iff₀ (by positivity)]
  nlinarith only [hh]

theorem initialRms_tail_tracking (hN : 0 < N) (hm : 0 < m) :
    (seedLaw m).real {ω | (N:ℝ)^2 < initialRms N m ω} ≤ (2*lossConstant)^4/(N:ℝ)^16 := by
  convert initialRms_tail hN hm (a:=(N:ℝ)^2) (by positivity) using 1
  ring

theorem initialRms_tail_fit (hN : 0 < N) (hm : 0 < m) :
    (seedLaw m).real {ω | 2*sqrt (12*(N:ℝ)) < initialRms N m ω} ≤
      (2*lossConstant)^4/(48*(N:ℝ))^4 := by
  convert initialRms_tail hN hm (a:=2*sqrt (12*(N:ℝ))) (by positivity) using 1
  have hh : (2*√(12*(N:ℝ)))^2 = 48*(N:ℝ) := by rw [mul_pow,sq_sqrt (by positivity)]; ring
  rw [show (2*√(12*(N:ℝ)))^8 = ((2*√(12*(N:ℝ)))^2)^4 by ring,hh]

/-- Coarse polynomial upper bound for this specific logarithmic horizon. -/
theorem horizon_le_cubic {n : ℝ} (hn : 1 ≤ n) : (horizon n : ℝ) ≤ 385*n^3 := by
  have hn' : 0 < n := by linarith
  have hsq : sqrt (12*n) ≤ 4*n := sqrt_le_iff.mpr ⟨by positivity,by nlinarith [mul_nonneg hn'.le (sub_nonneg.mpr hn)]⟩
  have hs : 1 ≤ sqrt (12*n) := le_sqrt_of_sq_le (by linarith)
  have n3 : 1 ≤ n^3 := one_le_pow₀ hn
  have sc : 1 ≤ 2*sqrt (12*n)*n^3 := by nlinarith [mul_le_mul hs n3 (by norm_num : (0:ℝ) ≤ 1) (sqrt_nonneg _)]
  have ub : 2*sqrt (12*n)*n^3 ≤ 8*n^4 := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hn'.le 3)]
  have hl := log_le_log (by positivity : 0 < 2*sqrt (12*n)*n^3) ub
  rw [log_mul (by norm_num : (8:ℝ) ≠ 0) (pow_ne_zero 4 hn'.ne'),log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hl' : log (2*sqrt (12*n)*n^3) ≤ 12*n := by linarith [log_le_sub_one_of_pos hn',log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 8)]
  have hlog := log_nonneg sc
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*π^2*n^2*log (2*sqrt (12*n)*n^3))).le
  change (⌈_⌉₊ : ℝ) ≤ _
  have hp : π^2 ≤ 16 := by nlinarith [Real.pi_lt_four,Real.pi_pos,sq_nonneg (4-π),mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (show 0 ≤ 4+π by positivity)]
  have h := mul_le_mul_of_nonneg_left hl' (show 0 ≤ 2*π^2*n^2 by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hp (pow_nonneg hn'.le 3)]

def horizonMomentConstant : ℝ := 7/2+84*gaussianSquareNorm+799*lossConstant

theorem horizon_fourth (hN : 0 < N) {τ b : ℝ} (hτ : 0 < τ) (hhi : τ ≤ 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (z : Seed (N^32) → ℝ → State (N^32))
    (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt (N^32:ℕ)) τ (horizon N) (z ω))
    (endpoint : Measurable fun ω => z ω (horizon N)) :
    let Y := fun ω => mean (z ω (horizon N)) - reference N (N^32) b ω
    MemLp Y 4 (seedLaw (N^32)) ∧ lpNorm Y 4 (seedLaw (N^32)) ≤ horizonMomentConstant*N*sqrt N := by
  have h := gaussian_flow_fourth_sharp hN (pow_pos hN 32) hτ hhi (Nat.cast_nonneg _) hb hb' z start flow endpoint
  refine ⟨h.1,h.2.trans ?_⟩
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hc := horizon_le_cubic hn
  have ns : 1 ≤ (N:ℝ)*sqrt N := one_le_mul_of_one_le_of_one_le hn (one_le_sqrt.mpr hn)
  have a : sqrt (2*(horizon N:ℝ)) ≤ 28*((N:ℝ)*sqrt N) := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [mul_pow,mul_pow,sq_sqrt hn'.le]
    nlinarith [pow_nonneg hn'.le 3]
  have mroot : sqrt ((N^32:ℕ):ℝ) = (N:ℝ)^16 := by
    rw [Nat.cast_pow,show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have nb : (N:ℝ)^3 ≤ (N:ℝ)^16 := pow_le_pow_right₀ hn (by norm_num)
  have b' : 2*(horizon N:ℝ)/sqrt ((N^32:ℕ):ℝ) ≤ 770 := by
    rw [mroot,div_le_iff₀ (by positivity)]
    linarith
  have lpos : 0 ≤ lossConstant := by unfold lossConstant; positivity
  have gpos : 0 ≤ gaussianSquareNorm := lpNorm_nonneg
  have mul1 := mul_le_mul_of_nonneg_right a gpos
  have mul2 := mul_le_mul_of_nonneg_right (show 1+sqrt (2*(horizon N:ℝ))+2*(horizon N:ℝ)/sqrt ((N^32:ℕ):ℝ) ≤
    799*((N:ℝ)*sqrt N) by linarith) lpos
  unfold horizonMomentConstant
  nlinarith


/-- The actual ceiling horizon retains its logarithmic time scale. -/
theorem horizon_log_upper {n : ℝ} (hn : 1 ≤ n) :
    (horizon n:ℝ) ≤ n^2*(1+128*log (8*n)) := by
  have hn' : 0 < n := by linarith
  have hsq : sqrt (12*n) ≤ 4*n := sqrt_le_iff.mpr ⟨by positivity,by nlinarith [mul_nonneg hn'.le (sub_nonneg.mpr hn)]⟩
  have hs : 1 ≤ sqrt (12*n) := le_sqrt_of_sq_le (by linarith)
  have n3 : 1 ≤ n^3 := one_le_pow₀ hn
  have sc : 1 ≤ 2*sqrt (12*n)*n^3 := by nlinarith [mul_le_mul hs n3 (by norm_num : (0:ℝ) ≤ 1) (sqrt_nonneg _)]
  have ub : 2*sqrt (12*n)*n^3 ≤ 8*n^4 := by
    nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hn'.le 3)]
  have hl := log_le_log (by positivity : 0 < 2*sqrt (12*n)*n^3) ub
  rw [log_mul (by norm_num : (8:ℝ) ≠ 0) (pow_ne_zero 4 hn'.ne'),log_pow] at hl
  have hl' : log (2*sqrt (12*n)*n^3) ≤ 4*log (8*n) := by
    rw [log_mul (by norm_num) hn'.ne']
    norm_num only [Nat.cast_ofNat] at hl
    linarith [log_nonneg (by norm_num : (1:ℝ) ≤ 8)]
  have hlog := log_nonneg sc
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2*π^2*n^2*log (2*sqrt (12*n)*n^3))).le
  change (⌈_⌉₊ : ℝ) ≤ _
  have hp : π^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (show 0 ≤ 4+π by positivity)]
  have h := mul_le_mul_of_nonneg_left hl' (show 0 ≤ 2*π^2*n^2 by positivity)
  have hl8 := log_nonneg (show 1 ≤ 8*n by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg n) hl8),one_le_pow₀ (n:=2) hn]

/-- At the specified width and physical horizon, the same-seed fourth norm
is bounded by a universal constant times N times the square root of log N. -/
theorem horizon_fourth_log {N : ℕ} (hN : 0 < N) {τ b : ℝ} (hτ : 0 < τ) (hhi : τ ≤ 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (z : Seed (N^32) → ℝ → State (N^32))
    (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt (N^32:ℕ)) τ (horizon N) (z ω))
    (endpoint : Measurable fun ω => z ω (horizon N)) :
    let Y := fun ω => mean (z ω (horizon N)) - reference N (N^32) b ω
    lpNorm Y 4 (seedLaw (N^32)) ≤
      (7/2+3*gaussianSquareNorm+772*lossConstant)*(N:ℝ)*sqrt (2+256*log (8*(N:ℝ))) := by
  have h := (gaussian_flow_fourth_sharp hN (pow_pos hN 32) hτ hhi (Nat.cast_nonneg _) hb hb' z start flow endpoint).2
  apply h.trans
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hn' : 0 < (N:ℝ) := by exact_mod_cast hN
  let a := sqrt (2+256*log (8*(N:ℝ)))
  have hl := log_nonneg (show 1 ≤ 8*(N:ℝ) by linarith)
  have hr : 0 ≤ 2+256*log (8*(N:ℝ)) := by linarith
  have h1 : 1 ≤ (N:ℝ)*a := one_le_mul_of_one_le_of_one_le hn (le_sqrt_of_sq_le (by linarith))
  have s : sqrt (2*(horizon N:ℝ)) ≤ (N:ℝ)*a := by
    apply sqrt_le_iff.mpr
    refine ⟨by dsimp [a]; positivity,?_⟩
    dsimp [a]
    rw [mul_pow,sq_sqrt hr]
    linarith only [horizon_log_upper hn]
  have mroot : sqrt ((N^32:ℕ):ℝ) = (N:ℝ)^16 := by
    rw [Nat.cast_pow,show (N:ℝ)^32=((N:ℝ)^16)^2 by ring,sqrt_sq (by positivity)]
  have nb : (N:ℝ)^3 ≤ (N:ℝ)^16 := pow_le_pow_right₀ hn (by norm_num)
  have b' : 2*(horizon N:ℝ)/sqrt ((N^32:ℕ):ℝ) ≤ 770 := by
    rw [mroot,div_le_iff₀ (by positivity)]
    linarith [horizon_le_cubic hn]
  have lpos : 0 ≤ lossConstant := by unfold lossConstant; positivity
  have gpos : 0 ≤ gaussianSquareNorm := lpNorm_nonneg
  have mul1 := mul_le_mul_of_nonneg_right s gpos
  have mul2 := mul_le_mul_of_nonneg_right (show 1+sqrt (2*(horizon N:ℝ))+2*(horizon N:ℝ)/sqrt ((N^32:ℕ):ℝ) ≤
    772*((N:ℝ)*a) by linarith) lpos
  change _ ≤ (7/2+3*gaussianSquareNorm+772*lossConstant)*(N:ℝ)*a
  nlinarith

/-- Quantitative all-seed integration. A path error B/N³ on a good event and
a Gaussian failure mass D/N¹⁶ suffice at the true evolving endpoint. -/
theorem all_seed_tracking (hN : 0 < N) {τ b B D : ℝ} (hτ : 0 < τ) (hhi : τ ≤ 2)
    (hb : 0 ≤ b) (hb' : b ≤ 1) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (z : Seed (N^32) → ℝ → State (N^32)) (start : ∀ ω, z ω 0 = ω)
    (flow : ∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt (N^32:ℕ)) τ (horizon N) (z ω))
    (endpoint : Measurable fun ω => z ω (horizon N)) (G : Set (Seed (N^32))) (meas : MeasurableSet G)
    (good : ∀ ω ∈ G, |mean (z ω (horizon N))-reference N (N^32) b ω| ≤ B/(N:ℝ)^3)
    (miss : (seedLaw (N^32)).real Gᶜ ≤ D/(N:ℝ)^16) :
    sqrt (∫ ω, (mean (z ω (horizon N))-reference N (N^32) b ω)^2 ∂seedLaw (N^32)) ≤
      (B+horizonMomentConstant*sqrt (sqrt D))/((N:ℝ)^2*sqrt N) := by
  let n := (N:ℝ)
  have hn : (1:ℝ) ≤ n := by dsimp [n]; exact_mod_cast hN
  have hn' : 0 < n := by linarith
  have sr : 0 < sqrt n := sqrt_pos.mpr hn'
  have h := horizon_fourth hN hτ hhi hb hb' z start flow endpoint
  let Y := fun ω => mean (z ω (horizon N))-reference N (N^32) b ω
  have hy : MemLp Y 4 (seedLaw (N^32)) := h.1
  have hnrm : lpNorm Y 4 (seedLaw (N^32)) ≤ horizonMomentConstant*n*sqrt n := h.2
  have hmpos : 0 ≤ horizonMomentConstant*n*sqrt n := lpNorm_nonneg.trans hnrm
  have fourth := (fourth_integral hy).le.trans (pow_le_pow_left₀ lpNorm_nonneg hnrm 4)
  have rms := all_seed_rms meas (square_mem hy) (show 0 ≤ B/n^3 by positivity)
    hmpos good miss fourth
  have quart : sqrt (sqrt (D/n^16)) = sqrt (sqrt D)/n^4 := by
    rw [show n^16=((n^4)^2)^2 by ring,sqrt_div hD,sqrt_sq (by positivity),
      sqrt_div (sqrt_nonneg _),sqrt_sq (by positivity)]
  change _ ≤ B/n^3+(horizonMomentConstant*n*sqrt n)*sqrt (sqrt (D/n^16)) at rms
  rw [quart] at rms
  apply rms.trans
  have bs : B*sqrt n ≤ B*n := mul_le_mul_of_nonneg_left (sqrt_le_iff.mpr ⟨hn'.le,by nlinarith [mul_nonneg hn'.le (sub_nonneg.mpr hn)]⟩) hB
  change B/n^3+(horizonMomentConstant*n*sqrt n)*(sqrt (sqrt D)/n^4) ≤
    (B+horizonMomentConstant*sqrt (sqrt D))/(n^2*sqrt n)
  calc
    _ = (B*sqrt n + horizonMomentConstant*sqrt (sqrt D)*n)/(n^3*sqrt n) := by
      field_simp
      linear_combination (horizonMomentConstant*sqrt (sqrt D)) * (Real.sq_sqrt hn'.le)
    _ ≤ (B*n+horizonMomentConstant*sqrt (sqrt D)*n)/(n^3*sqrt n) :=
      div_le_div_of_nonneg_right (add_le_add_left bs _) (by positivity)
    _ = _ := by field_simp

/-- The preceding explicit bound is little-o of N⁻² along every unbounded
design sequence, including the odd designs. -/
theorem tracking_littleO {ι : Type*} {l : Filter ι} {n : ι → ℕ} {err : ι → ℝ} {C : ℝ}
    (hn : Tendsto n l atTop) (nonneg : ∀ᶠ i in l, 0 ≤ err i)
    (bound : ∀ᶠ i in l, err i ≤ C/((n i:ℝ)^2*sqrt (n i))) :
    err =o[l] (fun i => 1/(n i:ℝ)^2) := by
  have h : Tendsto (fun i => (n i:ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hn
  have pos : ∀ᶠ i in l, 0 < (n i:ℝ) := h.eventually_gt_atTop 0
  apply isLittleO_of_tendsto' (pos.mono fun i hi hh => False.elim ((by positivity : (1:ℝ)/(n i:ℝ)^2 ≠ 0) hh))
  refine squeeze_zero' (g:=fun i => C*(sqrt (n i:ℝ))⁻¹) ?_ ?_ ?_
  · filter_upwards [nonneg,pos] with i he hi
    exact div_nonneg he (by positivity)
  · filter_upwards [bound,pos] with i hb hi
    calc
      err i/(1/(n i:ℝ)^2) ≤ (C/((n i:ℝ)^2*sqrt (n i)))/(1/(n i:ℝ)^2) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = C*(sqrt (n i:ℝ))⁻¹ := by field_simp
  · simpa using (tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp h)).const_mul C


open CircleInitializationConcentration

/-- Seed conditions of the two-rate actual tangent drift estimate. -/
def designGood (N : ℕ) (τ : ℝ) (ω : Seed (N^32)) :=
  GoodInit τ (32*π^2/(N:ℝ)^12) (1/(N:ℝ)^7) (populationGram N τ) (populationMeanRow N τ) ω

theorem designGood_failure (hN : 32 ≤ N) {τ : ℝ} (hτ : |τ| ≤ 2) :
    (seedLaw (N^32)).real {ω | ¬designGood N τ ω} ≤ 675/(N:ℝ)^16 := by
  have hn : (32:ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (1:ℝ) ≤ N := by linarith
  have hn' : 0 < (N:ℝ) := by linarith
  have hρ : 32*π^2/(N:ℝ)^12 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hn 12
    norm_num at h
    have hp : π^2 ≤ 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_lt_four.le) (show 0 ≤ 4+π by positivity)]
    linarith
  have h := goodInit_failure (m:=N^32) (N:=N) (pow_pos (by omega) _) hτ
    (show 0 ≤ 32*π^2/(N:ℝ)^12 by positivity) hρ (show 0 < 1/(N:ℝ)^7 by positivity)
    (show 1/(N:ℝ)^7 ≤ 1 from (div_le_one (by positivity)).mpr (one_le_pow₀ h1))
  refine h.trans ?_
  rw [Nat.cast_pow]
  have hb : ((N:ℝ)+1)^2+1 ≤ 5*(N:ℝ)^2 := by
    nlinarith [sq_nonneg ((N:ℝ)-1),sq_nonneg (N:ℝ),mul_nonneg (sub_nonneg.mpr h1) hn'.le]
  apply (mul_le_mul_of_nonneg_right hb (by positivity)).trans
  apply le_of_eq
  field_simp
  ring

def eventConstant : ℝ := 1350 + (2*lossConstant)^4

/-- A single measurable event for both actual rates and their common initial
residual radius. Its complement is taken under the original full Gaussian law. -/
theorem common_good_event (N : ℕ) (hN : 32 ≤ N) :
    ∃ G : Set (Seed (N^32)), MeasurableSet G ∧
      (∀ ω ∈ G, designGood N (1/2) ω ∧ designGood N 2 ω ∧ initialRms N (N^32) ω ≤ (N:ℝ)^2 ∧
        ∀ j, 0 < length ω j) ∧
      (seedLaw (N^32)).real Gᶜ ≤ eventConstant/(N:ℝ)^16 := by
  let μ := seedLaw (N^32)
  let S := {ω | ¬designGood N (1/2) ω}
  let F := {ω | ¬designGood N 2 ω}
  let R := {ω | (N:ℝ)^2 < initialRms N (N^32) ω}
  let Z := {ω : Seed (N^32) | ¬∀ j, 0 < length ω j}
  let D := ((S ∪ F) ∪ R) ∪ Z
  refine ⟨(toMeasurable μ D)ᶜ,(measurableSet_toMeasurable μ D).compl,?_,?_⟩
  · intro ω hω
    have hd : ω ∉ D := fun h => hω (subset_toMeasurable μ D h)
    simpa [D,S,F,R,Z,Set.mem_union,not_or,and_assoc] using hd
  · have h₁ : μ.real S ≤ 675/(N:ℝ)^16 := designGood_failure hN (by norm_num)
    have h₂ : μ.real F ≤ 675/(N:ℝ)^16 := designGood_failure hN (by norm_num)
    have h₃ : μ.real R ≤ (2*lossConstant)^4/(N:ℝ)^16 :=
      initialRms_tail_tracking (by omega) (pow_pos (by omega) _)
    change μ.real ((toMeasurable μ D)ᶜ)ᶜ ≤ _
    rw [compl_compl,measureReal_def,measure_toMeasurable,← measureReal_def]
    have u := (measureReal_union_le (μ:=μ) (S∪F) R).trans
      (add_le_add ((measureReal_union_le S F).trans (add_le_add h₁ h₂)) h₃)
    have hz : μ Z = 0 := ae_iff.mp (CircleInitializationConcentration.length_pos_ae (N^32))
    have hu := (measureReal_union_le (μ:=μ) ((S∪F)∪R) Z).trans (add_le_add_left u _)
    rw [measureReal_def μ Z,hz,ENNReal.toReal_zero,add_zero] at hu
    exact hu.trans_eq (by unfold eventConstant; ring)

/-- A Borel whole-trajectory solution supplies these seedwise hypotheses
simultaneously for every physical horizon. -/
theorem exists_actual_selector (N m : ℕ) (hN : 3 ≤ N) {τ : ℝ} (hτ : 0 < τ) (h2 : τ ≤ 2) :
    ∃ z : Seed m → ℝ → State m, (∀ ω, z ω 0 = ω) ∧
      ∀ T : ℝ, 0 ≤ T → (∀ ω, IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T (z ω)) ∧
        Measurable (fun ω => z ω T) := by
  let : MeasurableSpace C(ℝ≥0,State m) := borel _
  have : BorelSpace C(ℝ≥0,State m) := ⟨rfl⟩
  obtain ⟨f,hf,sol⟩ := CircleFlowConstruction.exists_borel_global_flow N m hN hτ h2
  refine ⟨fun ω => CircleInclusionExistence.realPath (f ω),?_,?_⟩
  · intro ω
    simpa [CircleInclusionExistence.realPath] using (sol ω).1
  · intro T hT
    refine ⟨fun ω => ((sol ω).2 T hT).1,?_⟩
    exact (continuous_eval_const (F:=C(ℝ≥0,State m)) (Real.toNNReal T)).measurable.comp hf


/-- The two prescribed learning-rate multipliers. -/
def benchmarkRate (fast : Bool) : ℝ := if fast then 2 else 1/2

private theorem rate_bounds (q : Bool) : 1/2 ≤ benchmarkRate q ∧ benchmarkRate q ≤ 2 := by
  cases q <;> norm_num [benchmarkRate]

private theorem weight_bounds (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ CircleSpectrum.weight τ n ∧ CircleSpectrum.weight τ n ≤ 1 := by
  refine ⟨?_,(le_abs_self _).trans (CircleActualTracking.weight_abs_le_one n τ hτ)⟩
  have hU : 0 ≤ CircleSpectrum.U τ n := by
    unfold CircleSpectrum.U CircleSpectrum.scaledU
    apply mul_nonneg (by unfold CircleSpectrum.rp; positivity)
    apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro j
    have hh := (CircleSpectrum.offset_bounds n j).1
    unfold CircleSpectrum.rp
    positivity
  have h0 : 0 < CircleSpectrum.k0 τ := by unfold CircleSpectrum.k0; positivity
  exact div_nonneg h0.le (add_nonneg h0.le hU)

def fitTolerance (N : ℕ) := 1/(N:ℝ)^3
def pathConstant := 1+176*π^2
def rmsConstant := pathConstant+horizonMomentConstant*sqrt (sqrt eventConstant)

abbrev Family (N : ℕ) := Bool → Seed (N^32) → ℝ → State (N^32)

/-- Endpoint comparison measured for the actual Gaussian seed and evaluated
at the physical horizon of the circle design. -/
def discrepancy (n : ℕ) (z : Family (n+1)) (q : Bool) (ω : Seed ((n+1)^32)) :=
  mean (z q ω (horizon (n+1))) -
    reference (n+1) ((n+1)^32) (CircleSpectrum.weight (benchmarkRate q) n) ω

def rmsError (n : ℕ) (z : Family (n+1)) (q : Bool) :=
  sqrt (∫ ω, (discrepancy n z q ω)^2 ∂seedLaw ((n+1)^32))

set_option maxHeartbeats 800000 in
/-- Conclusions hold for every choice of the two actual endpoint-measurable
flows on a shared seed. The good event is simultaneous across both rates. -/
theorem paired_actual_tracking (n : ℕ) (hN : 32 ≤ n+1) (ho : Odd (n+1)) (z : Family (n+1))
    (start : ∀ q ω, z q ω 0 = ω)
    (flow : ∀ q ω, IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32:ℕ):ℝ))
      (benchmarkRate q) (horizon (n+1)) (z q ω))
    (endpoint : ∀ q, Measurable fun ω => z q ω (horizon (n+1))) :
    (∃ G : Set (Seed ((n+1)^32)), MeasurableSet G ∧
      (seedLaw ((n+1)^32)).real Gᶜ ≤ eventConstant/((n:ℝ)+1)^16 ∧
      ∀ ω ∈ G, ∀ q, ‖CircleActualTracking.gridR (n+1) (z q ω (horizon (n+1)))‖ ≤ fitTolerance (n+1) ∧
        |discrepancy n z q ω| ≤ pathConstant/((n:ℝ)+1)^3) ∧
      ∀ q, rmsError n z q ≤ rmsConstant/(((n:ℝ)+1)^2*sqrt ((n:ℝ)+1)) := by
  obtain ⟨G,mg,good,miss⟩ := common_good_event (n+1) hN
  have hg (ω) (hω : ω ∈ G) (q : Bool) :
      ‖CircleActualTracking.gridR (n+1) (z q ω (horizon (n+1)))‖ ≤ fitTolerance (n+1) ∧
      |discrepancy n z q ω| ≤ pathConstant/((n:ℝ)+1)^3 := by
    obtain ⟨slow,fast,rr,nz⟩ := good ω hω
    have ig : designGood (n+1) (benchmarkRate q) ω := by cases q <;> assumption
    unfold designGood at ig
    rw [populationGram_sampled] at ig
    simp_rw [show populationMeanRow (n+1) (benchmarkRate q) =
       fun _ => CircleSpectrum.k0 (benchmarkRate q) from funext (populationMeanRow_constant _)] at ig
    have hi : ‖CircleActualTracking.gridR (n+1) (z q ω 0)‖ ≤ ((n:ℝ)+1)^2 := by
      rw [start]
      change initialRms (n+1) ((n+1)^32) ω ≤ _
      simpa only [Nat.cast_add,Nat.cast_one] using rr
    have zz := CircleActualTracking.design_endpoint n hN ho (benchmarkRate q) (rate_bounds q).1 (rate_bounds q).2
      (z q ω) (flow q ω) (by rw [start]; simpa [CircleActualTracking.designRadius,CircleActualTracking.designTolerance] using ig)
      hi (by rw [start]; exact nz)
    simpa [fitTolerance,discrepancy,pathConstant,start] using zz
  refine ⟨⟨G,mg,by simpa using miss,hg⟩,?_⟩
  intro q
  have hτ : 0 < benchmarkRate q := lt_of_lt_of_le (by norm_num) (rate_bounds q).1
  have wb := weight_bounds n hτ.le
  have rhs := all_seed_tracking (N:=n+1) (τ:=benchmarkRate q) (b:=CircleSpectrum.weight (benchmarkRate q) n) (B:=pathConstant) (D:=eventConstant) (Nat.succ_pos _) hτ (rate_bounds q).2 wb.1 wb.2
    (show 0 ≤ pathConstant by unfold pathConstant; positivity) (show 0 ≤ eventConstant by unfold eventConstant; positivity)
    (z q) (start q) (by simpa only [Nat.cast_add,Nat.cast_one] using (flow q)) (by simpa only [Nat.cast_add,Nat.cast_one] using (endpoint q)) G mg
    (by intro ω hω; simpa only [discrepancy,Nat.cast_add,Nat.cast_one] using (hg ω hω q).2) miss
  simpa only [rmsError,discrepancy,rmsConstant,Nat.cast_add,Nat.cast_one] using rhs

/-- Existence of the actual paired experiment and its fit and all-seed
tracking conclusions, with no assumed path or initialization event. -/
theorem exists_paired_actual_tracking (n : ℕ) (hN : 32 ≤ n+1) (ho : Odd (n+1)) :
    ∃ z : Family (n+1), (∀ q ω, z q ω 0 = ω) ∧
      (∀ q T, 0 ≤ T → (∀ ω, IsFlow (circleInput (n+1)) (circleLabel (n+1))
        (1/sqrt (((n+1)^32:ℕ):ℝ)) (benchmarkRate q) T (z q ω)) ∧ Measurable (fun ω => z q ω T)) ∧
      (∃ G : Set (Seed ((n+1)^32)), MeasurableSet G ∧
        (seedLaw ((n+1)^32)).real Gᶜ ≤ eventConstant/((n:ℝ)+1)^16 ∧
        ∀ ω ∈ G, ∀ q, ‖CircleActualTracking.gridR (n+1) (z q ω (horizon (n+1)))‖ ≤ fitTolerance (n+1) ∧
          |discrepancy n z q ω| ≤ pathConstant/((n:ℝ)+1)^3) ∧
      ∀ q, rmsError n z q ≤ rmsConstant/(((n:ℝ)+1)^2*sqrt ((n:ℝ)+1)) := by
  have ex (q : Bool) := exists_actual_selector (n+1) ((n+1)^32) (by omega) (τ:=benchmarkRate q)
      (by linarith [(rate_bounds q).1]) (rate_bounds q).2
  choose z start all using ex
  exact ⟨z,start,all,paired_actual_tracking n hN ho z start
    (fun q => (all q (horizon (n+1)) (Nat.cast_nonneg _)).1)
    (fun q => (all q (horizon (n+1)) (Nat.cast_nonneg _)).2)⟩


/-- Every sufficiently large odd design occurs in this enumeration exactly once. -/
def oddIndex (k : ℕ) := 2*(k+16)

/-- One sequence of paired actual global flows over every odd N≥33 has
unconditioned same-seed RMS tracking little-o of N⁻² at both rates. -/
theorem exists_odd_tracking_littleO :
    ∃ z : (k : ℕ) → Family (oddIndex k + 1),
      (∀ k q ω, z k q ω 0 = ω) ∧
      (∀ k q T, 0 ≤ T → (∀ ω, IsFlow (circleInput (oddIndex k+1)) (circleLabel (oddIndex k+1))
        (1/sqrt (((oddIndex k+1)^32:ℕ):ℝ)) (benchmarkRate q) T (z k q ω)) ∧ Measurable (fun ω => z k q ω T)) ∧
      ∀ q, (fun k => rmsError (oddIndex k) (z k) q) =o[atTop] (fun k => 1/((oddIndex k:ℝ)+1)^2) := by
  have ex (k : ℕ) := exists_paired_actual_tracking (oddIndex k) (by unfold oddIndex; omega) (⟨k+16,rfl⟩)
  choose z start flows events norms using ex
  refine ⟨z,start,flows,?_⟩
  intro q
  have diverge : Tendsto (fun k => oddIndex k + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => by dsimp [oddIndex]; omega) tendsto_id
  have est (k : ℕ) := norms k q
  have h := tracking_littleO (n:=fun k => oddIndex k + 1) (err:=fun k => rmsError (oddIndex k) (z k) q)
    (C:=rmsConstant) diverge (.of_forall fun k => sqrt_nonneg _) (.of_forall fun k => by simpa using est k)
  simpa using h

end CircleGaussianTracking
