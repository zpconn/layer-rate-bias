module

public import CirclePairedOrdering
import all CirclePairedOrdering
import all CirclePairedCoefficient
import all CircleGaussianTracking
import all CircleEscapeBridge
import all CircleComparison
import all CircleSpectrum
import Mathlib.Tactic

/-! The leading finite-grid correction in the population contrast is visible
even in the actual nonlinear flow. The Gaussian score norm at finite width
is recovered by polarizing the exact reference moments. -/
public section
noncomputable section
namespace CirclePairedSecondOrder
open MeasureTheory ProbabilityTheory Real Filter CirclePairedOrdering CirclePairedCoefficient
  CircleComparison CircleEscapeBridge CircleGaussianTracking CircleSharpMoments CircleSpectrum

theorem score_rms (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) :
    lpNorm (score (n+1) m) 2 (seedLaw m) = sqrt (1+c0+S n) := by
  let N := n+1
  let μ := seedLaw m
  let Z := reference N m
  have hZ (b : ℝ) := CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num)
  have moment (b : ℝ) : (∫ z, (Z b z)^2 ∂μ) = c0*(1-b)^2+b^2*S n+b^2 := by
    have h := CircleReferenceMoments.reference_moments n m hn ho hm b
    change (∫ z, reference (n+1) m b z^2 ∂seedLaw m)=_
    simpa only [sub_zero,h.1,h.2] using CircleStats.mse_decomposition (CircleSeedIntegrability.reference_memLp (n+1) m b 2 (by norm_num)) 0
  have point (z : Seed m) : score N m z^2=2*Z 0 z^2+2*Z 1 z^2-4*Z (1/2) z^2 := by
    dsimp only [Z,score,reference]; ring
  rw [←rms_of_mem μ (score_bound (m:=m) hn hm).1]
  change sqrt (∫ z, score N m z^2 ∂μ)=_
  simp_rw [point]
  have hadd : Integrable (fun z => 2*Z 0 z^2+2*Z 1 z^2) μ := ((hZ 0).integrable_sq.const_mul 2).add ((hZ 1).integrable_sq.const_mul 2)
  rw [integral_sub hadd
    ((hZ (1/2)).integrable_sq.const_mul 4),integral_add ((hZ 0).integrable_sq.const_mul 2)
    ((hZ 1).integrable_sq.const_mul 2)]
  simp only [integral_const_mul]
  congr 1
  change 2*(∫ z, Z 0 z^2 ∂μ)+2*(∫ z, Z 1 z^2 ∂μ)-4*(∫ z, Z (1/2) z^2 ∂μ)=_
  rw [moment,moment,moment]; ring

private theorem reverse_norm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {a b : Ω → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    |lpNorm a 2 μ-lpNorm b 2 μ| ≤ lpNorm (a-b) 2 μ := by
  have h := lpNorm_add_le (ha.sub hb) (g:=b) (by norm_num)
  rw [sub_add_cancel] at h
  have g := lpNorm_sub_le ha (g:=a-b) (by norm_num)
  rw [sub_sub_cancel] at g
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem error (n : ℕ) (hn : 36864≤n+1) (ho : Odd (n+1)) (F : ∀ q, Benchmark n (benchmarkRate q)) :
    |sqrt (∫ z, pairedError n (paths n F) z^2 ∂seedLaw ((n+1)^32)) -
      |coefficient n-π^2/40| * sqrt (1+c0+S n)| ≤ 2*trackingConstant/((n:ℝ)+1)^13 := by
  let μ := seedLaw ((n+1)^32)
  let X := score (n+1) ((n+1)^32)
  let B := (coefficient n-π^2/40) • X
  let E := pairedError n (paths n F)
  let A := fun z => difference n (paths n F) z-coefficient n*X z
  have hx := (score_bound (m:=(n+1)^32) (by omega : 3≤n+1) (by positivity)).1
  have hb : MemLp B 2 μ := hx.const_smul _
  have ha : MemLp A 2 μ := by
    have hf (q : Bool) := discrepancy_mem n (paths n F) q (F q).start ((F q).flow _ (Nat.cast_nonneg _))
      ((F q).endpoint _ (Nat.cast_nonneg _))
    have eq : A = ((n:ℝ)+1)^2 • (discrepancy n (paths n F) false-discrepancy n (paths n F) true) := by
      funext z; exact CirclePairedOrdering.identity n _ _
    rw [eq]; exact ((hf false).sub (hf true)).const_smul _
  have eq : E-B=A := by
    funext z
    dsimp only [E,B,A,pairedError,difference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,X]
    ring
  have he : MemLp E 2 μ := by
    rw [←sub_add_cancel E B,eq];exact ha.add hb
  have bound := actual_scaled_rms n hn ho F
  change sqrt (∫ z, A z^2 ∂μ) ≤ _ at bound
  rw [rms_of_mem μ ha] at bound
  have rev := reverse_norm μ he hb
  rw [eq] at rev
  change |sqrt (∫ z, E z^2 ∂μ)-_| ≤ _
  rw [rms_of_mem μ he]
  have bnorm : lpNorm B 2 μ = |coefficient n-π^2/40| * sqrt (1+c0+S n) := by
    dsimp only [B]
    rw [lpNorm_const_smul,coe_nnnorm,Real.norm_eq_abs]
    exact congrArg _ (score_rms n _ (by omega) ho (by positivity))
  rw [←bnorm]
  exact rev.trans bound

open scoped Topology
/-- Exact leading nonzero RMS constant when the limiting coefficient π²/40
is used in place of the finite-grid coefficient in the paired prediction. -/
theorem leading_rms (n : ℕ → ℕ) (grow : Tendsto n atTop atTop)
    (hn : ∀ i, 36864≤n i+1) (ho : ∀ i, Odd (n i+1)) (F : ∀ i q, Benchmark (n i) (benchmarkRate q)) :
    Tendsto (fun i => ((n i:ℝ)+1)^2*sqrt (∫ z, pairedError (n i) (paths (n i) (F i)) z^2
      ∂seedLaw ((n i+1)^32))) atTop (𝓝 (π^4/1600*sqrt (1+2/π^2))) := by
  let x (i : ℕ) := (n i:ℝ)+1
  have xp (i : ℕ) : 0<x i := by dsimp [x]; positivity
  have xgrow := CircleComparison.grown n grow
  have limits := CircleFiniteCoefficient.coefficient_second_order.comp grow
  have s0 : Tendsto (fun i => S (n i)) atTop (𝓝 0) := by
    have d₀ : Tendsto (CircleSpectrum.rp 4) atTop (𝓝 0) := by
      change Tendsto (fun j : ℕ => 1/((j:ℝ)+1)^4) atTop (𝓝 0)
      simpa [div_pow] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).pow 4
    have d := d₀.comp grow
    simpa only [S,Function.comp_def,zero_mul] using d.mul (scaledS_limit.comp grow)
  have lhs : Tendsto (fun i => |x i^2*(coefficient (n i)-π^2/40)| * sqrt (1+c0+S (n i)))
      atTop (𝓝 (π^4/1600*sqrt (1+2/π^2))) := by
    have h := limits.abs.mul ((tendsto_const_nhds (x:=1+c0) (f:=atTop)).add s0).sqrt
    simpa only [Function.comp_def,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤π^4),
      abs_of_nonneg (by norm_num : (0:ℝ)≤1600),add_zero,c0,coefficient,x] using h
  have small : Tendsto (fun i => 2*trackingConstant/(x i)^11) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by decide : 11≠0)).comp xgrow)
  apply lhs.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) (g:=_) _ small
  intro i
  rw [Real.dist_eq,abs_mul,abs_of_nonneg (sq_nonneg (x i))]
  have h := mul_le_mul_of_nonneg_left (error (n i) (hn i) (ho i) (F i)) (sq_nonneg (x i))
  change _ ≤ 2*trackingConstant/(x i)^11
  nth_rw 1 [←abs_of_nonneg (sq_nonneg (x i))] at h
  rw [←abs_mul] at h
  rw [abs_sub_comm]
  convert h.trans_eq (show (x i)^2*(2*trackingConstant/(x i)^13)=2*trackingConstant/(x i)^11 by field_simp [ne_of_gt (xp i)]) using 1
  dsimp only [x]
  congr 1;ring

end CirclePairedSecondOrder
