module

public import CircleWidthPublished
public import CircleSharpTracking
public import CircleInitialResidualSecond
import all CircleFlowMoments
import all CircleFlowPath
import all CircleSharpTracking
import all CircleActualTracking
import all CircleTangentDrift
import all CircleSpectralPathLength
import all CircleGaussianTracking
import all CirclePairedCoefficient
import all CircleEscapeBridge
import all CircleSeedIntegrability
import all CircleInitialResidualSecond
import all CircleKernelGD
import Mathlib.Tactic

/-! Unconditional tracking at arbitrary widths and physical times. The comparison
uses a kernel reference evaluated on exactly the same initial draw as the flow. -/
@[expose] public section
noncomputable section
namespace CircleVariableFlow
open Real MeasureTheory Set Filter CircleFlowPath CircleFlowMoments CircleTangentDrift
 CircleActualTracking CircleSpectralPathLength CircleEscapeBridge CircleGridSpectrum CircleGaussianTracking
 CircleSharpTracking

private def b (n : ℕ) := CircleSpectrum.weight 1 n
private def multiplier (n : ℕ) (T : ℝ) := exp (-(CircleKernelGD.gamma (n+1)*T))
private def stopped (n : ℕ) (T : ℝ) := b n*(1-multiplier n T)

private theorem stopped_ref (n m : ℕ) (hn : 3≤n+1) (T : ℝ) (z : Seed m) :
    reference (n+1) m (stopped n T) z = reference (n+1) m (b n) z+
      multiplier n T*rowOp (fun _ : Fin (n+1) => b n) (gridR (n+1) z) := by
  rw [←actual_reference hn,←actual_reference hn]
  simp only [stopped,rowOp_apply,←Finset.mul_sum];ring

private theorem good_path {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m)
    {T R ρ u : ℝ} (ht : 0≤T) (rp : 0≤ρ) (rc : ρ≤1) (up : 0≤u)
    (small : 2*(2*(30*ρ+3*u))≤1/(π*(n+1:ℕ))^2)
    (budget : 8*(R/(1/(π*(n+1:ℕ))^2))/sqrt m<ρ/2)
    (z : ℝ → State m) (flow : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T z)
    (G : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => CircleSpectrum.k0 1) (z 0))
    (init : ‖gridR (n+1) (z 0)‖≤R) (nz : ∀ j, 0<length (z 0) j) :
    |mean (z T)-reference (n+1) m (stopped n T) (z 0)|≤6*(2*(30*ρ+3*u))*(R/(1/(π*(n+1:ℕ))^2)) := by
  let K := sampledMatrix (N:=n+1) 1
  let kQ := fun _ : Fin (n+1) => CircleSpectrum.k0 1
  let lam := 1/(π*(n+1:ℕ))^2
  let p := rowOp (fun _ : Fin (n+1) => b n)
  let f := referencePath 1 (rawResidual (n+1) m (z 0))
  have lp : 0<lam := by dsimp [lam];positivity
  have start : gridR (n+1) (z 0)=f 0 := (referencePath_zero ..).symm
  have df (s : ℝ) : HasDerivAt f (-(gramOp K (f s))) s := referencePath_deriv _ (by norm_num) (by norm_num) _ s
  have gap (v) : lam*‖v‖^2 ≤ inner ℝ v (gramOp K v) := gramOp_gap hn ho 1 (by norm_num) (by norm_num) v
  have area := frozen_area_cap f _ ht lp df gap
  rw [←start] at area
  have result := sharp_observable K kQ f flow (by omega) hm (by norm_num) ht lp (by positivity) small
    rp rc budget nz start df (area.trans (div_le_div_of_nonneg_right init lp.le)) gap
    (fun s _ tube g ad => by
      have l := G.track_ops (by omega) hm (by norm_num) rp rc up tube ad
      exact ⟨(norm_sub_rev _ _).le.trans l.1,l.2⟩)
    (weight_abs_le_one n 1 (by norm_num)) (population_row_factorization n hn ho 1 (by norm_num) (by norm_num))
  have mode := frozen_mode f (gramOp K) p ht (lt_of_lt_of_le (by positivity : 0<(3:ℝ)/π^2) (CircleKernelGD.gamma_bounds (N:=n+1)).1)
    df (gramOp_eigenrow 1 (b n) (by norm_num) (by norm_num))
  rw [←start] at mode
  rw [stopped_ref _ _ hn,←actual_reference hn]
  change |mean (z T)-(mean (z 0)-p (gridR (n+1) (z 0))+multiplier n T*p (gridR (n+1) (z 0)))|≤_
  exact (by rw [show multiplier n T*p (gridR (n+1) (z 0))=p (f T) from mode.symm];exact result.2)

private theorem lag {n m : ℕ} (hn : 3≤n+1) (hm : 0<m) (T : ℝ) (Y : Seed m→ℝ)
    (mY : MemLp Y 2 (seedLaw m)) :
    sqrt (∫ z, (Y z-reference (n+1) m (b n) z)^2 ∂seedLaw m) ≤
    sqrt (∫ z, (Y z-reference (n+1) m (stopped n T) z)^2 ∂seedLaw m)+sqrt 2*multiplier n T := by
  let D := Y-reference (n+1) m (stopped n T)
  let V := Y-reference (n+1) m (b n)
  let L := reference (n+1) m (stopped n T)-reference (n+1) m (b n)
  let μ := seedLaw m
  have mem (q : ℝ) := CircleSeedIntegrability.reference_memLp (n+1) m q 2 (by norm_num)
  have md : MemLp D 2 μ := mY.sub (mem _)
  have mv : MemLp V 2 μ := mY.sub (mem _)
  have ml : MemLp L 2 μ := (mem _).sub (mem _)
  have mp : 0≤multiplier n T := exp_nonneg _
  have op := rowOp_norm (N:=n+1) (by omega) zero_le_one (fun _ => weight_abs_le_one n 1 (by norm_num))
  have ub (z : Seed m) : (L z)^2≤(multiplier n T)^2*‖gridR (n+1) z‖^2 := by
    have p := ((rowOp (fun _ : Fin (n+1) => b n)).le_opNorm (gridR (n+1) z)).trans
      ((mul_le_mul_of_nonneg_right op (norm_nonneg _)).trans_eq (one_mul _))
    have sq := pow_le_pow_left₀ (norm_nonneg _) p 2
    rw [Real.norm_eq_abs,sq_abs] at sq
    dsimp [L];rw [stopped_ref n m hn T z,add_sub_cancel_left,mul_pow]
    exact mul_le_mul_of_nonneg_left sq (sq_nonneg _)
  have rr := CircleInitialResidualSecond.residual_second hn hm
  have integral := integral_mono ml.integrable_sq (rr.1.const_mul ((multiplier n T)^2)) ub
  rw [integral_const_mul,rr.2] at integral
  have cost := sqrt_le_sqrt integral
  rw [sqrt_mul (sq_nonneg _),sqrt_sq mp,mul_comm (multiplier n T),CirclePairedCoefficient.rms_of_mem μ ml] at cost
  change sqrt (∫ z, V z^2 ∂μ)≤sqrt (∫ z, D z^2 ∂μ)+_
  rw [CirclePairedCoefficient.rms_of_mem μ mv,CirclePairedCoefficient.rms_of_mem μ md]
  have eq : V=D+L := by dsimp [V,D,L];abel
  rw [eq]
  exact (lpNorm_add_le md (by norm_num)).trans (add_le_add_right cost _)

/-- Width-explicit RMS bound for every measurable endpoint of the actual flow.
The good-event, exceptional-event, and stopping contributions retain distinct
width, time, and confidence dependences. -/
theorem finite {n m : ℕ} (hn : 3≤n+1) (ho : Odd (n+1)) (hm : 0<m) {T d : ℝ}
    (ht : 0≤T) (dp : 0≤d) (dm : d≤m)
    (z : Seed m→ℝ→State m) (start : ∀ ω, z ω 0=ω)
    (flow : ∀ ω, IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt m) 1 T (z ω))
    (meas : Measurable fun ω => z ω T) :
    let R := 2+sqrt (8*d)
    let u := 64*sqrt (d/m)
    let lam := 1/(π*(n+1:ℕ))^2
    let U := R/lam
    let ρ := 32*U/sqrt m
    let e := 2*(30*ρ+3*u)
    let Δ := 8*(((n+1:ℕ):ℝ)+1)^2*exp (-d)
    let K := 7/2+3*sqrt (2*T)*CircleFlowMoments.gaussianSquareNorm+(1+sqrt (2*T)+2*T/sqrt m)*lossConstant
    ρ≤1 → u≤1 → 2*e≤lam →
    sqrt (∫ ω, (mean (z ω T)-reference (n+1) m (CircleSpectrum.weight 1 n) ω)^2 ∂seedLaw m) ≤
      6*e*U+K*(min 1 Δ)^(1/4:ℝ)+sqrt 2*exp (-(CircleKernelGD.gamma (n+1)*T)) := by
  intro R u lam U ρ e Δ K rc uc small
  let μ := seedLaw m
  let I := {ω : Seed m | ¬GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => CircleSpectrum.k0 1) ω} ∪
    {ω | R < initialRms (n+1) m ω}
  let Z := {ω : Seed m | ¬∀ j, 0<length ω j}
  let G := (toMeasurable μ (I∪Z))ᶜ
  have rp : 0<ρ := by dsimp [ρ,U,R,lam];positivity
  have up : 0≤u := by dsimp [u];positivity
  have wp : 0<U/sqrt m := by dsimp [U,R,lam];positivity
  have kp : 0≤K := by
    have a : 0≤CircleFlowMoments.gaussianSquareNorm := lpNorm_nonneg
    have l : 0≤lossConstant := by unfold lossConstant;positivity
    dsimp [K];positivity
  have budget : 8*U/sqrt m<ρ/2 := by dsimp [ρ];linarith only [wp,show 32*U/sqrt m/2=16*(U/sqrt m) by ring,show 8*U/sqrt m=8*(U/sqrt m) by ring]
  have measure : μ.real Gᶜ≤min 1 Δ := by
    apply le_min measureReal_le_one
    change μ.real ((toMeasurable μ (I∪Z))ᶜ)ᶜ≤_
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    have c := CircleWidthPublished.initialization_confidence (N:=n+1) hm dp dm rp.le rc uc
    have hz : μ Z=0 := ae_iff.mp (CircleInitializationConcentration.length_pos_ae m)
    have un := (measureReal_union_le (μ:=μ) I Z).trans (add_le_add_left c _)
    rwa [measureReal_def μ Z,hz,ENNReal.toReal_zero,add_zero] at un
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have mult0 : 0≤multiplier n T := exp_nonneg _
  have gp := (by positivity : 0≤3/π^2).trans (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have mult1 : multiplier n T≤1 := exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg gp ht))
  have slo : 0≤stopped n T := mul_nonneg wb.1 (sub_nonneg.mpr mult1)
  have shi : stopped n T≤1 := (mul_le_of_le_one_right wb.1 (sub_le_self _ mult0)).trans wb.2
  let Y := fun ω => mean (z ω T)
  let X := Y-reference (n+1) m (stopped n T)
  have h := gaussian_flow_fourth_sharp (N:=n+1) (by omega) hm (by norm_num : 0<(1:ℝ)) (by norm_num) ht slo shi z start flow meas
  have hd : MemLp X 4 μ := h.1
  have good (ω) (goodSeed : ω∈G) : |X ω|≤6*e*U := by
    have notBad : ω∉I∪Z := fun hh => goodSeed (subset_toMeasurable μ (I∪Z) hh)
    have ini : GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin (n+1) => CircleSpectrum.k0 1) ω := by
      by_contra bad;exact notBad (Or.inl (Or.inl bad))
    have r : ‖gridR (n+1) ω‖≤R := le_of_not_gt (fun bad => notBad (Or.inl (Or.inr bad)))
    have nonzero : ∀ j, 0<length ω j := not_not.mp (fun bad => notBad (Or.inr bad))
    have bnd := good_path hn ho hm ht rp.le rc up small budget (z ω) (flow ω)
    rw [start] at bnd
    exact bnd ini r nonzero
  have pos : 0≤6*e*U := by dsimp [e,U,R,lam];positivity
  have four := (CircleGaussianTracking.fourth_integral hd).le.trans (pow_le_pow_left₀ lpNorm_nonneg h.2 4)
  have rms := CircleFlowTracking.all_seed_rms (measurableSet_toMeasurable μ (I∪Z)).compl
    (CircleGaussianTracking.square_mem hd) pos kp good measure four
  have mY : MemLp Y 2 μ := by
    have id : Y=X+reference (n+1) m (stopped n T) := by dsimp [X];abel
    rw [id];exact (hd.mono_exponent (by norm_num)).add (CircleSeedIntegrability.reference_memLp (n+1) m (stopped n T) 2 (by norm_num))
  have pay := lag hn hm T Y mY
  have nn : 0≤min 1 Δ := le_min zero_le_one (by dsimp [Δ];positivity)
  have root : sqrt (sqrt (min 1 Δ))=(min 1 Δ)^(1/4:ℝ) := by
    rw [sqrt_eq_rpow,sqrt_eq_rpow,←rpow_mul nn];norm_num
  rw [root] at rms
  exact pay.trans (add_le_add_left rms _)
end CircleVariableFlow
