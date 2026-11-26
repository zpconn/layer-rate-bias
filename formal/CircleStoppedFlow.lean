module

public import CircleSharpMoments
public import CircleTruncatedBudget
import all CircleTruncatedBudget
import all CircleSharpMoments
import all CircleSharpTracking
import all CircleSpectralPathLength
import all CircleActualTracking
import all CircleSharpInitialization
import all CircleFlowMoments
import all CircleGaussianTracking
import all CircleEscapeBridge
public import CircleKernelGD
import all CircleKernelGD
import Mathlib.Tactic

/-! The population statistic at the two logarithmic physical times. The
transient of the constant Fourier mode is kept separate from the nonlinear
error at the same time and seed. -/
public section
noncomputable section
namespace CircleStoppedFlow
open MeasureTheory ProbabilityTheory Real Set Filter
open CircleFlowPath CircleFlowMoments CircleFlowTracking CircleSharpTracking CircleActualTracking
  CircleTangentDrift CircleSpectralPathLength CircleEscapeBridge CircleGridSpectrum CircleComparison
  CircleSharpInitialization CircleTruncatedBudget CircleGaussianTracking CircleSharpMoments
open scoped ENNReal Topology

def multiplier (n T : ℕ) (τ : ℝ) := exp (-(aliasValue (tangentCoeff τ) (0:ZMod (n+1)) * T))
def stoppedWeight (n T : ℕ) (τ : ℝ) := CircleSpectrum.weight τ n*(1-multiplier n T τ)

private theorem stopped_identity (n T : ℕ) (hN : 3≤n+1) (ho : Odd (n+1)) {τ : ℝ}
    (ht : 1/2≤τ) (hu : τ≤2) (z : Seed ((n+1)^32)) :
    reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) z+
      rowOp (fun _ : Fin (n+1) => CircleSpectrum.weight τ n)
        (referencePath τ (rawResidual (n+1) ((n+1)^32) z) T) =
    reference (n+1) ((n+1)^32) (stoppedWeight n T τ) z := by
  let p := rowOp (fun _ : Fin (n+1) => CircleSpectrum.weight τ n)
  let f := referencePath τ (rawResidual (n+1) ((n+1)^32) z)
  have pos : 0 < aliasValue (tangentCoeff τ) (0:ZMod (n+1)) :=
    lt_of_lt_of_le (by positivity : 0 < 1/(π*((n+1:ℕ):ℝ))^2) (tangent_gap hN ho τ ht hu 0)
  have tr := frozen_mode f (gramOp (sampledMatrix τ)) p (Nat.cast_nonneg T) pos
    (referencePath_deriv τ (by linarith) hu _) (gramOp_eigenrow τ _ (by linarith) hu)
  have zero : f 0 = gridR (n+1) z := referencePath_zero _ _
  rw [zero] at tr
  change p (f T) = multiplier n T τ*p (gridR (n+1) z) at tr
  change _ + p (f T) = _
  rw [tr,←actual_reference hN,←actual_reference hN]
  simp only [p,stoppedWeight,rowOp_apply,← Finset.mul_sum]
  ring

theorem good_endpoint (n k T : ℕ) (hN : 36864≤n+1) (hk : k+17≤n+1) (ho : Odd (n+1))
    {τ : ℝ} (ht : 1/2≤τ) (hu : τ≤2) (F : Benchmark n τ) :
    let B := initialError (n+1) ((n+1)^32) τ
    let V := truncatedBudget ho ((n+1)^32) T
    ∃ G : Set (Seed ((n+1)^32)), MeasurableSet G ∧ (seedLaw _).real Gᶜ ≤ 14/((n:ℝ)+1)^k ∧
      ∀ z ∈ G, |mean (F.path z T) - reference (n+1) ((n+1)^32) (stoppedWeight n T τ) z| ≤
        6*B z*V z + 44928*(1+V z)*V z/((n:ℝ)+1)^16 := by
  intro B V
  have hh : |τ| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; exact hu
  obtain ⟨G,meas,tail,inside⟩ := CircleSharpEvent.design_event (n+1) k hN hk hh
  refine ⟨G,meas,by simpa using tail,?_⟩
  intro z hz
  obtain ⟨nz,en,rd,Bcap,marg⟩ := inside z hz
  let D := (n:ℝ)+1
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast (by omega : 32 ≤ n+1)
  have dp : 0 < D := by linarith
  have pp := pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2
  have big := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) d 5
  have cmp : 4/D^7 ≤ 1/(4*(π*D)^2) := by
    rw [show D^7=D^2*D^5 by ring]
    field_simp
    nlinarith only [pp,big]
  rw [←stopped_identity n T (by omega) ho ht hu z]
  have orig := F.start z
  have forward := F.flow (T:ℝ) (Nat.cast_nonneg T) z
  have args := sharp_stopped_design n (T:ℝ) (Nat.cast_nonneg T) (by omega) ho τ ht hu (V z) (F.path z) forward
  rw [orig] at args
  apply args en (by simpa using marg) nz
  · simpa only [gridR,CircleGaussianTracking.initialRms,Nat.cast_add,Nat.cast_one] using rd
  · exact (show B z ≤ 4/D^7 from by simpa only [Nat.cast_add,Nat.cast_one] using Bcap).trans cmp
  · exact flow_area ho ht hu T z

private theorem bounded_weight (n T : ℕ) (hN : 3≤n+1) (ho : Odd (n+1)) {τ : ℝ}
    (ht : 1/2≤τ) (hu : τ≤2) : 0 ≤ stoppedWeight n T τ ∧ stoppedWeight n T τ ≤ 1 := by
  have g := tangent_gap hN ho τ ht hu (0:ZMod (n+1))
  have pos : 0 ≤ aliasValue (tangentCoeff τ) (0:ZMod (n+1)) := (by positivity : 0≤1/(π*((n+1:ℕ):ℝ))^2).trans g
  have w := CircleGaussianTracking.weight_bounds n (by linarith : 0≤τ)
  have r : multiplier n T τ ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg pos (Nat.cast_nonneg _)))
  have r' : 0≤multiplier n T τ := exp_nonneg _
  exact ⟨mul_nonneg w.1 (by linarith),(mul_le_mul_of_nonneg_left (by linarith : 1-multiplier n T τ≤1) w.1).trans (by simpa using w.2)⟩

private theorem norm_arithmetic {x t b v d p cb cv cd : ℝ} (hx : 1≤x) (ht : 1≤t)
    (nv : 0≤v) (pc : 0≤cb) (pc' : 0≤cv) (pd : 0≤cd)
    (hb : b≤cb/x^16) (hv : v≤cv*sqrt (sqrt t)) (hd : d≤cd*x^2)
    (hp : p≤14/x^72) :
    6*b*v+44928*(1/x^16)*(1+v)*v+1/x^16 + d*sqrt (sqrt p) ≤
      (6*cb*cv+44928*(cv+cv^2)+1+2*cd)*sqrt t/x^16 := by
  have xp : 0<x := by linarith
  have s := one_le_sqrt.mpr ht
  have ss : sqrt (sqrt t) ≤ sqrt t := by
    apply sqrt_le_iff.mpr
    refine ⟨sqrt_nonneg _,?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr s) (sqrt_nonneg t)]
  have vl := hv.trans (mul_le_mul_of_nonneg_left ss pc')
  have v2 : v^2 ≤ cv^2*sqrt t := by simpa only [mul_pow,sq_sqrt (sqrt_nonneg t)] using pow_le_pow_left₀ nv hv 2
  have vv : (1+v)*v ≤ (cv+cv^2)*sqrt t := by nlinarith
  have rr : sqrt (sqrt p) ≤ 2/x^18 := by
    have h : 14/x^72 ≤ ((2/x^18)^2)^2 := by
      calc
        _ ≤ 16/x^72 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
        _ = _ := by field_simp; norm_num
    simpa only [sqrt_sq (by positivity : (0:ℝ)≤(2/x^18)^2),sqrt_sq (by positivity : 0≤2/x^18)] using
      sqrt_le_sqrt (sqrt_le_sqrt (hp.trans h))
  have product := mul_le_mul hb vl nv (div_nonneg pc (by positivity))
  have e := mul_le_mul hd rr (sqrt_nonneg _) (by positivity)
  have small := mul_le_mul_of_nonneg_left vv (by positivity : (0:ℝ) ≤ 44928*(1/x^16))
  have constcap := mul_le_mul_of_nonneg_right s (by positivity : 0 ≤ (1+2*cd)/x^16)
  have eq : cd*x^2*(2/x^18) = 2*cd/x^16 := by field_simp
  rw [eq] at e
  calc
    _ ≤ 6*(cb/x^16*(cv*sqrt t)) + 44928*(1/x^16)*((cv+cv^2)*sqrt t) + sqrt t*((1+2*cd)/x^16) := by
      rw [one_mul] at constcap
      nth_rw 1 [add_div] at constcap
      rw [mul_assoc (44928*(1/x^16)),mul_assoc (6:ℝ) b]
      linarith only [e,small,product,constcap]
    _ = _ := by ring


def fourthConstant := 7/2+45*gaussianSquareNorm+216*lossConstant
def stoppedConstant := 6*(6*markConstant)*truncConstant+
  44928*(truncConstant+truncConstant^2)+1+2*fourthConstant

set_option maxRecDepth 4096 in
/-- Uniform in the rate, the deterministic stopping time and the choice of
actual flow. Both logarithmic endpoints are inside the finite window. -/
theorem same_time_rms (n T : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1))
    {τ : ℝ} (ht : 1/2≤τ) (hu : τ≤2) (F : Benchmark n τ) (hT : T ≤ 100*(n+1)) :
    sqrt (∫ z, (mean (F.path z T) - reference (n+1) ((n+1)^32) (stoppedWeight n T τ) z)^2
      ∂seedLaw ((n+1)^32)) ≤ stoppedConstant*sqrt (T+1:ℕ)/((n:ℝ)+1)^16 := by
  let N := n+1
  let m := N^32
  let x := (n:ℝ)+1
  let μ := seedLaw m
  let B := initialError N m τ
  let V := truncatedBudget ho m T
  let D := fun z => mean (F.path z T)-reference N m (stoppedWeight n T τ) z
  let w := 1/x^16
  have nx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have xp : 0<x := by linarith
  have hxN : (N:ℝ) = x := Nat.cast_add_one n
  have hm := pow_pos (Nat.succ_pos n) 32
  have hmx : sqrt (m:ℝ) = x^16 := by
    rw [show (m:ℝ)=x^32 by dsimp [m]; rw [Nat.cast_pow,hxN],show x^32=(x^16)^2 by ring,sqrt_sq (by positivity)]
  have tbound : (T:ℝ) ≤ 100*x := by
    rw [←hxN]; exact_mod_cast hT
  have scales : (T:ℝ)/sqrt m ≤ 100 := by
    rw [hmx,div_le_iff₀ (by positivity)]
    exact tbound.trans (mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ nx (by decide : 1≤16)) (by norm_num))
  have x2 : x≤x^2 := by simpa only [pow_one] using pow_le_pow_right₀ nx (by decide : 1≤2)
  have sq : sqrt (2*(T:ℝ)) ≤ 15*x := sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [tbound,x2,sq_nonneg x]⟩
  have wt := bounded_weight n T (by omega) ho ht hu
  have hd := gaussian_flow_fourth_sharp (Nat.succ_pos n) hm (by linarith : 0<τ) hu (Nat.cast_nonneg T)
    wt.1 wt.2 F.path F.start (F.flow T (Nat.cast_nonneg _)) (F.endpoint T (Nat.cast_nonneg _))
  change MemLp D 4 μ ∧ lpNorm D 4 μ ≤ _ at hd
  have lc : 0≤lossConstant := by unfold lossConstant; positivity
  have gc : 0≤gaussianSquareNorm := lpNorm_nonneg
  have cd : 0≤fourthConstant := by unfold fourthConstant; positivity
  have db : lpNorm D 4 μ ≤ fourthConstant*x^2 := by
    apply hd.2.trans
    have s' : 2*(T:ℝ)/sqrt m ≤ 200 := by rw [mul_div_assoc]; linarith only [scales]
    have xa : 1≤x^2 := one_le_pow₀ nx
    have h1 := mul_le_mul_of_nonneg_right (show sqrt (2*(T:ℝ))≤15*x^2 by linarith) gc
    have h2 := mul_le_mul_of_nonneg_right (show 1+sqrt (2*(T:ℝ))+2*T/sqrt m≤216*x^2 by linarith) lc
    change 7/2+3*sqrt (2*(T:ℝ))*gaussianSquareNorm+(1+sqrt (2*(T:ℝ))+2*T/sqrt m)*lossConstant ≤ _
    unfold fourthConstant
    nlinarith only [xa,h1,h2]
  have hb := initialError_fourth (N:=N) hm τ (abs_le.mpr ⟨by linarith,hu⟩)
  have hv := budget_mem ho hm T
  obtain ⟨G,mG,prob,good⟩ := good_endpoint n 72 T hN (by omega) ho ht hu F
  let E := fun z => 6*(B z*V z)+(44928*w)*((1+V z)*V z)+w
  have hw : 0≤w := by dsimp [w]; positivity
  have hE := CircleSharpMoments.envelope hb.1 hv w hw
  have ene (z : Seed m) : 0≤E z := by
    have hb : 0 ≤ B z := by dsimp only [B,initialError,finiteRms]; positivity
    have hv : 0≤V z := budget_nonneg ho m T z
    dsimp only [E]; positivity
  have ge (z : Seed m) (hz : z∈G) : |D z|≤E z := by
    have pp := good z hz
    change |D z| ≤ 6*B z*V z+44928*(1+V z)*V z/x^16 at pp
    apply pp.trans
    change _ ≤ _ + w
    exact (le_add_of_nonneg_right hw).trans_eq (by unfold w; ring)
  have bound := random_envelope_split hd.1 hE.1 ene mG ge
  apply bound.trans ((add_le_add hE.2 le_rfl).trans ?_)
  have ht1 : (1:ℝ)≤(T+1:ℕ) := by exact_mod_cast (by omega : 1≤T+1)
  have bc := budget_lp4 ho hm T
  have cc : 0≤truncConstant := by
    unfold truncConstant
    have a := CircleSpectralPathLength.modeConstant_nonneg
    have b := shellConstant_pos
    positivity
  exact norm_arithmetic nx ht1 lpNorm_nonneg (by dsimp [markConstant]; positivity) cc cd
    (hb.2.trans_eq (by rw [hmx])) bc db prob

private theorem finite_transient (n T p : ℕ) (lo : (p:ℝ)*log ((n:ℝ)+1) ≤ CircleKernelGD.gamma (n+1)*T) :
    multiplier n T 1 ≤ 1/((n:ℝ)+1)^p := by
  let x := (n:ℝ)+1
  have xp : 0<x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  change exp (-(CircleKernelGD.gamma (n+1)*T)) ≤ 1/x^p
  rw [show 1/x^p=exp (-((p:ℝ)*log x)) by
    rw [←log_pow,exp_neg,exp_log (by positivity),one_div]]
  exact exp_le_exp.mpr (neg_le_neg lo)

private theorem multiplier_bounds (n : ℕ) :
    let x := (n:ℝ)+1
    multiplier n (CircleKernelGD.short x) 1 ≤ 1/x^3 ∧
      multiplier n (CircleKernelGD.medium x) 1 ≤ 1/x^18 := by
  intro x
  have nx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have ln := log_nonneg nx
  have hg := (CircleKernelGD.gamma_bounds (N:=n+1)).1
  have a := Nat.le_ceil (π^2*log x)
  have b := Nat.le_ceil (60*log x)
  change _ ≤ (CircleKernelGD.short x:ℝ) at a
  change _ ≤ (CircleKernelGD.medium x:ℝ) at b
  have gpos : 0≤3/π^2 := by positivity
  constructor
  · apply finite_transient
    calc
      (3:ℝ)*log x = (3/π^2)*(π^2*log x) := by field_simp
      _ ≤ _ := mul_le_mul hg a (mul_nonneg (sq_nonneg _) ln) (gpos.trans hg)
  · apply finite_transient
    have pp : π^2 ≤ 10 := by nlinarith [pi_lt_d2, mul_nonneg (sub_nonneg.mpr pi_lt_d2.le) (show 0≤3.15+π by positivity)]
    have ge : (18:ℝ)≤3/π^2*60 := by field_simp; linarith
    calc
      (18:ℝ)*log x ≤ (3/π^2*60)*log x := mul_le_mul_of_nonneg_right ge ln
      _ = (3/π^2)*(60*log x) := by ring
      _ ≤ _ := mul_le_mul hg b (by positivity) (gpos.trans hg)

private theorem benchmark_window (n : ℕ) :
    let x := (n:ℝ)+1
    CircleKernelGD.short x ≤ CircleKernelGD.medium x ∧ CircleKernelGD.medium x ≤ 100*(n+1) := by
  intro x
  have nx : 1≤x := by dsimp [x]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have ln := log_nonneg nx
  have pp : π^2≤60 := by nlinarith only [pi_lt_four,pi_pos,mul_nonneg (sub_nonneg.mpr pi_lt_four.le) (by positivity : 0≤4+π)]
  constructor
  · exact Nat.ceil_le_ceil (mul_le_mul_of_nonneg_right pp ln)
  · apply Nat.ceil_le.mpr
    push_cast
    change 60*log x≤100*x
    linarith only [log_le_self (show 0≤x by linarith),nx]

private theorem matched_bound (n T : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1))
    (F : Benchmark n 1) (hT : T≤100*(n+1)) :
    sqrt (∫ z, (mean (F.path z T) - matched n 1 z)^2 ∂seedLaw ((n+1)^32)) ≤
      stoppedConstant*sqrt (T+1:ℕ)/((n:ℝ)+1)^16+
      multiplier n T 1*CircleResidualSpectrum.modeConstant := by
  let b := CircleSpectrum.weight 1 n
  let e := multiplier n T 1
  let b' := stoppedWeight n T 1
  let Y := fun z => mean (F.path z T)
  have w := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
  have hm := pow_pos (Nat.succ_pos n) 32
  have hN' : 3≤n+1 := by omega
  have ydiff : MemLp (fun z => Y z-reference (n+1) ((n+1)^32) b z) 4 (seedLaw ((n+1)^32)) :=
    (gaussian_flow_fourth_sharp (Nat.succ_pos n) hm (by norm_num : (0:ℝ)<1) (by norm_num)
      (Nat.cast_nonneg T) w.1 w.2 F.path F.start (F.flow T (Nat.cast_nonneg _)) (F.endpoint T (Nat.cast_nonneg _))).1
  have y : MemLp Y 2 (seedLaw ((n+1)^32)) := by
    have hy := (ydiff.mono_exponent (by norm_num : (2:ENNReal)≤4)).add
      (CircleSeedIntegrability.reference_memLp (n+1) ((n+1)^32) b 2 (by norm_num))
    convert hy using 1
    ext; dsimp only [Pi.add_apply]; ring
  have h := change_reference_bound hN' hm Y y b b'
  have epos : 0≤e := exp_nonneg _
  have bd : |b'-b| ≤ e := by
    change |b*(1-e)-b|≤e
    rw [show b*(1-e)-b= -(b*e) by ring,abs_neg,abs_of_nonneg (mul_nonneg w.1 epos)]
    exact mul_le_of_le_one_left epos w.2
  exact h.trans (add_le_add (same_time_rms n T hN ho (by norm_num) (by norm_num) F hT)
    (mul_le_mul_of_nonneg_right bd CircleSpectralPathLength.modeConstant_nonneg))

/-- The short and middle same-seed flow errors about the fitted kernel carry
respectively the N⁻³ and N⁻¹⁸ stopping transient. The nonlinear part is
O(√(1+T)/N¹⁶) at both logarithmic physical times. -/
theorem logarithmic_endpoints (n : ℕ) (hN : 36864≤n+1) (ho : Odd (n+1)) (F : Benchmark n 1) :
    let x := (n:ℝ)+1
    let S := CircleKernelGD.short x
    let M := CircleKernelGD.medium x
    let cost := fun T : ℕ => stoppedConstant*sqrt (T+1:ℕ)/x^16
    let distance := fun T : ℕ => sqrt (∫ z, (mean (F.path z T) - matched n 1 z)^2 ∂seedLaw ((n+1)^32))
    distance S ≤ cost S + (1/x^3)*CircleResidualSpectrum.modeConstant ∧
    distance M ≤ cost M + (1/x^18)*CircleResidualSpectrum.modeConstant := by
  have window := benchmark_window n
  have tr := multiplier_bounds n
  exact ⟨(matched_bound n _ hN ho F (window.1.trans window.2)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right tr.1 CircleSpectralPathLength.modeConstant_nonneg)),
    (matched_bound n _ hN ho F window.2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right tr.2 CircleSpectralPathLength.modeConstant_nonneg))⟩

end CircleStoppedFlow
