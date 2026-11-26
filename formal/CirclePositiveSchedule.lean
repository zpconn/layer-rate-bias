module

public import CirclePositiveWidth
public import CircleFiniteSchedule
import all CirclePositiveWidth
import all CircleFiniteSchedule
import all CircleGaussianTracking
import all CircleFiniteConfidence
import Mathlib.Tactic

/-! A width polynomial of degree 16 for every fixed positive layer
multiplier. The dependence on the multiplier is explicit. -/
@[expose] public section
noncomputable section
namespace CirclePositiveSchedule
open Real MeasureTheory Filter Topology CircleEscapeBridge CircleFlowPath CircleActualTracking
  CircleWeightedStep CircleWeightedDynamics CircleSpectrum CircleFiniteConfidence
open CirclePositiveConfidence (mult)

def stretch (τ : ℝ) := mult τ/τ

def designWidth (τ : ℝ) (N : ℕ) := (⌈300000000*(stretch τ)^2⌉₊*N^8)^2

private theorem row_le_radius {N : ℕ} (hn : 3≤N) {δ : ℝ} (hd : 0<δ) :
    rowScale N δ ≤ CircleFiniteWidth.A N δ := by
  let x : ℝ := N
  let r := CircleFiniteWidth.R δ
  have big : 3≤x := by dsimp only [x];exact_mod_cast hn
  have xp : 0<x := by linarith
  have rp : 0≤r := sqrt_nonneg _
  have h : rowScale N δ≤r*(3*x) := by
    apply (sq_le_sq₀ (show 0≤rowScale N δ from sqrt_nonneg _) (mul_nonneg rp (by positivity))).mp
    rw [rowScale,mul_pow,show r^2=12/δ from sq_sqrt (by positivity),sq_sqrt (by positivity)]
    change 90*x/δ≤12/δ*(3*x)^2
    field_simp
    nlinarith only [xp,big,mul_nonneg (by linarith only [big] : 0≤x-1) xp.le]
  have lower : 3*x≤4*(π*x)^2 := by
    have a := mul_le_mul_of_nonneg_right pi_gt_three.le xp.le
    have b := pow_le_pow_left₀ (show 0≤3*x by positivity) a 2
    nlinarith only [b,mul_nonneg (by linarith only [big] : 0≤x-1) xp.le,xp]
  exact h.trans ((mul_le_mul_of_nonneg_left lower rp).trans_eq
    (by simp [CircleFiniteWidth.A,CircleFiniteWidth.D,CircleFiniteWidth.gap,r,x];ring))

/-- Uniform comparison of the five design terms. It holds at arbitrary
confidence, including away from the inverse-grid specialization. -/
theorem width_compare (n : ℕ) (hn : 3≤n+1) {τ δ ε : ℝ} (hp : 0<τ) (hd : 0<δ) (he : 0<ε) :
    CirclePositiveWidth.width τ n δ ε ≤ 3*(stretch τ)^2*CircleFiniteWidth.width n δ ε := by
  let N := n+1
  let x : ℝ := N
  let a := stretch τ
  let c := mult τ
  let B := CircleFiniteWidth.A N δ
  let V := CircleFiniteWidth.D N δ
  let gap₁ := CircleFiniteWidth.gap N
  let H := gridScale N δ
  let b := weight 1 n
  let f := weight τ n
  let L := CircleFiniteWidth.width n δ ε
  let F := 2*x^2*V/ε
  have xp : 0<x := by dsimp [x,N];positivity
  have x3 : 3≤x := by dsimp only [x];exact_mod_cast hn
  have cp : 0<c := zero_lt_one.trans_le (le_max_left _ _)
  have a1 : 1≤a := (one_le_div hp).mpr (le_max_right _ _)
  have ap := zero_lt_one.trans_le a1
  have bp : 0<B := by dsimp [B,CircleFiniteWidth.A,CircleFiniteWidth.D,CircleFiniteWidth.R,CircleFiniteWidth.gap];positivity
  have fp : 0≤F := by dsimp [F,V,CircleFiniteWidth.D,CircleFiniteWidth.R,CircleFiniteWidth.gap];positivity
  have lp : 0<gap₁ := by dsimp [gap₁,CircleFiniteWidth.gap];positivity
  have hg : 0≤H := by dsimp [H,gridScale];positivity
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
  have wf := CircleGaussianTracking.weight_bounds n hp.le
  change 0≤b ∧ b≤1 at wb
  change 0≤f ∧ f≤1 at wf
  have eqG : CirclePositiveWidth.gap τ N=τ*gap₁ := by dsimp [gap₁,CircleFiniteWidth.gap,CirclePositiveWidth.gap];ring
  have eqD : CirclePositiveWidth.D τ N δ=V/τ := by
    rw [CirclePositiveWidth.D,eqG];dsimp only [V,CircleFiniteWidth.D,gap₁];ring
  have eqA : CirclePositiveWidth.A τ N δ=a*B := by
    rw [CirclePositiveWidth.A,eqD]
    dsimp only [B,CircleFiniteWidth.A,a,stretch,c,V];ring
  have five : max B (max (sqrt (36/δ)) (max (10*(x+1)/(δ*B))
    (max (2*(H+36*B)/gap₁) (F*(signedScale N b δ+(1+b)*36*B))))) ≤ L := le_rfl
  simp only [max_le_iff] at five
  obtain ⟨fa,fe,fm,fg,fs⟩ := five
  have Lp := bp.le.trans fa
  have aa := mul_le_mul_of_nonneg_right a1 ap.le
  have larger : a≤3*a^2 := by nlinarith only [aa,sq_nonneg a]
  have big : L≤3*a^2*L := by nlinarith only [mul_le_mul_of_nonneg_right (a1.trans larger) Lp]
  have sg : 0≤signedScale N b δ := mul_nonneg
    (by change 0≤6/x+1-b;linarith only [wb.2,div_nonneg (by norm_num : (0:ℝ)≤6) xp.le]) (sqrt_nonneg _)
  have smallSigned : signedScale N f δ≤3*B := by
    have f1 : 6/x+1-f≤3 := by linarith only [wf.1, (div_le_iff₀ xp).mpr (by linarith only [x3] : 6≤2*x)]
    exact mul_le_mul f1 (row_le_radius hn hd) (sqrt_nonneg _) (by norm_num : (0:ℝ)≤3)
  have grid : 2*(c*H+36*c*(a*B))/(τ*gap₁)≤3*a^2*L := by
    have inside : H+36*a*B≤a*(H+36*B) := by nlinarith only [mul_le_mul_of_nonneg_right a1 hg]
    calc
      _ = (2*a/gap₁)*(H+36*a*B) := by dsimp only [a,stretch,c];ring
      _ ≤ (2*a/gap₁)*(a*(H+36*B)) := mul_le_mul_of_nonneg_left inside (by positivity)
      _ = a^2*(2*(H+36*B)/gap₁) := by ring
      _ ≤ a^2*L := mul_le_mul_of_nonneg_left fg (sq_nonneg _)
      _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg a) Lp]
  have signed : (2*x^2*(V/τ)/ε)*(c*signedScale N f δ+(1+f)*36*c*(a*B))≤3*a^2*L := by
    let s := signedScale N b δ+(1+b)*36*B
    have ba := mul_le_mul_of_nonneg_right a1 bp.le
    have low : 36*B≤s := by dsimp [s];nlinarith only [sg,mul_nonneg wb.1 bp.le]
    have hi := mul_le_mul_of_nonneg_right wf.2 (mul_nonneg ap.le bp.le)
    have part : signedScale N f δ+(1+f)*36*a*B≤3*a*s := by
      nlinarith only [smallSigned,hi,ba,mul_le_mul_of_nonneg_left low ap.le,mul_nonneg ap.le bp.le]
    calc
      _ = (a*F)*(signedScale N f δ+(1+f)*36*a*B) := by dsimp only [a,stretch,F,c];ring
      _ ≤ (a*F)*(3*a*s) := mul_le_mul_of_nonneg_left part (mul_nonneg ap.le fp)
      _ = (3*a^2)*(F*s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left fs (by positivity)
  change max _ (max _ (max _ (max _ _)))≤_
  simp only [max_le_iff]
  rw [eqA,eqD,eqG]
  refine ⟨(mul_le_mul_of_nonneg_left fa ap.le).trans (mul_le_mul_of_nonneg_right larger Lp),fe.trans big,?_,grid,signed⟩
  have den : δ*B≤δ*(a*B) := mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_right a1 bp.le).trans_eq' (one_mul B)) hd.le
  exact (div_le_div_of_nonneg_left (by positivity) (mul_pos hd bp) den).trans (fm.trans big)

/-- Fixed-τ width coefficient and the explicit physical-clock upper bound. -/
theorem schedule (n : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {τ η : ℝ} (hp : 0<τ) (hη : 0<η)
    (stable : η*(1+τ)≤2) :
    let N := n+1
    let m := designWidth τ N
    let T := CirclePositiveWidth.cap τ N η (1/(N:ℝ)) (1/(N:ℝ))
    T≤⌈(192/(η*τ))*(N:ℝ)^2*log N⌉₊ ∧
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤1/(N:ℝ) ∧ ∀ z∈E,
      rms τ η N z T≤1/(N:ℝ)^3 ∧
      (N:ℝ)^2*|learnerMean τ η N z T-reference N m (weight τ n) z|≤1/(N:ℝ) ∧
      ∃ w : State m, Tendsto (iterate τ η N z) atTop (𝓝 w) ∧ ‖gridR N w‖=0 := by
  intro N m T
  let δ := 1/(N:ℝ)
  have big : (3:ℝ)≤N := by exact_mod_cast hn
  have x : (0:ℝ)<N := by linarith only [big]
  have d : 0<δ := by dsimp [δ];positivity
  have small : δ<1 := (div_lt_one x).mpr (by linarith only [big])
  have fit := CircleFiniteSchedule.width_bound n hn
  change CircleFiniteWidth.width n δ δ≤sqrt (CircleFiniteSchedule.designWidth N:ℝ) at fit
  have size := (width_compare n hn hp d d).trans (mul_le_mul_of_nonneg_left fit (show 0≤3*(stretch τ)^2 by positivity))
  have arithmetic : 3*(stretch τ)^2*sqrt (CircleFiniteSchedule.designWidth N:ℝ) ≤ sqrt (m:ℝ) := by
    dsimp only [m,designWidth,CircleFiniteSchedule.designWidth]
    push_cast
    rw [sqrt_sq (by positivity),sqrt_sq (by positivity)]
    convert mul_le_mul_of_nonneg_right (Nat.le_ceil (300000000*(stretch τ)^2)) (pow_nonneg x.le 8) using 1; ring
  have clk : T=CircleFiniteWidth.cap N (η*τ) δ δ := by
    dsimp only [T,CirclePositiveWidth.cap,CircleFiniteWidth.cap,CirclePositiveWidth.gap,CircleFiniteWidth.gap]
    congr 1
    ring
  obtain ⟨E,meas,prob,he⟩ := CirclePositiveWidth.finite_width n m hn odd hp hη stable d small d (size.trans arithmetic)
  refine ⟨clk.le.trans (CircleFiniteSchedule.cap_bound N hn (mul_pos hη hp)),E,meas,prob,?_⟩
  intro z hz
  obtain ⟨training,err,_,lim⟩ := he z hz
  exact ⟨training,(mul_comm _ _).le.trans ((le_div_iff₀ (sq_pos_of_pos x)).mp err),lim⟩

end CirclePositiveSchedule
