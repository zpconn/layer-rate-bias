module

public import CircleWidthThreshold
import all CircleWidthUpper
import all CircleWidthMoment
import all CircleCapInduction
import all CircleCapMoments
import all CircleInitializationCheck
import all CircleTangentDrift
import all CircleGaussianTracking
import all CircleSeedIntegrability
import Mathlib.Tactic

/-! A constant-energy initialization screen for unrestricted fixed-step GD. -/
@[expose] public section
noncomputable section
namespace CircleWidthEnergyScreen
open Real MeasureTheory Set Filter
open CircleEscape CircleEscapeBridge CircleCapInduction CircleCapMoments CircleInitializationCheck
open CircleWidthUpper CircleWidthMoment CircleWidthTracking CircleGaussianTracking

/-- At bounded initial energy, the exact Gram increment keeps the deterministic
step stable up to the specified deterministic time, without changing the update. -/
theorem energy_bound (N m T : ℕ) (hn : 81≤N) (odd : Odd N) (hm : 0<m) (span : 12*T≤m)
    {η : ℝ} (hη : 0≤η) (hc : η≤1) (z : Net ℂ m) (E : energy z≤4) :
    ∀ t≤T, energy (train N m η z t)≤4+12*(t:ℝ)/m := by
  let Z := train N m η z
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have boundC : C N≤3/10 := by
    have h : (81:ℝ)≤N := by exact_mod_cast hn
    have hh : (4:ℝ)/N≤1/20 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    unfold C; linarith
  have step (t : ℕ) (ht : t≤T) (ih : energy (Z t)≤4+12*(t:ℝ)/m) :
      (m:ℝ)*(energy (Z (t+1))-energy (Z t))≤12*η := by
    have H := CircleCapMoments.initial_top N m (by omega) odd hm (Z t)
    have cap : energy (Z t)≤5 := by
      have h : 12*(t:ℝ)≤m := by exact_mod_cast (show 12*t≤m by omega)
      linarith only [ih,(div_le_one mp).mpr h]
    have ep : 0≤energy (Z t) := by unfold energy rawEnergy;positivity
    have h := mul_le_mul boundC cap ep (by norm_num : (0:ℝ)≤3/10)
    have hcap : η*curvature (gridPoint N) (Z t)≤7/2 := by
      have h' := mul_le_mul_of_nonneg_left (H.2.trans h) hη
      nlinarith only [h',hc]
    exact actual_increment _ _ _ (by omega) hm η _ hη hcap H.1.1 (label_energy N (by omega)).le
  intro t ht
  induction t with
  | zero => simpa [Z,train] using E
  | succ t ih =>
    have H := ih (by omega)
    have d := step t (by omega) H
    have h := (le_div_iff₀ mp).mpr (show (energy (Z (t+1))-energy (Z t))*(m:ℝ)≤12 by nlinarith only [d,hc])
    change energy (Z (t+1))≤4+12*((t+1:ℕ):ℝ)/m
    push_cast
    linarith only [H,h,show 12*((t:ℝ)+1)/(m:ℝ)=12*t/m+12/m by ring]

private theorem init_eq (m : ℕ) (z : Seed m) : energy (initial z)=CircleTangentDrift.meanEnergy z := by
  rw [energy,initial_energy_coordinates,CircleTangentDrift.meanEnergy,Fintype.sum_prod_type]
  simp [CircleTangentDrift.length_sq,Fin.sum_univ_three,add_assoc]

private theorem error_on_screen (n m T : ℕ) (hn : 81≤n+1) (odd : Odd (n+1)) (hm : 0<m) (span : 12*T≤m)
    {η b : ℝ} (hη : 0≤η) (hc : η≤1) (hb : 0≤b) (h1 : b≤1) (z : Seed m)
    (hz : z∉exceptional (n+1) m 0 1) :
    |rawError (n+1) m T η b z|≤8*sqrt m := by
  have initE : energy (initial z)≤4 := by
    rw [init_eq]
    have hG : CircleTangentDrift.GoodInit 1 0 1 (CircleGridSpectrum.sampledMatrix 1)
        (fun _ : Fin (n+1) => CircleSpectrum.k0 1) z := by
      by_contra hh; exact hz (Or.inl hh)
    exact hG.energy
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have rise : 12*(T:ℝ)/m≤1 := (div_le_one mp).mpr (by exact_mod_cast span)
  have cap := energy_bound (n+1) m T hn odd hm span hη hc (initial z) initE T le_rfl
  have hY := mean_le_energy m hm (train (n+1) m η (initial z) T)
  have hZ := reference_envelope (n+1) m (by omega) hm b hb h1 z
  have root : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  apply (abs_sub _ _).trans
  change |populationMean _ (train (n+1) m η (initial z) T)|+_≤_
  nlinarith only [hY,hZ,mul_le_mul_of_nonneg_left initE (sqrt_nonneg (m:ℝ)),
    mul_le_mul_of_nonneg_left (show energy (train (n+1) m η (initial z) T)≤5 by linarith) (sqrt_nonneg (m:ℝ)),root]

theorem screened_mse (n m T : ℕ) (hn : 81≤n+1) (odd : Odd (n+1)) (hm : 0<m) (span : 12*T≤m)
    {η r u : ℝ} (hη : 0≤η) (hc : η≤1) (H : FitsBudget m T r u) :
    (∫ z, (rawError (n+1) m T η (stoppedCoefficient n T η) z)^2 ∂seedLaw m) ≤
      (errorBound m T r u)^2 + 64*m*failureBound (n+1) m u +
      sqrt (CircleShortGDTails.fourthBound m T)*sqrt (failureBound (n+1) m 1) := by
  let X := rawError (n+1) m T η (stoppedCoefficient n T η)
  let E := exceptional (n+1) m r u
  let F := exceptional (n+1) m 0 1
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : 0≤(1:ℝ))
  have gp : 0≤CircleKernelGD.gamma (n+1) := (show 0≤(3:ℝ)/π^2 by positivity).trans CircleKernelGD.gamma_bounds.1
  have al : 0≤1-η*CircleKernelGD.gamma (n+1) := sub_nonneg.mpr ((mul_le_of_le_one_left gp hc).trans CircleKernelGD.gamma_bounds.2)
  have a1 : 1-η*CircleKernelGD.gamma (n+1)≤1 := sub_le_self _ (mul_nonneg hη gp)
  have b0 : 0≤stoppedCoefficient n T η := mul_nonneg wb.1 (sub_nonneg.mpr (pow_le_one₀ al a1))
  have b1 : stoppedCoefficient n T η≤1 := (mul_le_of_le_one_right wb.1 (sub_le_self _ (pow_nonneg al T))).trans wb.2
  have m4 := raw_mem4 (n+1) m T η (stoppedCoefficient n T η)
  have mono := two_event_bound X m4 E F (CircleWidthUpper.measurable_exceptional hm _ _)
    (CircleWidthUpper.measurable_exceptional hm _ _) (errorBound m T r u) (8*sqrt m)
    (CircleWidthUpper.inside (by omega) odd hm hη hc H) (error_on_screen _ _ _ hn odd hm span hη hc b0 b1)
  have p := probability (N:=n+1) hm H.1 H.2.1 H.2.2.1 H.2.2.2.1
  have q := probability (N:=n+1) hm (ρ:=0) (u:=1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have four := raw_fourth hη hc (by omega : 0<n+1) hm T b0 b1
  rw [show (8*sqrt (m:ℝ))^2=64*m by rw [mul_pow,sq_sqrt (by positivity)];ring] at mono
  exact mono.trans (add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left p (by positivity)) _)
    (mul_le_mul (sqrt_le_sqrt four) (sqrt_le_sqrt q) (sqrt_nonneg _) (sqrt_nonneg _)))

end CircleWidthEnergyScreen
