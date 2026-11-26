module

public import CirclePairedGDTube
public import CirclePairedGDShadow
public import CirclePairedGDCenter
public import CirclePairedGDEndpoint
public import CirclePairedGDCoordinates
import all CircleFlowMoments
import all CircleEscape
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Population means on a common Gaussian coordinate box for the two
simultaneous gradient-descent trajectories. -/
@[expose] public section
noncomputable section
namespace CirclePairedGDBox
open Real CircleEscapeBridge CircleFlowPath CirclePairedGDTube
variable {m N : ℕ}

private theorem mean_unit {m : ℕ} (hm : 0<m) (p : ℝ) :
    ((1/sqrt (m:ℝ))/π) * (m*p) = (sqrt (m:ℝ)/π)*p := by
  have mp : 0<(m:ℝ) := by exact_mod_cast hm
  have sp := Real.sqrt_pos.mpr mp
  have sq := Real.sq_sqrt mp.le
  field_simp
  nlinarith only [congrArg (· * p) sq]

/-- Uniform relative coordinate control gives explicit upper and lower bounds
on the signed population mean. -/
theorem signed_mean {z : State m} {σ A W e : ℝ} (hm : 0<m) (hs : |σ|=1)
    (hA : 0≤A) (hW : 0≤W) (he : e≤1/8) (h : Near z (σ*A) (σ*W) e) :
    (sqrt (m:ℝ)/π)*(A*W/2) ≤ σ * CircleFlowMoments.mean z ∧
      σ * CircleFlowMoments.mean z ≤ (sqrt (m:ℝ)/π)*(2*(A*W)) := by
  have hs2 : σ^2=1 := by rw [←sq_abs, hs]; norm_num
  have ax : |σ*A|=A := by rw [abs_mul,hs,one_mul,abs_of_nonneg hA]
  have wx : |σ*W|=W := by rw [abs_mul,hs,one_mul,abs_of_nonneg hW]
  have ha := mul_le_mul_of_nonneg_right he hA
  have hw := mul_le_mul_of_nonneg_right he hW
  let v (j : Fin m) := (σ*z (j,0))*‖(initial z).w j‖
  have pt (j : Fin m) : A*W/2 ≤ v j ∧ v j ≤ 2*(A*W) := by
    obtain ⟨a,w,b⟩ := h j
    rw [ax] at a
    rw [wx] at w b
    have ar : |σ*z (j,0)-A| ≤ e*A := by
      rw [show σ*z (j,0)-A = σ*(z (j,0)-σ*A) by nlinarith only [congrArg (· * A) hs2],
        abs_mul,hs,one_mul]
      exact a
    have wa : |z (j,1)| ≤ W+e*W := by
      have := abs_sub_abs_le_abs_sub (z (j,1)) (σ*W)
      linarith [wx]
    have wb : W-e*W ≤ |z (j,1)| := by
      have := abs_sub_abs_le_abs_sub (σ*W) (z (j,1))
      rw [abs_sub_comm (σ*W) (z (j,1))] at this
      linarith [wx]
    have lo : |z (j,1)| ≤ ‖(initial z).w j‖ := Complex.abs_re_le_norm ((initial z).w j)
    have hi : ‖(initial z).w j‖ ≤ |z (j,1)|+|z (j,2)| :=
      Complex.norm_le_abs_re_add_abs_im ((initial z).w j)
    have ar' := abs_le.mp ar
    have la : (7/8)*A ≤ σ*z (j,0) := by linarith
    have ua : σ*z (j,0) ≤ (9/8)*A := by linarith
    have lw : (7/8)*W ≤ ‖(initial z).w j‖ := by linarith
    have uw : ‖(initial z).w j‖ ≤ (10/8)*W := by linarith
    dsimp only [v]
    have hprod := mul_nonneg hA hW
    constructor
    · have hh := mul_le_mul la lw (by positivity) ((by positivity : 0≤(7/8)*A).trans la)
      linarith only [hh,hprod]
    · have hh := mul_le_mul ua uw (norm_nonneg _) (by positivity)
      linarith only [hh,hprod]
  have scale : 0≤(1/sqrt (m:ℝ))/π := by positivity
  have ident : σ*CircleFlowMoments.mean z = ((1/sqrt (m:ℝ))/π)*∑ j, v j := by
    unfold CircleFlowMoments.mean CircleEscape.populationMean
    rw [mul_left_comm σ, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by dsimp [v,initial]; ring)
  rw [ident,←mean_unit hm,←mean_unit hm]
  constructor
  · apply mul_le_mul_of_nonneg_left _ scale
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (pt j).1)
  · apply mul_le_mul_of_nonneg_left _ scale
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (pt j).2)

private theorem initial_near {T : ℕ} {R : ℝ} (hN : 0<N) (hR : 1≤R) {z : Seed m}
    (hz : z ∈ CircleSynchronizedEscape.syncBox N m (2*T) 1 (R/2)) :
    Near z R R (1/(8*(N:ℝ)*1024^T)) := by
  intro j
  have coord := CirclePairedGDCoordinates.coordinate hN hR hz j
  have r : 0≤R := by linarith
  simpa [abs_of_nonneg r] using And.intro (coord 0) (And.intro (coord 1) (coord 2))

private theorem contrast_lower {slow fast σ S F c q : ℝ}
    (hs : |σ|=1) (hc : 0≤c) (gap : 8*S≤F) (grow : q*S≤F)
    (hl : c*(F/2) ≤ σ*fast) (hu : σ*slow ≤ c*(2*S)) :
    c*(q*S)/4 ≤ |slow-fast| := by
  calc
    c*(q*S)/4 ≤ c*F/4 := by linarith only [mul_le_mul_of_nonneg_left grow hc]
    _ ≤ σ*(fast-slow) := by linarith only [mul_le_mul_of_nonneg_left gap hc,hl,hu]
    _ ≤ |σ*(fast-slow)| := le_abs_self _
    _ = |slow-fast| := by rw [abs_mul,hs,one_mul,abs_sub_comm]

open CirclePairedGDCenter CircleWeightedStep

private theorem contrast_of_near {t : ℕ} {η R : ℝ} (hN : 3≤N) (hm : 0<m)
    (hη : 0<η) (hR : 32≤R) (hlarge : 16*(32/η+32)≤R^2) (ht : 1≤t) {z : Seed m}
    (nearby : ∀ τ : ℝ, 1/2≤τ → Near (iterate τ η N z (t+1))
      (CirclePairedGDCenter.sign (t+1) * (orbit N m τ η R (t+1)).1)
      (CirclePairedGDCenter.sign (t+1) * (orbit N m τ η R (t+1)).2) (1/(8*(N:ℝ)))) :
    sqrt (m:ℝ)*((2:ℝ)^(3^t)) ≤ |CirclePairedGDEndpoint.contrast N m (t+1) η z| := by
  let S := orbit N m (1/2) η R (t+1)
  have r1 : 1≤R := by linarith
  have sl := orbit_large (τ:=1/2) hN hm (by norm_num) hη r1 hlarge (t+1)
  have fa := orbit_large (τ:=2) hN hm (by norm_num) hη r1 hlarge (t+1)
  have np : 3≤(N:ℝ) := by exact_mod_cast hN
  have nr : 0<(N:ℝ) := by linarith
  have e : 1/(8*(N:ℝ))≤1/8 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have slow := (signed_mean hm (abs_sign (t+1)) ((by linarith : 0≤R).trans sl.1)
    ((by linarith : 0≤R).trans sl.2) e (nearby (1/2) (by norm_num))).2
  have fast := (signed_mean hm (abs_sign (t+1)) ((by linarith : 0≤R).trans fa.1)
    ((by linarith : 0≤R).trans fa.2) e (nearby 2 (by norm_num))).1
  have lb : 16≤S.1*S.2 := by
    have p := mul_le_mul sl.1 sl.2 (by linarith : 0≤R) ((by linarith : 0≤R).trans sl.1)
    change R*R≤S.1*S.2 at p
    linarith only [p, show (16:ℝ) ≤ R*R from (by nlinarith [sq_nonneg (R-4)])]
  have scale : 4*π≤S.1*S.2 := by linarith [pi_lt_four]
  have scaled : sqrt (m:ℝ)*((2:ℝ)^(3^t)) ≤
      (sqrt (m:ℝ)/π)*((2:ℝ)^(3^t)*(S.1*S.2))/4 := by
    field_simp [pi_ne_zero]
    linarith only [scale]
  apply scaled.trans
  exact contrast_lower (abs_sign (t+1)) (by positivity)
    (separation hN hm hη r1 hlarge (t+1) (by omega))
    (ratio_growth hN hm hη r1 hlarge t) fast slow

/-- A single Gaussian box forces a doubly exponential separation of the two
actual simultaneous-GD population means. Its side depends on the number of
updates, and its center may be chosen for any fixed positive step size. -/
theorem box_contrast_scaled {N m t : ℕ} {η R : ℝ} (hN : 3≤N) (odd : Odd N) (hm : 0<m)
    (hη : 0<η) (hR : 32≤R) (hlarge : 16*(32/η+32)≤R^2) (ht : 1≤t) {z : Seed m}
    (hz : z ∈ CircleSynchronizedEscape.syncBox N m (2*(t+1)) 1 (R/2)) :
    sqrt (m:ℝ)*((2:ℝ)^(3^t)) ≤ |CirclePairedGDEndpoint.contrast N m (t+1) η z| := by
  have r1 : 1≤R := by linarith
  have near := initial_near (by omega : 0<N) r1 hz
  apply contrast_of_near hN hm hη hR hlarge ht
  intro τ hτ
  exact CirclePairedGDShadow.shadow hN hm odd hτ hη r1 hlarge (t+1) near

/-- Width-independent consequence of the finite box lower bound. -/
theorem box_contrast {N m t : ℕ} {η R : ℝ} (hN : 3≤N) (odd : Odd N) (hm : 0<m)
    (hη : 0<η) (hR : 32≤R) (hlarge : 16*(32/η+32)≤R^2) (ht : 1≤t) {z : Seed m}
    (hz : z ∈ CircleSynchronizedEscape.syncBox N m (2*(t+1)) 1 (R/2)) :
    (2:ℝ)^(3^t) ≤ |CirclePairedGDEndpoint.contrast N m (t+1) η z| :=
  (le_mul_of_one_le_left (by positivity) (Real.one_le_sqrt.mpr (by exact_mod_cast hm))).trans
    (box_contrast_scaled hN odd hm hη hR hlarge ht hz)

end CirclePairedGDBox
