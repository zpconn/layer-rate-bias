module

public import CircleGroupedWidth
public import CircleGroupedGrowthWidth
public import CircleFiniteSchedule
public import CircleGroupedDyadic
import all CircleDiscreteBudget
import all CircleGroupedDyadic
import all CircleGroupedResidual
import all CircleSpectralPathLength
import all CircleGroupedBudget
import all CircleFiniteWidth
import all CircleGridSpectrum
import all CircleReciprocalSpectral
import all CircleTangentDrift
import Mathlib.Tactic

/-! A confidence-uniform dyadic Gaussian movement budget and the resulting
polynomial width for actual fixed-step circle GD. -/
@[expose] public section
noncomputable section
namespace CircleGroupedTrainingSchedule
open Real Set Filter Topology MeasureTheory CircleSpectralPathLength CircleEscapeBridge CircleGroupedWidth
  CircleTangentDrift CircleReciprocalSpectral CircleActualTracking CircleGroupedBudget
variable {N m : ℕ}

def K := 6*(1+budgetConstant)
def movement (N : ℕ) (δ : ℝ) := K*sqrt (N:ℝ)*sqrt (1/δ)
theorem one_le_K : 1≤K := by unfold K;linarith only [budgetConstant_nonneg]

private theorem seed_tail [NeZero N] (hm : 0<m) (ho : Odd N) {δ : ℝ} (hd : 0<δ) :
    (seedLaw m).real {z | movement N δ/2<seedBudget ho m z}≤δ/6 := by
  let J := (N+1).log2
  let F := CircleGroupedResidual.groupCost N J (shell ho) CircleDiscreteBudget.rate
  have fcap := CircleGroupedDyadic.cost_le ho
  change F≤budgetConstant*sqrt (N:ℝ) at fcap
  have root : sqrt (6/δ) = sqrt 6*sqrt (1/δ) := by
    rw [←sqrt_mul (by norm_num : (0:ℝ)≤6)]
    congr 1;ring
  have c : sqrt (6:ℝ)≤3 := (sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have hi : sqrt (6/δ)*F≤movement N δ/2 := by
    rw [root];unfold movement K
    calc
      _ ≤ (3*sqrt (1/δ))*(budgetConstant*sqrt (N:ℝ)) := mul_le_mul
        (mul_le_mul_of_nonneg_right c (sqrt_nonneg _)) fcap
        (CircleGroupedDyadic.cost_pos ho).le (by positivity)
      _ ≤ _ := by nlinarith only [mul_nonneg (sqrt_nonneg (N:ℝ)) (sqrt_nonneg (1/δ))]
  exact (measureReal_mono (s₂:={z | sqrt (6/δ)*F < CircleGroupedResidual.groupSeed N m J
      (shell ho) CircleDiscreteBudget.rate z}) (fun z hz => lt_of_le_of_lt hi hz)).trans
    (CircleGroupedResidual.group_design_tail hm J (shell ho) _ CircleDiscreteBudget.rate_pos
      (CircleGroupedDyadic.cost_pos ho) hd)

/-- One movement allowance uniformly handles every horizon and every positive
fixed step at most one. -/
theorem training (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) {η δ ε : ℝ}
    (he : 0<η) (hu : η≤1) (hd : 0<δ) (hp : 0<ε)
    (width : CircleGroupedWidth.width n (movement (n+1) δ) δ ε≤sqrt m) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E,
      Trained n η δ ε (movement (n+1) δ) z := by
  have kp : 0<K := by linarith only [one_le_K]
  have np : (0:ℝ)<(n+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  have mp : 0<movement (n+1) δ := by unfold movement;positivity
  have cash : 2*movement (n+1) δ≤sqrt (m:ℝ) := (le_max_left ..).trans width
  have hm : 0<m := by exact_mod_cast sqrt_pos.mp ((by linarith only [mp] : 0<2*movement (n+1) δ).trans_le cash)
  apply CircleGroupedWidth.finite_width n m hn ho he hu hd hp mp width
  apply (measureReal_mono (s₂:={z | movement (n+1) δ/2<seedBudget ho m z}) _).trans (seed_tail hm ho hd)
  rintro z ⟨_,bad⟩
  by_contra h
  apply bad
  intro T
  exact (dyadic_area he hu ho T m z).trans (le_of_not_gt h)

/-- Integer width allocation and physical high-confidence conclusion at every
larger integer width, for arbitrary requested accuracy and confidence. -/
theorem sufficient_neurons (n m : ℕ) (hn : 3≤n+1) (ho : Odd (n+1)) {η δ ε : ℝ}
    (he : 0<η) (hu : η≤1) (hd : 0<δ) (hd' : δ≤1) (hp : 0<ε) (hp' : ε≤1)
    (size : CircleGroupedGrowthWidth.neurons K n δ ε≤m) :
    (CircleGroupedGrowthWidth.neurons K n δ ε:ℝ) ≤ ((4000*K^2)^2+1)*(n+1:ℝ)^6/(δ^2*ε^2) ∧
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E,
      Trained n η δ ε (movement (n+1) δ) z := by
  exact ⟨CircleGroupedGrowthWidth.width_bound n hn one_le_K hd hd' hp hp',
    training n m hn ho he hu hd hp ((CircleGroupedGrowthWidth.sufficient K n δ ε).trans (sqrt_le_sqrt (by exact_mod_cast size)))⟩

open Asymptotics
/-- The improved design has O(N¹⁰) neurons when both δ and ε equal 1/N.
For every odd grid, the paired error is at most N⁻³ with failure mass at most 1/N
at the original long cap. -/
theorem inverse_training :
    ((fun n : ℕ => (CircleGroupedGrowthWidth.neurons K n (1/(n+1:ℝ)) (1/(n+1:ℝ)):ℝ))
      =O[atTop] fun n => (n+1:ℝ)^10) ∧
    ∀ n : ℕ, 3≤n+1 → Odd (n+1) → ∀ η : ℝ, 0<η → η≤1 →
      let N := n+1
      let m := CircleGroupedGrowthWidth.neurons K n (1/(N:ℝ)) (1/(N:ℝ))
      let T := CircleFiniteWidth.cap N η (1/(N:ℝ)) (1/(N:ℝ))
      T≤⌈(192/η)*(N:ℝ)^2*log N⌉₊ ∧
      ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤1/(N:ℝ) ∧
        ∀ z∈E, CircleRateTrajectory.rms η N z T≤1/(N:ℝ)^3 ∧
          |CircleRateTrajectory.learnerMean η N z T-CircleEscapeBridge.reference N m (CircleSpectrum.weight 1 n) z|≤1/(N:ℝ)^3 := by
  refine ⟨CircleGroupedGrowthWidth.inverse_schedule one_le_K,?_⟩
  intro n hn ho η he hu N m T
  have px : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos n)
  have pd : 0<1/(N:ℝ) := one_div_pos.mpr px
  obtain ⟨E,me,prob,good⟩ := training n m hn ho he hu pd pd (CircleGroupedGrowthWidth.sufficient K n _ _)
  refine ⟨CircleFiniteSchedule.cap_bound N hn he,E,me,prob,fun z hz => ⟨(good z hz).1,(good z hz).2.1.trans_eq ?_⟩⟩
  ring

end CircleGroupedTrainingSchedule
