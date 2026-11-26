module

public import CircleGroupedDynamics
public import CircleFiniteWidth
public import CircleGroupedResidual
import all CircleGroupedResidual
import all CircleSpectralPathLength
import all CircleGroupedBudget
import all CircleFiniteWidth
import all CircleFiniteConfidence
import all CircleRateTrajectory
import all CircleReadoutMargin
import all CircleKernelGD
import all CircleGaussianTracking
import all CircleReciprocalSpectral
import all CircleTangentDrift
import Mathlib.Tactic

/-! The two improved finite-width designs for physical fixed-step circle GD. -/
@[expose] public section
noncomputable section
namespace CircleGroupedWidth
open Real MeasureTheory Filter Topology Set Finset CircleEscapeBridge CircleActualTracking CircleFlowPath
  CircleWidthTracking CircleRateTrajectory CircleFiniteConfidence CircleSpectrum CircleFiniteWidth
  CircleDiscreteTracking CircleTangentDrift CircleGridSpectrum CircleReciprocalSpectral
variable {N m : ℕ}

def AreaBound (N : ℕ) [NeZero N] (η U : ℝ) (z : Seed m) := ∀ T : ℕ,
  η*(∑ t ∈ range T, ‖((propagator N η)^t) (gridR N z)‖)≤U

/-- Width lower bound for the square root of the number of neurons. Here D is
the accumulated nonlinear path allowance and the tube scale is A=2D. -/
def width (n : ℕ) (D δ ε : ℝ) :=
  let N := n+1
  let b := weight 1 n
  let A := 2*D
  max A (max (sqrt (36/δ)) (max (135*((N:ℝ)+1)/(δ*A))
    (max (2*(gridScale N δ+36*A)/gap N)
      ((2*(N:ℝ)^2*D/ε)*(signedScale N b δ+CircleGroupedDynamics.drift N b*A)))))

def Trained (n : ℕ) {m : ℕ} (η δ ε D : ℝ) (z : Seed m) : Prop :=
  let N := n+1
  let T := cap N η δ ε
  rms η N z T≤1/(N:ℝ)^3 ∧
  |learnerMean η N z T-reference N m (weight 1 n) z|≤ε/(N:ℝ)^2 ∧
  (∀ t, rms η N z t≤(1-η*(gap N/2))^t*R δ ∧ budget η N z t≤D) ∧
  ∃ w : State m, Tendsto (iterateAt N η z) atTop (𝓝 w) ∧ ‖gridR N w‖=0

private theorem init (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) (hm : 0<m)
    {η δ A U : ℝ} (pδ : 0<δ) (pa : 0<A) (hr : A/sqrt m≤1) (en : 36/δ≤m)
    (margin : 135*(((n+1:ℕ):ℝ)+1)/(δ*A)≤sqrt m)
    (path : (seedLaw m).real {z | ‖gridR (n+1) z‖≤R δ ∧ ¬AreaBound (n+1) η U z}≤δ/6) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E,
      CircleGroupedDynamics.Bounds (n+1) (weight 1 n) (A/sqrt m) (R δ) (gridScale (n+1) δ/sqrt m)
        (signedScale (n+1) (weight 1 n) δ/sqrt m) z ∧ AreaBound (n+1) η U z := by
  let N := n+1
  let b := weight 1 n
  let ρ := A/sqrt m
  let P := seedLaw m
  let F : Fin 6→Set (Seed m) := ![
    {z | R δ<‖gridR N z‖},
    {z | ¬∀ i j : Fin N, |gridGram 1 z (startGates z) i j-sampledMatrix 1 i j|≤gridScale N δ/sqrt m},
    {z | ¬∀ j : Fin N, |CircleSignedRow.mixedRow N b z z (CircleEscape.gridPoint N j)|≤signedScale N b δ/sqrt m},
    {z | ¬meanEnergy z≤4}, {z | ¬CircleReadoutMargin.Good N ρ z},
    {z | ‖gridR N z‖≤R δ ∧ ¬AreaBound (n+1) η U z}]
  have each (i : Fin 6) : P.real (F i)≤δ/6 := by
    fin_cases i
    · have a := CircleInitialResidualSecond.residual_tail hn odd hm (show 0<R δ by unfold R;positivity)
      apply a.trans_eq
      rw [R,sq_sqrt (by positivity : 0≤12/δ)];field_simp;ring
    · exact grid_failure N m hm pδ
    · exact signed_failure n m hn odd hm pδ
    · exact energy_failure m hm pδ en
    · exact CircleReadoutMargin.failure_design hm pa pδ hr margin
    · exact path
  let V := ⋃ i, F i
  have total : P.real V≤δ := (measureReal_iUnion_fintype_le F).trans ((sum_le_sum (fun i _ => each i)).trans_eq (by simp;ring))
  refine ⟨(toMeasurable P V)ᶜ,(measurableSet_toMeasurable _ _).compl,?_,?_⟩
  · change P.real ((toMeasurable P V)ᶜ)ᶜ≤δ
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def];exact total
  · intro z hz
    have no (i : Fin 6) : z∉F i := fun hh => hz (subset_toMeasurable P V (mem_iUnion_of_mem i hh))
    have res : ‖gridR N z‖≤R δ := le_of_not_gt (no 0)
    refine ⟨⟨res,not_not.mp (no 3),not_not.mp (no 4),not_not.mp (no 1),not_not.mp (no 2)⟩,?_⟩
    by_contra h
    exact no 5 ⟨res,h⟩

/-- All positive odd grids, arbitrary positive fixed step at most one, and
the exact five-entry improved width formula. The only remaining input is
the tail of the chosen linear movement budget. -/
theorem finite_width (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {η δ ε D : ℝ}
    (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hε : 0<ε) (hp : 0<D)
    (hw : width n D δ ε≤sqrt m)
    (path : (seedLaw m).real {z | ‖gridR (n+1) z‖≤R δ ∧ ¬AreaBound (n+1) η (D/2) z}≤δ/6) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E, Trained n η δ ε D z := by
  let N := n+1
  let b := weight 1 n
  let A := 2*D
  let L := sqrt (m:ℝ)
  let ρ := A/L
  let T := cap N η δ ε
  have gp : 0<gap N := by dsimp [gap,N];positivity
  have ap : 0<A := by dsimp [A];positivity
  have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have wb := CircleGaussianTracking.weight_bounds n (by norm_num : (0:ℝ)≤1)
  change 0≤b ∧ b≤1 at wb
  change max _ (max _ (max _ (max _ _)))≤L at hw
  simp only [max_le_iff] at hw
  obtain ⟨wA,wE,wM,wG,wS⟩ := hw
  have lp : 0<L := ap.trans_le wA
  have hm : 0<m := by exact_mod_cast sqrt_pos.mp lp
  have small : ρ≤1 := (div_le_one lp).mpr wA
  have en : 36/δ≤(m:ℝ) := (sq_sqrt (by positivity : 0≤36/δ)).symm.le.trans
    ((pow_le_pow_left₀ (sqrt_nonneg _) wE 2).trans_eq (sq_sqrt (Nat.cast_nonneg m)))
  obtain ⟨E,meas,bad,good⟩ := init n m hn odd hm hδ ap small en wM path
  refine ⟨E,meas,bad,?_⟩
  intro z hz
  obtain ⟨I,area⟩ := good z hz
  have gg : 0≤gridScale N δ := by unfold gridScale;positivity
  have sv : 0≤signedScale N b δ := by
    unfold signedScale
    exact mul_nonneg (by linarith only [div_nonneg (by norm_num : (0:ℝ)≤6) np.le,wb.2]) (sqrt_nonneg _)
  have cash : 2/sqrt (m:ℝ)*(2*(D/2))≤ρ := by dsimp only [ρ,A,L];exact (by ring : (2:ℝ)/sqrt m*(2*(D/2))=(2*D)/sqrt m).le
  have grid : 2*(36*ρ+gridScale N δ/L)≤gap N := by
    have w := (div_le_iff₀ gp).mp wG
    dsimp only [ρ];field_simp;linarith only [w]
  have C := CircleGroupedDynamics.trajectory hn odd hm z hη hc wb.1
    (div_nonneg ap.le lp.le) small (div_nonneg gg lp.le) (div_nonneg sv lp.le) (half_pos hp).le I area cash grid
  have rt := (C.1 T).1.trans (time_bound (Nat.succ_pos n) hε hδ hη hc ((half_le_self gp.le).trans (CircleKernelGD.gap_le_one hn)))
  have coeff : (signedScale N b δ/L+CircleGroupedDynamics.drift N b*ρ)*(2*(D/2))≤ε/(2*(N:ℝ)^2) := by
    have w : (2*(N:ℝ)^2*D)*(signedScale N b δ+CircleGroupedDynamics.drift N b*A)≤L*ε :=
      (div_le_iff₀ hε).mp (by convert wS using 1;ring)
    dsimp only [ρ];field_simp;linarith only [w]
  have proj := (mul_le_of_le_one_left (show 0≤rms η N z T from norm_nonneg _) wb.2).trans (rt.trans (min_le_right _ _))
  refine ⟨rt.trans (min_le_left _ _), (C.1 T).2.2.trans ((add_le_add proj coeff).trans_eq (by ring)),?_,C.2⟩
  exact fun t => ⟨(C.1 t).1,(C.1 t).2.1.trans_eq (by ring)⟩

/-- Conservative movement uses the slowest grid eigenvalue and needs no
additional Gaussian event. -/
theorem full_path (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {η δ ε : ℝ}
    (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hε : 0<ε)
    (hw : width n (D (n+1) δ) δ ε≤sqrt m) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E, Trained n η δ ε (D (n+1) δ) z := by
  have gp : 0<gap (n+1) := by unfold gap;positivity
  have rp : 0<R δ := by unfold R;positivity
  apply finite_width n m hn odd hη hc hδ hε (by unfold D;positivity) hw
  have empty : {z : Seed m | ‖gridR (n+1) z‖≤R δ ∧ ¬AreaBound (n+1) η (D (n+1) δ/2) z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨r,ha⟩
    apply ha
    let W := propagator (n+1) η
    let f (t : ℕ) := (W^t) (gridR (n+1) z)
    have balance (T : ℕ) : gap (n+1)*(η*∑ t ∈ range T, ‖f t‖)+‖f T‖≤R δ := by
      induction T with
      | zero => simpa [f] using r
      | succ T ih =>
        have step := CircleRateTrajectory.contractionAt hn odd hη.le hc (f T)
        have eq : f (T+1)=W (f T) := by dsimp [f];rw [pow_succ'];rfl
        change ‖W (f T)‖≤(1-η*gap (n+1))*‖f T‖ at step
        rw [sum_range_succ,eq];linarith only [ih,step]
    intro T
    have ap := (le_div_iff₀ gp).2 (by linarith only [balance T,norm_nonneg (f T)] : (η*∑ t ∈ range T, ‖f t‖)*gap (n+1)≤R δ)
    exact ap.trans_eq (by dsimp [D];ring)
  rw [empty,measureReal_empty];positivity
open CircleSpectralPathLength CircleGroupedResidual

/-- Every positive finite mode partition gives the Gaussian movement design of
the margins theorem. Its budget includes the exact residual second moments. -/
theorem grouped (n m : ℕ) (hn : 3≤n+1) (odd : Odd (n+1)) {η δ ε : ℝ}
    (hη : 0<η) (hc : η≤1) (hδ : 0<δ) (hε : 0<ε)
    (J : ℕ) (level : ZMod (n+1)→ℕ) (rate : ℕ→ℝ)
    (cover : ∀ r, level r≤J) (pos : ∀ d, 0<rate d) (upper : ∀ d,rate d≤1)
    (floor : ∀ r, rate (level r)≤eigen 1 r) (hF : 0<groupCost (n+1) J level rate)
    (hw : width n (2*sqrt (6/δ)*groupCost (n+1) J level rate) δ ε≤sqrt m) :
    ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤δ ∧ ∀ z∈E,
      Trained n η δ ε (2*sqrt (6/δ)*groupCost (n+1) J level rate) z := by
  let U := sqrt (6/δ)*groupCost (n+1) J level rate
  have up : 0<U := mul_pos (sqrt_pos.mpr (by positivity)) hF
  have cash : 2*(2*sqrt (6/δ)*groupCost (n+1) J level rate)≤sqrt (m:ℝ) := (le_max_left ..).trans hw
  have hm : 0<m := Nat.cast_pos.mp (sqrt_pos.mp ((by dsimp [U] at up;linarith only [up] : 0<2*(2*sqrt (6/δ)*groupCost (n+1) J level rate)).trans_le cash))
  apply finite_width n m hn odd hη hc hδ hε (by positivity) hw
  apply (measureReal_mono (s₂:={z | U<groupSeed (n+1) m J level rate z}) _).trans (group_design_tail hm J level rate pos hF hδ)
  rintro z ⟨_,bad⟩
  by_contra! hz
  apply bad
  intro T
  have ar := CircleGroupedBudget.grouped_area hη hc (rawResidual (n+1) m z) T J level rate cover pos upper floor
  have rr : normalizedCoeff (rawResidual (n+1) m z) = _ := funext (fun r => normalizedCoeff_raw m r z)
  rw [rr] at ar
  exact ar.trans ((le_of_not_gt hz).trans_eq (by dsimp [U];ring))

end CircleGroupedWidth
