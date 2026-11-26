module

public import CircleGaussianBernstein
import all CircleInitializationConcentration
import all CircleTangentDrift
import all CircleGaussianBernstein
import Mathlib.Tactic

/-! The sharper concentration constant for ordinary simultaneous training.
For equal multipliers the two parts of an initial tangent entry are bounded
by the energy of the hidden weights and the squared readout separately. -/
@[expose] public section
noncomputable section
namespace CircleWidthInitTail
open Real MeasureTheory ProbabilityTheory CircleTangentDrift CircleEscapeBridge
  CircleInitializationConcentration CircleGaussianBernstein CircleGridSpectrum CircleFlowPath

theorem unit_mark (x y : ℝ×ℝ) (hx : UnitInput x) (hy : UnitInput y) (z : Atom) :
    |weightedAtom 1 x y z| ≤ atomEnergy z := by
  let A := z 1^2+z 2^2
  have A0 : 0≤A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have feat (x : ℝ×ℝ) (hx : UnitInput x) :
      |max (x.1*z 1+x.2*z 2) 0|≤sqrt A := by
    rw [abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (sqrt_nonneg _)
    apply (le_abs_self _).trans
    apply (le_sqrt (abs_nonneg _) A0).mpr
    rw [sq_abs]
    have p := mul_le_mul_of_nonneg_right hx A0
    dsimp [A] at p ⊢
    nlinarith only [p,sq_nonneg (x.1*z 2-x.2*z 1)]
  let p := x.1*z 1+x.2*z 2
  let q := y.1*z 1+y.2*z 2
  have gate (a : ℝ) : |actualGate a|≤1 := by unfold actualGate;split <;> norm_num
  have absG : |actualGate p*actualGate q|≤1 := by
    rw [abs_mul];simpa using mul_le_mul (gate p) (gate q) (abs_nonneg _) zero_le_one
  have zw : |max p 0*max q 0|≤A := by
    rw [abs_mul]
    exact (mul_le_mul (feat x hx) (feat y hy) (abs_nonneg _) (sqrt_nonneg _)).trans_eq (by rw [←sq,sq_sqrt A0])
  have za : |1*(z 0*z 0)*(actualGate p*actualGate q)*dot x y| ≤ z 0^2 := by
    rw [one_mul,abs_mul,abs_mul,abs_of_nonneg (mul_self_nonneg _)]
    have d := mul_le_mul absG (dot_bound hx hy) (abs_nonneg _) zero_le_one
    rw [mul_one] at d
    rw [mul_assoc,←sq]
    exact mul_le_of_le_one_right (sq_nonneg _) d
  exact (abs_add_le ..).trans ((add_le_add zw za).trans_eq (by dsimp [A,atomEnergy];ring))

theorem init_marks (N : ℕ) (ρ : ℝ) (q : InitIndex N) (z : Atom) :
    |initTest N 1 ρ q z|≤atomEnergy z := by
  have margin (t : ℝ) (a : Atom) : |marginAtom ρ (phase t) a| ≤ 1*atomEnergy a := by
    simpa using CircleInitializationConcentration.margin_cap ρ (phase t) a
  rcases q with _ | (i | ⟨j,i⟩)
  · exact (abs_of_nonneg (atomEnergy_nonneg z)).le
  · cases i with
    | none => simpa only [initTest,one_mul] using CircleInitializationConcentration.angle_cap margin z
    | some i => exact CircleInitializationConcentration.margin_cap ρ _ z
  · cases i with
    | none =>
      have bnd (t : ℝ) (a : Atom) : |weightedAtom 1 (phase t) (circleInput N j) a|≤1*atomEnergy a := by
        simpa only [one_mul] using unit_mark _ _ (phase_unit t) (grid_unit j) a
      simpa only [initTest,one_mul] using CircleInitializationConcentration.angle_cap bnd z
    | some i => exact unit_mark _ _ (grid_unit i) (grid_unit j) z

theorem good_init {m N : ℕ} [NeZero N] (hm : 0<m) {ρ u : ℝ}
    (hρ : 0≤ρ) (hr : ρ≤1) (hu : 0≤u) (hc : u≤1) :
    (seedLaw m).real {ω | ¬GoodInit 1 ρ u (sampledMatrix 1) (fun _ : Fin N => CircleSpectrum.k0 1) ω} ≤
      ((N+1:ℝ)^2+1)*(2*exp (-(m:ℝ)*u^2/4096)) := by
  simpa only [populationGram_sampled,funext (populationMeanRow_constant (N:=N) 1)] using
    goodInit_failure_of_tests (N:=N) hm hρ hr hu hc (fun q => two_sided hm _
      (initTest_meas N 1 ρ q) (fun z => (init_marks N ρ q z).trans_eq (by
        simp [energy,atomEnergy,Fin.sum_univ_three,add_assoc])) hu (by linarith))
end CircleWidthInitTail
