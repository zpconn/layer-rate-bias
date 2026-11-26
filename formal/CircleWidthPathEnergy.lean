module

public import CircleWidthMoment
public import CircleCapMoments
import all CircleEscape
import all CircleEscapeBridge
import all CircleCapInduction
import all CircleCapMoments
import all CircleFlowMoments
import all CircleInitializationCheck
import all CircleSeedIntegrability
import all CircleWidthMoment
import Mathlib.Tactic

/-! Pointwise energy growth of every ordinary fixed-step circle network. -/
@[expose] public section
noncomputable section
namespace CircleWidthPathEnergy
open Real MeasureTheory CircleEscape CircleEscapeBridge CircleInitializationCheck
  CircleCapInduction CircleCapMoments CircleSeedIntegrability CircleWidthMoment
variable {N m : ℕ}

theorem actual_step {η : ℝ} (hη : 0≤η) (hc : η≤1) (hn : 0<N) (hm : 0<m) (z : Net ℂ m) :
    4+2*energy (step (gridPoint N) (fun i => 1+(gridPoint N i).re) (1/sqrt m) (η/(N*sqrt m)) z)
      ≤ (4+2*energy z)^3 := by
  let M := energy z
  let k := η/((N:ℝ)*sqrt m)
  let A := sqrt (m:ℝ)*M/2+2
  let g := 2+M/2
  let r (i : Fin N) := output (1/sqrt m) z (gridPoint N i)-(1+(gridPoint N i).re)
  let z' := step (gridPoint N) (fun i => 1+(gridPoint N i).re) (1/sqrt m) k z
  have mp : (0:ℝ)<m := Nat.cast_pos.mpr hm
  have np : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have sp : 0<sqrt (m:ℝ) := sqrt_pos.mpr mp
  have s1 : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  have ep : 0≤M := by dsimp [M,energy,rawEnergy];positivity
  have gp : 0≤g := by dsimp [g];positivity
  have Ap : 0≤A := by dsimp [A];positivity
  have hr (i) : |r i|≤A := (abs_sub _ _).trans (add_le_add
    (output_le_energy _ hm _ _ (grid_norm N i).le) (CircleFlowMoments.circle_label_abs N i))
  have mult : |k| *N*A≤g := by
    rw [abs_of_nonneg (by dsimp [k];positivity)]
    calc k*N*A = η*(A/sqrt m) := by dsimp [k];field_simp
         _ ≤ A/sqrt m := mul_le_of_le_one_left (by positivity) hc
         _ ≤ g := by apply (div_le_iff₀ sp).mpr;dsimp [A,g];nlinarith only [s1]
  have neuron (j : Fin m) : (z'.a j)^2+‖z'.w j‖^2 ≤ (1+g)^2*((z.a j)^2+‖z.w j‖^2) := by
    have a := sum_norm_cap (fun i => r i*feature (z.w j) (gridPoint N i)) (A*‖z.w j‖) (by
      intro i;rw [Real.norm_eq_abs,abs_mul];exact mul_le_mul (hr i) (feature_cap _ _ (grid_norm N i).le) (abs_nonneg _) Ap)
    have w := sum_norm_cap (fun i => (r i*gate (z.w j) (gridPoint N i)) • gridPoint N i) A (by
      intro i;rw [norm_smul,Real.norm_eq_abs,abs_mul,grid_norm,mul_one]
      have one : |gate (z.w j) (gridPoint N i)|≤1 := by unfold gate;split <;> norm_num
      simpa only [mul_one] using mul_le_mul (hr i) one (abs_nonneg _) Ap)
    simp only [Fintype.card_fin,Real.norm_eq_abs] at a w
    have aa : |z'.a j| ≤ |z.a j|+g*‖z.w j‖ := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      have b := mul_le_mul_of_nonneg_left a (abs_nonneg k)
      have c := mul_le_mul_of_nonneg_right mult (norm_nonneg (z.w j))
      change _+|k| * |∑ i, r i*feature (z.w j) (gridPoint N i)|≤_
      nlinarith only [b,c]
    have ww : ‖z'.w j‖ ≤ ‖z.w j‖+g* |z.a j| := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul,Real.norm_eq_abs,abs_mul]
      have b := mul_le_mul_of_nonneg_left w (mul_nonneg (abs_nonneg k) (abs_nonneg (z.a j)))
      have c := mul_le_mul_of_nonneg_right mult (abs_nonneg (z.a j))
      change _+(|k| * |z.a j|)*‖∑ i, (r i*gate (z.w j) (gridPoint N i)) • gridPoint N i‖≤_
      nlinarith only [b,c]
    have ai := pow_le_pow_left₀ (abs_nonneg _) aa 2
    have wi := pow_le_pow_left₀ (norm_nonneg _) ww 2
    rw [sq_abs] at ai
    calc _ ≤ (|z.a j|+g*‖z.w j‖)^2+(‖z.w j‖+g* |z.a j|)^2 := add_le_add ai wi
         _ ≤ _ := by nlinarith only [mul_nonneg gp (sq_nonneg (|z.a j|-‖z.w j‖)),sq_abs (z.a j),
           show (1+g)^2* |z.a j|^2 = (1+g)^2*(z.a j)^2 by rw [sq_abs]]
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => neuron j)
  rw [←Finset.mul_sum] at sum
  have e : energy z'≤(1+g)^2*M := (div_le_div_of_nonneg_right sum mp.le).trans_eq (by dsimp [M,energy,rawEnergy];ring)
  change 4+2*energy z'≤(4+2*M)^3
  dsimp [g] at e
  nlinarith only [e,ep,sq_nonneg M,mul_nonneg (sq_nonneg M) ep]

theorem actual_path {η : ℝ} (hη : 0≤η) (hc : η≤1) (hn : 0<N) (hm : 0<m) (z : Net ℂ m) (T : ℕ) :
    4+2*energy (train N m η z T) ≤ (4+2*energy z)^(3^T) := by
  induction T with
  | zero => simp [train]
  | succ t ih =>
    rw [pow_succ 3,pow_mul]
    apply (actual_step hη hc hn hm (train N m η z t)).trans
    apply pow_le_pow_left₀ _ ih
    unfold energy rawEnergy;positivity

theorem actual_paired {η b : ℝ} (hη : 0≤η) (hc : η≤1) (hn : 0<N) (hm : 0<m)
    (hb : 0≤b) (h1 : b≤1) (T : ℕ) (ω : Seed m) :
    |rawError N m T η b ω|≤2*sqrt (m:ℝ)*(4+2*energy (initial ω))^(3^T) := by
  let M := energy (initial ω)
  let P := (4+2*M)^(3^T)
  have ep : 0≤M := by dsimp [M,energy,rawEnergy];positivity
  have e0 : 1≤4+2*M := by linarith
  have ub : 4+2*M≤P := by
    simpa only [pow_one] using pow_le_pow_right₀ e0 (Nat.one_le_pow _ _ (by decide : 0<3) : 1≤3^T)
  have sp : 0≤sqrt (m:ℝ) := sqrt_nonneg _
  have sr : 1≤sqrt (m:ℝ) := one_le_sqrt.mpr (by exact_mod_cast hm)
  have y := mean_le_energy m hm (train N m η (initial ω) T)
  have z := reference_envelope N m hn hm b hb h1 ω
  have e := actual_path hη hc hn hm (initial ω) T
  apply (abs_sub _ _).trans
  change |populationMean _ (train N m η (initial ω) T)| + |reference N m b ω|≤2*sqrt (m:ℝ)*P
  change 4+2*energy (train N m η (initial ω) T)≤P at e
  change |reference N m b ω|≤1+sqrt (m:ℝ)*M at z
  nlinarith only [y,z,mul_le_mul_of_nonneg_left ub sp,mul_le_mul_of_nonneg_left e sp,sr,mul_nonneg sp ep]
end CircleWidthPathEnergy
