module

public import CircleCapInduction
public import CircleSeedIntegrability
public import CircleMoment
import all CircleCapInduction
import all CircleEscape
import all CircleEscapeBridge
import all CircleInitializationCheck
import all CircleSeedIntegrability
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

/-! Moment and screen bounds for the actual fixed-initial-cap circle learner. -/

public section
noncomputable section
namespace CircleCapMoments
open CircleEscape CircleCapInduction CircleEscapeBridge CircleInitializationCheck
open MeasureTheory ProbabilityTheory Set TopologicalSpace

private theorem initial_top (N m : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m)
    (u : Net ℂ m) : IsTopGram (gridPoint N) u (curvature (gridPoint N) u) ∧
      curvature (gridPoint N) u ≤ C N * energy u := by
  have nC : (N:ℝ)*C N = (N:ℝ)/4+4 := by
    have np : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
    unfold C
    field_simp
  have upper := gram_upper (gridPoint N) u hm (C N) (by unfold C; positivity)
    (fun w v => by rw [nC]; exact CircleAngularGeometry.grid_gated_sq_upper N hN odd w v)
  have top := curvature_isTop (gridPoint N) u (by omega) hm ⟨_, upper⟩
  exact ⟨top, top.2 upper⟩

/-- Borel dependence of the actual initial top curvature, including discontinuous
strict gates. A countable dense collection of residual vectors suffices. -/
theorem curvature_measurable (N m : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m) :
    Measurable fun ω : Seed m => curvature (gridPoint N) (initial ω) := by
  apply measurable_of_Iic
  intro L
  obtain ⟨d, dense⟩ := exists_dense_seq (Fin N → ℝ)
  let J := fun (ω : Seed m) (z : Fin N → ℝ) => jacSq (gridPoint N) (initial ω) z
  let b := fun z : Fin N → ℝ => (N:ℝ)*m*L*∑ i, (z i)^2
  have measurableJ (z : Fin N → ℝ) : Measurable fun ω => J ω z := by
    unfold J jacSq
    apply Finset.measurable_fun_sum
    intro j _
    have hw := (CircleSeedIntegrability.parameter_measurable N m 1 0 j).2
    change Measurable (fun ω : Seed m => (initial ω).w j) at hw
    apply Measurable.add
    · apply Measurable.pow_const
      exact Finset.measurable_fun_sum _ fun i _ => measurable_const.mul
        (CircleSeedIntegrability.feature_meas hw (gridPoint N i))
    · apply (Measurable.pow_const (measurable_pi_apply (j,0)) 2).mul
      apply Measurable.pow_const
      apply Measurable.norm
      exact Finset.measurable_fun_sum _ fun i _ => (measurable_const.mul
        (CircleSeedIntegrability.gate_meas hw (gridPoint N i))).smul measurable_const
  have e : (fun ω : Seed m => curvature (gridPoint N) (initial ω)) ⁻¹' Iic L =
      ⋂ k : ℕ, {ω | J ω (d k) ≤ b (d k)} := by
    ext ω
    change curvature (gridPoint N) (initial ω) ≤ L ↔ _
    rw [mem_iInter]
    have top := (initial_top N m hN odd hm (initial ω)).1
    constructor
    · intro H k
      exact (top.1 (d k)).trans (by
        have h := mul_le_mul_of_nonneg_left H (show 0 ≤ (N:ℝ)*m by positivity)
        exact mul_le_mul_of_nonneg_right h (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    · intro h
      apply top.2
      have closed : IsClosed {z | J ω z ≤ b z} := by
        apply isClosed_le <;> dsimp [J,jacSq,b] <;> fun_prop
      have contains : range d ⊆ {z | J ω z ≤ b z} := by
        rintro _ ⟨k,rfl⟩; exact h k
      intro z
      exact closure_minimal contains closed (dense z)
  rw [e]
  exact MeasurableSet.iInter fun k => measurableSet_le (measurableJ _) measurable_const

def rate (N m : ℕ) (ω : Seed m) := capRate (curvature (gridPoint N) (initial ω))

def cappedY (N m t : ℕ) (ω : Seed m) : ℝ :=
  populationMean (1/Real.sqrt m) (train N m (rate N m ω) (initial ω) t)

theorem cappedY_measurable (N m t : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m) :
    Measurable (cappedY N m t) := by
  have hr : Measurable (rate N m) := measurable_const.div
    (measurable_const.max (curvature_measurable N m hN odd hm))
  let path := fun s (ω : Seed m) => train N m (rate N m ω) (initial ω) s
  have meas (s : ℕ) : ∀ j, Measurable (fun ω => (path s ω).a j) ∧
      Measurable (fun ω => (path s ω).w j) := by
    induction s with
    | zero => exact CircleSeedIntegrability.parameter_measurable N m 1 0
    | succ s ih =>
      let u := path s
      let r := fun ω (i : Fin N) => output (1/Real.sqrt m) (u ω) (gridPoint N i) - (1+(gridPoint N i).re)
      have res i : Measurable (fun ω => r ω i) := (CircleSeedIntegrability.output_meas u
        (fun j => (ih j).1) (fun j => (ih j).2) _ _).sub measurable_const
      intro j
      constructor
      · apply (ih j).1.sub
        apply (hr.div measurable_const).mul
        exact Finset.measurable_fun_sum _ fun i _ => (res i).mul
          (CircleSeedIntegrability.feature_meas (ih j).2 _)
      · apply (ih j).2.sub
        apply ((hr.div measurable_const).mul (ih j).1).smul
        exact Finset.measurable_fun_sum _ fun i _ => ((res i).mul
          (CircleSeedIntegrability.gate_meas (ih j).2 _)).smul measurable_const
  apply measurable_const.mul
  exact Finset.measurable_fun_sum _ fun j _ => ((meas t j).1).mul (meas t j).2.norm

theorem mean_le_energy (m : ℕ) (hm : 0 < m) (n : Net ℂ m) :
    |populationMean (1/Real.sqrt m) n| ≤ Real.sqrt m * energy n / 2 := by
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have sp := Real.sqrt_pos.mpr mp
  have sum : |∑ j, n.a j*‖n.w j‖| ≤ rawEnergy n / 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have h := Finset.sum_le_sum (s := Finset.univ) (f := fun j => |n.a j*‖n.w j‖|)
      (g := fun j => ((n.a j)^2+‖n.w j‖^2)/2) (by
        intro j _
        rw [abs_mul,abs_of_nonneg (norm_nonneg _)]
        nlinarith [sq_nonneg (|n.a j|-‖n.w j‖),sq_abs (n.a j)])
    exact h.trans_eq (Finset.sum_div ..).symm
  have nonneg : 0 ≤ rawEnergy n := Finset.sum_nonneg fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [populationMean,abs_mul, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left sum (show 0 ≤ 1/Real.sqrt m/Real.pi by positivity)
  apply h.trans
  have coef : 1/Real.sqrt m/Real.pi ≤ 1/Real.sqrt m := by
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ Real.pi by linarith [Real.pi_gt_three]) (show 0 ≤ 1/Real.sqrt m by positivity)]
  apply (mul_le_mul_of_nonneg_right coef (by linarith)).trans_eq
  unfold energy
  field_simp
  nlinarith [Real.sq_sqrt mp.le]

/-- The all-seed moment envelope is uniform in the update count through the
whole certified range, including a seed-dependent choice within that range. -/
theorem endpoint_envelope (N m T : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (hT : 200*T ≤ m) :
    ∀ᵐ ω ∂seedLaw m, ∀ t ≤ T, |cappedY N m t ω| ≤
      Real.sqrt m * (energy (initial ω)+1)/2 := by
  filter_upwards [gaussian_hidden_ne_zero m] with ω nz t ht
  have cap := (circle_cap_81 N m T hN odd hm hT (initial ω) nz t ht).1
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have dt : (200:ℝ)*t ≤ m := by exact_mod_cast (Nat.le_trans (Nat.mul_le_mul_left 200 ht) hT)
  have le1 : rate N m ω ≤ 1 := by
    unfold rate capRate
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    simp
  have rise : 12*rate N m ω*t/m ≤ 1 := by
    apply (div_le_iff₀ mp).mpr
    nlinarith [mul_le_mul_of_nonneg_right le1 (Nat.cast_nonneg t)]
  have cap' : energy (train N m (rate N m ω) (initial ω) t) ≤ energy (initial ω)+1 :=
    cap.trans (add_le_add_right rise _)
  exact (mean_le_energy _ hm _).trans (by gcongr)


theorem initial_energy_coordinates (m : ℕ) (ω : Seed m) :
    rawEnergy (initial ω) = ∑ i, (ω i)^2 := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [initial, Complex.sq_norm, Complex.normSq_apply,Fin.sum_univ_three]
  ring

private theorem coord_mem (m n : ℕ) (i : Fin m × Fin 3) :
    Integrable (fun ω : Seed m => (ω i)^n) (seedLaw m) := by
  have h : MemLp (fun ω : Seed m => ω i) (n:ENNReal) (seedLaw m) :=
    (memLp_id_gaussianReal' (μ:=0) (v:=1) (n:ENNReal) (by simp)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin m × Fin 3 => gaussianReal 0 1) i)
  apply h.integrable_norm_pow'.mono' ((measurable_pi_apply i).pow_const n).aestronglyMeasurable
  exact ae_of_all _ fun ω => by simp [Real.norm_eq_abs]

/-- The fourth moment of the normalized squared parameter length uses one
scalar eighth moment, uniformly in width. The bound uses Jensen irrespective
of the dependence among summands. -/
theorem initial_energy_fourth_point (m : ℕ) (hm : 0 < m) (ω : Seed m) :
    (energy (initial ω))^4 ≤ (27/(m:ℝ))*∑ i, (ω i)^8 := by
  rw [energy,initial_energy_coordinates, div_pow]
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ)
    (f := fun i : Fin m × Fin 3 => (ω i)^2) (fun i _ => sq_nonneg _) 3
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,
    ← pow_mul] at h
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  apply (div_le_iff₀ (pow_pos mp 4)).mpr
  apply h.trans_eq
  field_simp
  ring

def eighth : ℝ := ∫ x : ℝ, x^8 ∂gaussianReal 0 1

open Polynomial in
theorem gaussian_eighth : eighth = 105 := by
  unfold eighth
  let g : ℝ → ℝ := fun t => Real.exp (t^2/2)
  have dg (t : ℝ) : HasDerivAt g (t*g t) t := by
    have h := (((hasDerivAt_id t).pow 2).div_const 2).exp
    convert h using 1 <;> dsimp [g]
    ring
  let D := fun (p : Polynomial ℝ) => p.derivative+X*p
  have next (p : Polynomial ℝ) :
      deriv (fun t => p.eval t * g t) = fun t => (D p).eval t * g t := by
    funext t
    change deriv ((fun x => p.eval x) * g) t = _
    rw [((p.hasDerivAt t).mul (dg t)).deriv]
    simp [D]; ring
  have mg : mgf (fun z : ℝ => z) (gaussianReal 0 1) = fun t => (1:Polynomial ℝ).eval t * g t := by
    rw [mgf_fun_id_gaussianReal]; ext t; simp [g]
  change (∫ x : ℝ, ((fun z : ℝ => z)^8) x ∂gaussianReal 0 1) = 105
  rw [← iteratedDeriv_mgf_zero (X := fun z : ℝ => z) (by simp),mg]
  simp only [show 8 = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))))) by decide, iteratedDeriv_succ,iteratedDeriv_zero]
  simp only [next]
  norm_num [D,g,derivative_add,derivative_mul]

private theorem envelope_fourth (m : ℕ) (hm : 0 < m) (F : Seed m → ℝ)
    (meas : Measurable F) (envelope : ∀ᵐ ω ∂seedLaw m,
      |F ω| ≤ Real.sqrt m*(energy (initial ω)+1)/2) :
    Integrable (fun ω => (F ω)^4) (seedLaw m) ∧
      ∫ ω, (F ω)^4 ∂seedLaw m ≤ (m:ℝ)^2 * (81*eighth+1)/2 := by
  let A := fun ω : Seed m => (27/(m:ℝ))*(∑ i, ω i^8)
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have hA : Integrable A (seedLaw m) :=
    (integrable_finsetSum _ (fun i _ => coord_mem m 8 i)).const_mul _
  have hX : Integrable (fun ω => (m:ℝ)^2*(A ω+1)/2) (seedLaw m) :=
    ((hA.add (integrable_const _)).const_mul _).div_const _
  have bound : ∀ᵐ ω ∂seedLaw m, |F ω|^4 ≤ (m:ℝ)^2*(A ω+1)/2 := by
    filter_upwards [envelope] with ω h
    have H := pow_le_pow_left₀ (abs_nonneg _) h 4
    have E : 0 ≤ energy (initial ω) := div_nonneg
      (Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))) mp.le
    have add := add_pow_le E (show (0:ℝ) ≤ 1 by norm_num) 4
    norm_num only [Nat.reduceSub, Nat.reducePow, one_pow] at add
    have init : (energy (initial ω))^4 ≤ A ω := initial_energy_fourth_point m hm ω
    have root : (Real.sqrt m)^4 = (m:ℝ)^2 := by
      rw [show 4=2*2 by decide,pow_mul, Real.sq_sqrt mp.le]
    rw [div_pow,mul_pow,root] at H
    nlinarith only [H, mul_le_mul_of_nonneg_left add (sq_nonneg (m:ℝ)),
      mul_le_mul_of_nonneg_left init (sq_nonneg (m:ℝ))]
  have integ : Integrable (fun ω => (F ω)^4) (seedLaw m) := by
    apply hX.mono' (meas.pow_const 4).aestronglyMeasurable
    simpa only [Real.norm_eq_abs,abs_pow] using bound
  refine ⟨integ,(integral_mono_ae integ hX ?_).trans_eq ?_⟩
  · filter_upwards [bound] with ω h
    simpa only [show ∀ x : ℝ, |x|^4 = x^4 by intro x; rw [show 4=2*2 by decide,pow_mul,sq_abs,←pow_mul]] using h
  · have ci (i : Fin m × Fin 3) : ∫ ω : Seed m, (ω i)^8 ∂seedLaw m = eighth := by
      have e := (measurePreserving_eval (fun _ : Fin m × Fin 3 => gaussianReal 0 1) i).map_eq
      rw [eighth,← e,integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
      rfl
    have ai : ∫ ω, A ω ∂seedLaw m = 81*eighth := by
      unfold A
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => coord_mem m 8 i)]
      simp [ci]
      field_simp
      ring
    rw [integral_div, integral_const_mul,integral_add hA (integrable_const _),ai]
    simp


theorem capped_fourth (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) :
    Integrable (fun ω => (cappedY N m t ω)^4) (seedLaw m) ∧
      ∫ ω, (cappedY N m t ω)^4 ∂seedLaw m ≤ (m:ℝ)^2 * (81*eighth+1)/2 :=
  envelope_fourth m hm _ (cappedY_measurable N m t (by omega) odd hm)
    ((endpoint_envelope N m t hN odd hm ht).mono (fun _ h => h t le_rfl))

/-- One exact exponential moment of a squared standard Gaussian. -/
theorem gaussian_exp_sq : ∫ x : ℝ, Real.exp (x^2/32) ∂gaussianReal 0 1 =
    Real.sqrt (16/15) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  have row (x : ℝ) : gaussianPDFReal 0 1 x • Real.exp (x^2/32) =
      (1/Real.sqrt (2*Real.pi))*Real.exp (-(15/32:ℝ)*x^2) := by
    simp only [gaussianPDFReal,NNReal.coe_one, mul_one,sub_zero,smul_eq_mul,one_div]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  simp_rw [row]
  rw [integral_const_mul,integral_gaussian]
  have den := Real.sqrt_pos.mpr (show 0 < 2*Real.pi by positivity)
  have num := Real.sq_sqrt (show 0 ≤ Real.pi/(15/32:ℝ) by positivity)
  have hsq : ((1/Real.sqrt (2*Real.pi))*Real.sqrt (Real.pi/(15/32:ℝ)))^2 = 16/15 := by
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity),num]
    field_simp
    ring
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 16/15),
    Real.sqrt_nonneg (16/15),show 0 ≤ (1/Real.sqrt (2*Real.pi))*Real.sqrt (Real.pi/(15/32:ℝ)) by positivity]

/-- At odd N≥81 the chance of rejecting is bounded exponentially in width.
The proof integrates the product of Gaussian squares at t=1/32 and uses
C_N < 3/10, independent of N. -/
theorem reject_probability (N m : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m) :
    (seedLaw m).real {ω | 1 < curvature (gridPoint N) (initial ω)} ≤ Real.exp (-(m:ℝ)/240) := by
  let X := fun ω : Seed m => ∏ i, Real.exp ((ω i)^2/32)
  have mgf : ∫ ω, X ω ∂seedLaw m = (Real.sqrt (16/15))^(m*3) := by
    unfold X seedLaw
    rw [integral_fintype_prod_eq_pow (ι := Fin m × Fin 3) (μ := gaussianReal 0 1)
      (fun x => Real.exp (x^2/32)),gaussian_exp_sq]
    simp only [Fintype.card_prod,Fintype.card_fin]
  have int : Integrable X (seedLaw m) := by
    by_contra h
    rw [integral_undef h] at mgf
    exact (ne_of_gt (pow_pos (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<16/15)) _)) mgf.symm
  have mark := mul_meas_ge_le_integral_of_nonneg
    (μ := seedLaw m) (f := X) (ae_of_all _ (fun _ => Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)))
    int (Real.exp (5*(m:ℝ)/48))
  have sub : {ω | 1 < curvature (gridPoint N) (initial ω)} ⊆ {ω | Real.exp (5*(m:ℝ)/48) ≤ X ω} := by
    intro ω hr
    have hp := (initial_top N m (by omega) odd hm (initial ω)).2
    have n81 : (81:ℝ) ≤ N := by exact_mod_cast hN
    have np : (0:ℝ)<N := by linarith
    have c : C N ≤ 3/10 := by
      unfold C
      have : (4:ℝ)/N ≤ 1/20 := (div_le_iff₀ np).mpr (by linarith)
      linarith
    have mp : (0:ℝ)<m := by exact_mod_cast hm
    have e0 : 0 ≤ energy (initial ω) := div_nonneg
      (Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))) mp.le
    have lower : 10/3 < energy (initial ω) := by
      change 1 < curvature (gridPoint N) (initial ω) at hr
      nlinarith only [hr,hp,mul_le_mul_of_nonneg_right c e0]
    rw [energy,initial_energy_coordinates] at lower
    have total := (lt_div_iff₀ mp).mp lower
    change Real.exp _ ≤ ∏ i, Real.exp _
    rw [← Real.exp_sum,← Finset.sum_div]
    exact Real.exp_le_exp.mpr (by linarith)
  have mono := measureReal_mono (μ := seedLaw m) sub
  rw [mgf] at mark
  have one : Real.sqrt (16/15) ≤ Real.exp (1/30) := by
    have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤16/15)
    have e := Real.add_one_le_exp (1/30)
    nlinarith [Real.sqrt_nonneg (16/15)]
  have big := pow_le_pow_left₀ (Real.sqrt_nonneg _) one (m*3)
  rw [← Real.exp_nat_mul] at big
  have v := (mul_le_mul_of_nonneg_left mono (Real.exp_pos (5*(m:ℝ)/48)).le).trans (mark.trans big)
  apply le_of_mul_le_mul_left (a := Real.exp (5*(m:ℝ)/48))
  · apply v.trans_eq
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  · exact Real.exp_pos _


theorem output_le_energy (m : ℕ) (hm : 0 < m) (n : Net ℂ m) (x : ℂ) (unit : ‖x‖ ≤ 1) :
    |output (1/Real.sqrt m) n x| ≤ Real.sqrt m * energy n / 2 := by
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have sp := Real.sqrt_pos.mpr mp
  have sum : |∑ j, n.a j*feature (n.w j) x| ≤ rawEnergy n/2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have h := Finset.sum_le_sum (s := Finset.univ) (f := fun j => |n.a j*feature (n.w j) x|)
      (g := fun j => ((n.a j)^2+‖n.w j‖^2)/2) (by
        intro j _
        rw [abs_mul]
        have f := CircleSeedIntegrability.feature_cap (n.w j) x unit
        nlinarith [mul_le_mul_of_nonneg_left f (abs_nonneg (n.a j)),
          sq_nonneg (|n.a j|-‖n.w j‖),sq_abs (n.a j)])
    exact h.trans_eq (Finset.sum_div ..).symm
  rw [output,abs_mul,abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left sum (show 0 ≤ 1/Real.sqrt m by positivity)).trans_eq
  unfold energy
  field_simp
  rw [Real.sq_sqrt mp.le, mul_comm]

theorem reference_envelope (N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) (ω : Seed m) :
    |reference N m b ω| ≤ 1+Real.sqrt m*energy (initial ω) := by
  let n := initial ω
  let A := Real.sqrt m*energy n/2
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have mean : |populationMean (1/Real.sqrt m) n| ≤ A := mean_le_energy _ hm _
  let f := fun i => output (1/Real.sqrt m) n (gridPoint N i)
  have fr i : |f i| ≤ A := output_le_energy _ hm _ _ (grid_norm N i).le
  have ga : |(∑ i, f i)/(N:ℝ)| ≤ A := by
    rw [abs_div, abs_of_pos np]
    apply (div_le_iff₀ np).mpr
    calc _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _ : Fin N, A := Finset.sum_le_sum fun i _ => fr i
         _ = _ := by simp [mul_comm]
  have av := (abs_sub ((∑ i, f i)/N) 1).trans (add_le_add ga (show |(1:ℝ)|≤1 by norm_num))
  change |populationMean _ n - b*((∑ i, f i)/N-1)| ≤ _
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hb]
  have Apos := (abs_nonneg _).trans mean
  have H := mul_le_mul hb' av (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  dsimp [A,n] at mean H
  linarith

theorem reference_measurable (N m : ℕ) (b : ℝ) : Measurable (reference N m b) := by
  unfold reference
  let u := fun ω : Seed m => initial ω
  have ih := CircleSeedIntegrability.parameter_measurable N m 1 0
  have a (j : Fin m) : Measurable fun ω => (u ω).a j := (ih j).1
  have w (j : Fin m) : Measurable fun ω => (u ω).w j := (ih j).2
  apply Measurable.sub
  · apply measurable_const.mul
    exact Finset.measurable_fun_sum _ fun j _ => (a j).mul (w j).norm
  · apply measurable_const.mul
    apply Measurable.sub _ measurable_const
    apply Measurable.div _ measurable_const
    exact Finset.measurable_fun_sum _ fun i _ => CircleSeedIntegrability.output_meas u a w _ _

/-- Full Gaussian fourth moment of the *paired error*, at either the finite
or limiting reference coefficient, uniform for all caps in the given range. -/
theorem paired_fourth (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    Integrable (fun ω => (cappedY N m t ω-reference N m b ω)^4) (seedLaw m) ∧
      ∫ ω, (cappedY N m t ω-reference N m b ω)^4 ∂seedLaw m ≤
        128*(m:ℝ)^2*(81*eighth+1) := by
  let F := fun ω => cappedY N m t ω-reference N m b ω
  have hZ := reference_measurable N m b
  have meas := (cappedY_measurable N m t (by omega) odd hm).sub hZ
  have env : ∀ᵐ ω ∂seedLaw m, |F ω/4| ≤ Real.sqrt m*(energy (initial ω)+1)/2 := by
    filter_upwards [endpoint_envelope N m t hN odd hm ht] with ω h
    have z := reference_envelope N m (by omega) hm b hb hb' ω
    have f := (abs_sub _ _).trans (add_le_add (h t le_rfl) z)
    have root : 1 ≤ Real.sqrt m := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast (show 1 ≤ m by omega)
    have p : 0 ≤ energy (initial ω) := div_nonneg (Finset.sum_nonneg fun j _ =>
      add_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg m)
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
    dsimp [F]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (m:ℝ)) p]
  obtain ⟨int,h⟩ := envelope_fourth m hm (fun ω => F ω/4) (meas.div_const 4) env
  have rat (ω : Seed m) : (F ω)^4 = 256*(F ω/4)^4 := by ring
  change Integrable (fun ω => (F ω)^4) _ ∧ ∫ ω, (F ω)^4 ∂seedLaw m ≤ _
  simp only [rat, integral_const_mul]
  exact ⟨int.const_mul _,by linarith⟩


def screen (N m : ℕ) : Set (Seed m) :=
  {ω | curvature (gridPoint N) (initial ω) ≤ 1}

theorem screen_measurable (N m : ℕ) (hN : 3 ≤ N) (odd : Odd N) (hm : 0 < m) :
    MeasurableSet (screen N m) := measurableSet_le (curvature_measurable N m hN odd hm) measurable_const

theorem screen_probability (N m : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m) :
    1-Real.exp (-(m:ℝ)/240) ≤ (seedLaw m).real (screen N m) ∧
      0 < (seedLaw m).real (screen N m) := by
  have rej := reject_probability N m hN odd hm
  have ident : (screen N m)ᶜ = {ω | 1 < curvature (gridPoint N) (initial ω)} := by
    ext ω; simp [screen]
  rw [← ident,measureReal_compl (screen_measurable N m (by omega) odd hm),probReal_univ] at rej
  have mpos : (0:ℝ)<m := by exact_mod_cast hm
  have small : Real.exp (-(m:ℝ)/240) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  exact ⟨by linarith,by linarith⟩

def fixedSq (N m t : ℕ) (b : ℝ) := pairedSquare N m t (fun _ => 1) initial (reference N m b)

def cappedSq (N m t : ℕ) (b : ℝ) (ω : Seed m) := (cappedY N m t ω-reference N m b ω)^2

theorem cappedSq_mem (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    MemLp (cappedSq N m t b) 2 (seedLaw m) := by
  have meas := ((cappedY_measurable N m t (by omega) odd hm).sub (reference_measurable N m b)).pow_const 2
  apply (memLp_two_iff_integrable_sq meas.aestronglyMeasurable).2
  simpa only [Pi.sub_apply, ← pow_mul] using (paired_fourth N m t hN odd hm ht b hb hb').1

/-- Price of omitting any set of exceptional initializations from a pathwise
tracking calculation. The resulting unnormalized *squared* error is uniform
in the finite update count throughout the stated cap. -/
theorem exceptional_mse (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) (B : Set (Seed m)) :
    ∫ ω in B, cappedSq N m t b ω ∂seedLaw m ≤ 1044*m*Real.sqrt ((seedLaw m).real B) := by
  let F := fun ω => cappedY N m t ω-reference N m b ω
  have fourth := (paired_fourth N m t hN odd hm ht b hb hb').2
  rw [gaussian_eighth] at fourth
  have h := CircleMoment.exceptional_second_moment (F := F) (cappedSq_mem N m t hN odd hm ht b hb hb') B
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply (Real.sqrt_le_left (by positivity)).mpr
  apply fourth.trans
  nlinarith [sq_nonneg (m:ℝ)]

theorem conditional_mse (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) :
    (∫ ω in screen N m, fixedSq N m t b ω ∂seedLaw m) / (seedLaw m).real (screen N m) ≤
      (∫ ω, cappedSq N m t b ω ∂seedLaw m) / (1-Real.exp (-(m:ℝ)/240)) := by
  have p := screen_probability N m hN odd hm
  have int := (cappedSq_mem N m t hN odd hm ht b hb hb').integrable one_le_two
  have res := (restricted_mse (seedLaw m) N m t (fun ω => curvature (gridPoint N) (initial ω))
    initial (reference N m b) (screen_measurable N m (by omega) odd hm) int).2
  have prob : 0 < 1-Real.exp (-(m:ℝ)/240) := by
    have hp : (0:ℝ)<m := by exact_mod_cast hm
    linarith [Real.exp_lt_one_iff.mpr (show -(m:ℝ)/240 < 0 by linarith)]
  exact div_le_div₀ (integral_nonneg fun ω => sq_nonneg _) res prob p.1

/-- For any measurable event, the part of its ordinary endpoint squared error
on accepted seeds is bounded by the full capped MSE. The rest is exactly the
ordinary contribution on rejected seeds in that event. In particular this
applies to a successful-fit event without inferring anything about its rejected
part. -/
theorem event_mse_split (N m t : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m)
    (ht : 200*t ≤ m) (b : ℝ) (hb : 0 ≤ b) (hb' : b ≤ 1) (F : Set (Seed m))
    (hF : MeasurableSet F) :
    0 ≤ (∫ ω in F, fixedSq N m t b ω ∂seedLaw m) -
        (∫ ω in F \ screen N m, fixedSq N m t b ω ∂seedLaw m) ∧
    (∫ ω in F, fixedSq N m t b ω ∂seedLaw m) -
        (∫ ω in F \ screen N m, fixedSq N m t b ω ∂seedLaw m) ≤
          ∫ ω, cappedSq N m t b ω ∂seedLaw m := by
  let E := screen N m
  let μ := seedLaw m
  let S := fixedSq N m t b
  have e : MeasurableSet E := screen_measurable N m (by omega) odd hm
  have fixed : Integrable S μ := ((CircleSeedIntegrability.trained_memLp N m t 1 2 (by norm_num)).sub
    (CircleSeedIntegrability.reference_memLp N m b 2 (by norm_num))).integrable_sq
  have split : (∫ ω in F, S ω ∂μ) = (∫ ω in F∩E, S ω ∂μ)+(∫ ω in F\E, S ω ∂μ) := by
    have union : (F∩E) ∪ (F\E) = F := by ext; simp
    nth_rw 1 [← union]
    apply setIntegral_union _ (hF.diff e) fixed.integrableOn fixed.integrableOn
    exact Set.disjoint_left.mpr (fun _ h₁ h₂ => h₂.2 h₁.2)
  have ci := (cappedSq_mem N m t hN odd hm ht b hb hb').integrable one_le_two
  have res := (restricted_mse μ N m t (fun ω => curvature (gridPoint N) (initial ω))
    initial (reference N m b) e ci).2
  change 0 ≤ (∫ ω in F,S ω ∂μ)-(∫ ω in F\E,S ω ∂μ) ∧ _ ≤ _
  rw [split,add_sub_cancel_right]
  refine ⟨setIntegral_nonneg (hF.inter e) (fun _ _ => sq_nonneg _),?_⟩
  exact (setIntegral_mono_set fixed.integrableOn
    (ae_of_all _ fun _ => sq_nonneg _) (Set.inter_subset_right (s := F) (t := E)).eventuallySubset).trans res


/-- Every seed with all scalar coordinates in [2,3] rejects, giving a
dimension-independent lower exponential as well as the upper exponential. -/
theorem reject_lower (N m : ℕ) (hN : 81 ≤ N) (odd : Odd N) (hm : 0 < m) :
    Real.exp (-20*(m:ℝ)) ≤ (seedLaw m).real {ω | 1 < curvature (gridPoint N) (initial ω)} := by
  have mp : (0:ℝ)<m := by exact_mod_cast hm
  have n81 : (81:ℝ) ≤ N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  have q : (7:ℝ)/24 ≤ 1/Real.pi-2/N := by
    have a : (2:ℝ)/N ≤ 2/81 := (div_le_iff₀ np).mpr (by linarith)
    have b : (7:ℝ)/22 ≤ 1/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_d4])
    linarith
  have nq : (N:ℝ)*(1/Real.pi-2/N) = N/Real.pi-2 := by field_simp
  have sub : box m 1 false ⊆ {ω | 1 < curvature (gridPoint N) (initial ω)} := by
    intro ω boxw
    have coord (i : Fin m × Fin 3) : 2 ≤ ω i := by
      simpa [boxInterval] using (boxw i (mem_univ i)).1
    have nz (j : Fin m) : (initial ω).w j ≠ 0 := by
      intro h
      have zero : ω (j,1) = 0 := congrArg Complex.re h
      linarith [coord (j,1)]
    have E : 12 ≤ energy (initial ω) := by
      rw [energy,initial_energy_coordinates]
      apply (le_div_iff₀ mp).mpr
      have H := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin m × Fin 3 => (4:ℝ))
        (g := fun i => (ω i)^2) (fun i _ => by
          nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤2) (coord i)])
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at H
      linarith
    have gram := ((initial_top N m (by omega) odd hm (initial ω)).1).1
    have low := gram_lower (gridPoint N) (initial ω) (by omega) hm (1/Real.pi-2/N) _
      (by linarith) nz (fun w => by rw [nq]; exact CircleAngularGeometry.grid_mean_lower N (by omega) w) gram
    have sq := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤7/24) q 2
    have total := mul_le_mul sq E (by norm_num : (0:ℝ)≤12) (sq_nonneg _)
    change 1 < _
    linarith
  have den : Real.sqrt (2*Real.pi) ≤ Real.exp 2 := by
    have d : Real.sqrt (2*Real.pi) ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
    linarith [Real.add_one_le_exp 2]
  have pdf : Real.exp (-(13:ℝ)/2) ≤ gaussianPDFReal 0 1 3 := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    calc
      Real.exp (-(13:ℝ)/2) = (Real.exp 2)⁻¹ * Real.exp (-(3:ℝ)^2/2) := by
        rw [← Real.exp_neg,← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (inv_anti₀ (Real.sqrt_pos.mpr (by positivity)) den) (Real.exp_pos _).le
  have mass := signed_gaussian_mass m 1 (by norm_num) false
  norm_num only [mul_one,one_mul] at mass
  calc
    Real.exp (-20*(m:ℝ)) ≤ Real.exp ((3*m:ℕ)*(-(13:ℝ)/2)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    _ = (Real.exp (-(13:ℝ)/2))^(3*m) := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le pdf _
    _ ≤ _ := mass.trans (measureReal_mono sub)

end CircleCapMoments
