module

public import NonlinearBudget
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
import Mathlib.Analysis.Real.Pi.Bounds

/-! Row estimates for a two-layer network in its whitened coordinates. -/
@[expose] public section
noncomputable section
namespace TwoLayerBudget
open NonlinearBudget MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

def leaky (α z : ℝ) : ℝ := if 0 ≤ z then z else α*z

def Slope (α z s : ℝ) : Prop :=
  α ≤ s ∧ s ≤ 1 ∧ (0 < z → s = 1) ∧ (z < 0 → s = α)

private theorem slope_agree {α z z' s s' : ℝ} (h : Slope α z s) (h' : Slope α z' s')
    (sgn : 0 < z*z') : s = s' := by
  rcases mul_pos_iff.mp sgn with ⟨p,q⟩ | ⟨p,q⟩
  · rw [h.2.2.1 p,h'.2.2.1 q]
  · rw [h.2.2.2 p,h'.2.2.2 q]

theorem leaky_lipschitz (α z z' : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    |leaky α z-leaky α z'| ≤ |z-z'| := by
  unfold leaky
  split_ifs with h k k
  · rfl
  · have k' := le_of_not_ge k
    rw [abs_of_nonneg (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα k'] : 0≤z-α*z'),
      abs_of_nonneg (by linarith : 0≤z-z')]
    nlinarith [mul_le_mul_of_nonpos_right hα' k']
  · have h' := le_of_not_ge h
    rw [abs_of_nonpos (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα h'] : α*z-z'≤0),
      abs_of_nonpos (by linarith : z-z'≤0)]
    nlinarith [mul_le_mul_of_nonpos_right hα' h']
  · rw [← mul_sub,abs_mul,abs_of_nonneg hα]
    simpa using mul_le_mul_of_nonneg_right hα' (abs_nonneg (z-z'))

/-- x is a unit input direction, b its original length. -/
def pred (φ : ℝ → ℝ) (b : ℝ) (x : V) (a : Fin n → ℝ) (w : Fin n → V) : ℝ :=
  (∑ i, a i * φ (b*inner ℝ (w i) x))/Real.sqrt n

/-- The width-scaled squared Euclidean distance between two full Jacobian
rows: the readout-column changes plus all hidden-coordinate changes. -/
def rowDiff (φ : ℝ → ℝ) (b : ℝ) (x : V) (a₀ a : Fin n → ℝ) (w₀ w : Fin n → V)
    (s₀ s : Fin n → ℝ) : ℝ :=
  ∑ i, ((φ (b*inner ℝ (w i) x)-φ (b*inner ℝ (w₀ i) x))^2 +
    ‖(b*(a i*s i-a₀ i*s₀ i)) • x‖^2)

private theorem pre_move (x w v : V) (hx : ‖x‖ ≤ 1) :
    |inner ℝ w x - inner ℝ v x| ≤ ‖w-v‖ := by
  rw [← inner_sub_left]
  exact (abs_real_inner_le_norm _ _).trans (by simpa using mul_le_mul_of_nonneg_left hx (norm_nonneg (w-v)))

/-- Algebraic derivative-row estimate shared by smooth and nonsmooth models.
It also applies to interval secant slopes on a two-layer forward chord. -/
theorem row_diff_bound (φ : ℝ → ℝ) (b L M R : ℝ) (hb : 0 ≤ b)
    (hl : 0 ≤ L) (hM : 0 ≤ M) (lip : ∀ u v, |φ u-φ v| ≤ L*|u-v|)
    (x : V) (hx : ‖x‖ ≤ 1) (a₀ a : Fin n → ℝ) (w₀ w : Fin n → V)
    (s₀ s : Fin n → ℝ) (cap : ∀ i, |a₀ i| ≤ M) (sl : ∀ i, |s i| ≤ L)
    (radius : ∑ i, ((a i-a₀ i)^2+‖w i-w₀ i‖^2) ≤ R^2) :
    rowDiff φ b x a₀ a w₀ w s₀ s ≤ 2*b^2*(L^2*R^2+M^2*∑ i,(s i-s₀ i)^2) := by
  have point (i : Fin n) :
      (φ (b*inner ℝ (w i) x)-φ (b*inner ℝ (w₀ i) x))^2+
        ‖(b*(a i*s i-a₀ i*s₀ i)) • x‖^2 ≤
      2*b^2*(L^2*((a i-a₀ i)^2+‖w i-w₀ i‖^2)+M^2*(s i-s₀ i)^2) := by
    have act := lip (b*inner ℝ (w i) x) (b*inner ℝ (w₀ i) x)
    rw [← mul_sub,abs_mul,abs_of_nonneg hb] at act
    have A := pow_le_pow_left₀ (abs_nonneg _) (act.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pre_move x _ _ hx) hb) hl)) 2
    rw [sq_abs] at A
    have strip : a i*s i-a₀ i*s₀ i = (a i-a₀ i)*s i+a₀ i*(s i-s₀ i) := by ring
    have coeff := pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le ((a i-a₀ i)*s i) (a₀ i*(s i-s₀ i))).trans
      (add_le_add (by simpa [abs_mul] using mul_le_mul_of_nonneg_left (sl i) (abs_nonneg (a i-a₀ i)))
        (by simpa [abs_mul] using mul_le_mul_of_nonneg_right (cap i) (abs_nonneg (s i-s₀ i))))) 2
    rw [sq_abs,← strip] at coeff
    have split := add_pow_le (mul_nonneg (abs_nonneg (a i-a₀ i)) hl)
      (mul_nonneg hM (abs_nonneg (s i-s₀ i))) 2
    norm_num only [Nat.reduceSub, pow_one, mul_pow,sq_abs] at split
    have hidden := mul_le_mul_of_nonneg_left (coeff.trans split) (sq_nonneg b)
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_pow]
    have xx := pow_le_pow_left₀ (norm_nonneg x) hx 2
    rw [one_pow] at xx
    have xc := mul_le_mul_of_nonneg_left xx (mul_nonneg (sq_nonneg b) (sq_nonneg (a i*s i-a₀ i*s₀ i)))
    nlinarith only [A,hidden,xc,mul_nonneg (sq_nonneg b) (mul_nonneg (sq_nonneg L) (sq_nonneg ‖w i-w₀ i‖))]
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => point i)
  unfold rowDiff
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total radius ⊢
  change _ ≤ _
  apply le_trans total
  gcongr

theorem smooth_row (φ g : ℝ → ℝ) (b L₁ L₂ M R : ℝ) (hb : 0 ≤ b) (h1 : 0 ≤ L₁)
    (h2 : 0 ≤ L₂) (hM : 0 ≤ M) (lip : ∀ u v, |φ u-φ v| ≤ L₁*|u-v|)
    (glip : ∀ u v, |g u-g v| ≤ L₂*|u-v|) (gb : ∀ u, |g u| ≤ L₁)
    (x : V) (hx : ‖x‖ ≤ 1) (a₀ a : Fin n → ℝ) (w₀ w : Fin n → V)
    (cap : ∀ i, |a₀ i| ≤ M) (radius : ∑ i, ((a i-a₀ i)^2+‖w i-w₀ i‖^2) ≤ R^2) :
    rowDiff φ b x a₀ a w₀ w (fun i => g (b*inner ℝ (w₀ i) x)) (fun i => g (b*inner ℝ (w i) x))
      ≤ 2*b^2*R^2*(L₁^2+M^2*L₂^2*b^2) := by
  have row := row_diff_bound φ b L₁ M R hb h1 hM lip x hx a₀ a w₀ w
    (fun i => g (b*inner ℝ (w₀ i) x)) (fun i => g (b*inner ℝ (w i) x))
    cap (fun i => gb _) radius
  have aux (i : Fin n) : (g (b*inner ℝ (w i) x)-g (b*inner ℝ (w₀ i) x))^2 ≤
      (L₂*b)^2*((a i-a₀ i)^2+‖w i-w₀ i‖^2) := by
    have h := glip (b*inner ℝ (w i) x) (b*inner ℝ (w₀ i) x)
    rw [←mul_sub,abs_mul,abs_of_nonneg hb] at h
    have g := pow_le_pow_left₀ (abs_nonneg _) (h.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pre_move x _ _ hx) hb) h2)) 2
    rw [sq_abs] at g
    nlinarith [mul_nonneg (sq_nonneg (L₂*b)) (sq_nonneg (a i-a₀ i))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => aux i)
  rw [← Finset.mul_sum] at hsum
  have drift := hsum.trans (mul_le_mul_of_nonneg_left radius (sq_nonneg _))
  apply row.trans
  nlinarith only [mul_le_mul_of_nonneg_left drift (mul_nonneg (sq_nonneg b) (sq_nonneg M))]


/-- Uniformly on a full displacement ball, all slope assignments at kinks
obey this bound. The count at initialization is fixed while the endpoint and
its possibly adversarial kink selections range over the whole ball. -/
theorem leaky_row (α b M R ε : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (hb : 0 < b)
    (hM : 0 ≤ M) (hε : 0 < ε) (x : V) (hx : ‖x‖ ≤ 1)
    (a₀ a : Fin n → ℝ) (w₀ w : Fin n → V) (s₀ s : Fin n → ℝ)
    (sinit : ∀ i, Slope α (b*inner ℝ (w₀ i) x) (s₀ i))
    (snew : ∀ i, Slope α (b*inner ℝ (w i) x) (s i))
    (cap : ∀ i, |a₀ i| ≤ M) (radius : ∑ i, ((a i-a₀ i)^2+‖w i-w₀ i‖^2) ≤ R^2) :
    let near := Finset.univ.filter (fun i => |inner ℝ (w₀ i) x| ≤ ε)
    rowDiff (leaky α) b x a₀ a w₀ w s₀ s ≤
      2*b^2*(R^2+M^2*(1-α)^2*((near.card:ℝ)+R^2/ε^2)) := by
  classical
  intro near
  let z₀ := fun i => inner ℝ (w₀ i) x
  let z := fun i => inner ℝ (w i) x
  let cross := Finset.univ.filter (fun i => z₀ i*z i ≤ 0)
  have count : (cross.card:ℝ) ≤ near.card + R^2/ε^2 :=
    gate_count z₀ z (fun i => ‖w i-w₀ i‖) ε R hε (fun i => pre_move x _ _ hx)
      ((Finset.sum_le_sum (fun i _ => le_add_of_nonneg_left (sq_nonneg (a i-a₀ i)))).trans radius)
  have slopeCap : ∑ i, (s i-s₀ i)^2 ≤ (1-α)^2*cross.card := by
    have each (i : Fin n) : (s i-s₀ i)^2 ≤ if z₀ i*z i ≤ 0 then (1-α)^2 else 0 := by
      split_ifs with h
      · have bound : |s i-s₀ i| ≤ 1-α := abs_le.mpr ⟨by linarith [(snew i).1,(sinit i).2.1],
          by linarith [(snew i).2.1,(sinit i).1]⟩
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) bound 2
      · have prod : 0 < (b*z₀ i)*(b*z i) := by
          nlinarith [mul_pos (sq_pos_of_pos hb) (lt_of_not_ge h)]
        rw [slope_agree (sinit i) (snew i) prod]; simp
    apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)).trans_eq
    rw [← Finset.sum_filter]
    simp [cross,mul_comm]
  have row := row_diff_bound (leaky α) b 1 M R hb.le (by norm_num) hM
    (fun v w => by simpa using leaky_lipschitz α v w hα hα') x hx a₀ a w₀ w s₀ s cap
    (fun i => by rw [abs_of_nonneg (hα.trans (snew i).1)]; exact (snew i).2.1) radius
  have extra := slopeCap.trans (mul_le_mul_of_nonneg_left count (sq_nonneg _))
  simp only [one_pow,one_mul] at row
  apply row.trans
  nlinarith only [mul_le_mul_of_nonneg_left extra (mul_nonneg (sq_nonneg b) (sq_nonneg M))]

/-- The count/width balance at ε=n^(-1/3), written with u=cuberoot(n);
the squared average contribution of crossings decays as 1/u. -/
theorem cube_cutoff (n : ℕ) (u A R count near : ℝ) (up : 0 < u) (width : (n:ℝ)=u^3)
    (nearby : near ≤ A*u^2) (crossing : count ≤ near+R^2/(1/u)^2) :
    count/n ≤ (A+R^2)/u := by
  rw [width]
  apply (div_le_iff₀ (pow_pos up 3)).mpr
  have eq : R^2/(1/u)^2 = R^2*u^2 := by field_simp
  rw [eq] at crossing
  calc _ ≤ A*u^2+R^2*u^2 := by linarith
       _ = _ := by field_simp


/-- Actual Jacobian-vector action for one example along a simultaneous movement
of the readout and all hidden units. The formula holds at every point where
the indicated scalar activation derivatives exist. -/
theorem pred_directional (φ g : ℝ → ℝ) (b : ℝ) (x : V) (a da : Fin n → ℝ)
    (w dw : Fin n → V) (diff : ∀ i, HasDerivAt φ (g (b*inner ℝ (w i) x)) (b*inner ℝ (w i) x)) :
    HasDerivAt (fun t : ℝ => pred φ b x (fun i => a i+t*da i) (fun i => w i+t • dw i))
      ((∑ i, (da i*φ (b*inner ℝ (w i) x) +
        a i*g (b*inner ℝ (w i) x)*(b*inner ℝ (dw i) x)))/Real.sqrt n) 0 := by
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro i _
  have h1 := ((hasDerivAt_id (0:ℝ)).mul_const (da i)).const_add (a i)
  let z := b*inner ℝ (w i) x
  have h2 : HasDerivAt (fun t : ℝ => b*inner ℝ (w i+t • dw i) x) (b*inner ℝ (dw i) x) 0 := by
    simp only [inner_add_left,real_inner_smul_left]
    convert (((hasDerivAt_id (0:ℝ)).mul_const (inner ℝ (dw i) x)).const_add (inner ℝ (w i) x)).const_mul b using 1
    · ext t; simp
    · simp
  have hp : HasDerivAt (fun t : ℝ => φ (b*inner ℝ (w i+t • dw i) x))
      (g z*(b*inner ℝ (dw i) x)) 0 :=
    (show HasDerivAt φ (g z) (b*inner ℝ (w i+(0:ℝ) • dw i) x) by simpa [z] using diff i).comp 0 h2
  convert h1.mul hp using 1
  · ext t; simp
  · simp [z]; ring

/-- A finite counterpart to the Gaussian small-margin count. -/
theorem gaussian_small_ball (ε : ℝ) (he : 0 ≤ ε) :
    (gaussianReal 0 1).real {x : ℝ | |x| ≤ ε} ≤ 2*ε := by
  have set : {x : ℝ | |x| ≤ ε} = Icc (-ε) ε := by ext x; simp [abs_le]
  rw [set,measureReal_def,gaussianReal_apply_eq_integral _ (by norm_num : (1:NNReal)≠0),
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc (fun _ _ => gaussianPDFReal_nonneg _ _ _))]
  have bound (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
    have coeff : (Real.sqrt (2*Real.pi))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity),Real.le_sqrt (by norm_num) (by positivity)]
      linarith [Real.pi_gt_three]
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    exact (mul_le_mul coeff (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
      (Real.exp_pos _).le (by norm_num : (0:ℝ)≤1)).trans_eq (one_mul _)
  have h := setIntegral_mono_on (s := Icc (-ε) ε) (integrable_gaussianPDFReal 0 1).integrableOn
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)) measurableSet_Icc (fun x _ => bound x)
  apply h.trans_eq
  simp [Real.volume_real_Icc_of_le (by linarith : -ε≤ε)]
  ring

/-- The margin count uses only the marginal laws of the preactivations. This
also applies to several fixed input directions with common hidden weights. -/
theorem gaussian_near_count {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Fin n → Ω → ℝ) (law : ∀ i, HasLaw (z i) (gaussianReal 0 1) μ)
    (ε A : ℝ) (hε : 0 ≤ ε) (hA : 0 < A) :
    μ.real {ω | A ≤ ((Finset.univ.filter (fun i => |z i ω| ≤ ε)).card:ℝ)} ≤ 2*n*ε/A := by
  let B := fun i => {ω | |z i ω| ≤ ε}
  let f := fun ω => ∑ i, (B i).indicator (fun _ => (1:ℝ)) ω
  have hm (i) : NullMeasurableSet (B i) μ :=
    (law i).aemeasurable.nullMeasurable (show MeasurableSet {x : ℝ | |x| ≤ ε} from
      measurableSet_le (by fun_prop : Measurable fun x : ℝ => |x|) measurable_const)
  have fi : Integrable f μ := integrable_finsetSum _ (fun i _ =>
    (integrable_const _).indicator₀ (hm i))
  have cnt (ω) : f ω = ((Finset.univ.filter (fun i => |z i ω| ≤ ε)).card:ℝ) := by
    simp [f,B,Set.indicator]
  have mx := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := f) (ae_of_all _ fun ω => by rw [cnt]; positivity) fi A
  have est (i) : ∫ ω, (B i).indicator (fun _ => (1:ℝ)) ω ∂μ ≤ 2*ε := by
    rw [integral_indicator₀ (hm i),setIntegral_const,smul_eq_mul,mul_one]
    change μ.real {ω | |z i ω|≤ε} ≤ _
    rw [(law i).measureReal_eq (measurableSet_le (by fun_prop : Measurable (fun x : ℝ => |x|)) measurable_const)]
    exact gaussian_small_ball ε hε
  have total : ∫ ω, f ω ∂μ ≤ 2*n*ε := by
    rw [show f = _ from rfl, integral_finsetSum _ (fun i _ => (integrable_const _).indicator₀ (hm i))]
    apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => est i)).trans_eq
    simp; ring
  apply (le_div_iff₀ hA).mpr
  have next := mx.trans total
  simp_rw [cnt] at next
  linarith

/-- Gaussian readout maximum via Chernoff and a finite union, without an
independence requirement. -/
theorem gaussian_max {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : Fin n → Ω → ℝ) (law : ∀ i, HasLaw (z i) (gaussianReal 0 1) μ)
    (M : ℝ) (hM : 0 ≤ M) : μ.real {ω | ∃ i, M ≤ |z i ω|} ≤ 2*n*Real.exp (-M^2/2) := by
  let γ := gaussianReal 0 1
  have plus := measure_ge_le_exp_mul_mgf (μ := γ) (X := fun x : ℝ => x) M hM
    (integrable_exp_mul_gaussianReal M)
  have minus := measure_le_le_exp_mul_mgf (μ := γ) (X := fun x : ℝ => x) (-M) (neg_nonpos.mpr hM)
    (integrable_exp_mul_gaussianReal (-M))
  simp only [γ,mgf_fun_id_gaussianReal,zero_mul,NNReal.coe_one,one_mul,zero_add,
    ← Real.exp_add] at plus minus
  ring_nf at plus minus
  have B : γ.real {x : ℝ | M ≤ |x|} ≤ 2*Real.exp (-M^2/2) := by
    rw [show {x : ℝ | M ≤ |x|} = {x | M ≤ x} ∪ {x | x ≤ -M} by
      ext x; simp [le_abs,le_neg]]
    apply (measureReal_union_le _ _).trans
    convert add_le_add plus minus using 1; ring_nf
  have localB (i) : μ.real {ω | M ≤ |z i ω|} ≤ 2*Real.exp (-M^2/2) := by
    rw [(law i).measureReal_eq (measurableSet_le measurable_const
      (by fun_prop : Measurable fun x : ℝ => |x|))]
    exact B
  rw [show {ω | ∃ i, M ≤ |z i ω|} = ⋃ i, {ω | M ≤ |z i ω|} by ext; simp]
  apply (measureReal_iUnion_fintype_le _).trans
  apply (Finset.sum_le_sum (s := Finset.univ) (fun i _ => localB i)).trans_eq
  simp; ring

end TwoLayerBudget
