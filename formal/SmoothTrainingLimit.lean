module

public import SmoothGramLimit
import Mathlib.Tactic

/-! Infinite-time smooth-network movement at the fixed learning rate selected
from the population Gram. -/
@[expose] public section
noncomputable section
namespace SmoothTrainingLimit
open SmoothSeedLaw SmoothGramLimit TwoLayerNetwork TwoLayerLimit NonlinearBudget
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped InnerProduct NNReal Topology
variable {n d k : ℕ}

def scale (n : ℕ) := sqrt (log n/n)

theorem scale_zero : Tendsto scale atTop (𝓝 0) := by
  have H := ((isLittleO_log_rpow_atTop (r:=1) zero_lt_one).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).sqrt
  change Tendsto (fun n : ℕ => sqrt (log n/n)) atTop (𝓝 0)
  simpa only [Function.comp_def,rpow_one,sqrt_zero] using H

theorem readout_max (n : ℕ) (hn : 0<n) :
    (law d).real {ω | ∃ i : Fin n, sqrt (4*log n) ≤ |readout (packed n ω) i|} ≤ 2/n := by
  let M := sqrt (4*log n)
  have h := TwoLayerBudget.gaussian_max (law d) (fun (i : Fin n) (ω : Draws d) => (ω i).1)
    (fun i => a_law i) M (sqrt_nonneg _)
  have n1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have np := zero_lt_one.trans_le n1
  apply h.trans_eq
  rw [show M^2=4*log n from sq_sqrt (mul_nonneg (by norm_num) (log_nonneg n1)),
    show -(4*log (n:ℝ))/2 = -(log n + log n) by ring,exp_neg,exp_add,exp_log np]
  field_simp

def S₀ (b : Fin k → ℝ) (R L : ℝ) := ∑ j, 2*(b j)^2*R^2*L^2
def S₁ (b : Fin k → ℝ) (R L : ℝ) := ∑ j, 2*(b j)^2*R^2*(L^2*(b j)^2)
def rowConstant (b : Fin k → ℝ) (R L₁ L₂ : ℝ) := sqrt (S₀ b R L₁+4*S₁ b R L₂)
def delta (b : Fin k → ℝ) (R L₁ L₂ : ℝ) (n : ℕ) : ℝ≥0 :=
  ⟨rowConstant b R L₁ L₂*scale n,mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)⟩

theorem smooth_mass (n : ℕ) (hn : 0<n) (lg : 1≤log n) (b : Fin k → ℝ) (R L₁ L₂ : ℝ) :
    (∑ j, 2*(b j)^2*R^2*(L₁^2+(sqrt (4*log n))^2*L₂^2*(b j)^2)) ≤
      n*(delta b R L₁ L₂ n:ℝ)^2 := by
  have z₀ : 0≤S₀ b R L₁ := Finset.sum_nonneg (fun j _ => by positivity)
  have z₁ : 0≤S₁ b R L₂ := Finset.sum_nonneg (fun j _ => by positivity)
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have ln := zero_le_one.trans lg
  change _ ≤ (n:ℝ)*(sqrt _*sqrt _)^2
  rw [mul_pow,sq_sqrt (show 0≤S₀ b R L₁+4*S₁ b R L₂ by positivity),sq_sqrt (div_nonneg ln np.le),sq_sqrt (mul_nonneg (by norm_num) ln)]
  have eq : (∑ j, 2*(b j)^2*R^2*(L₁^2+4*log n*L₂^2*(b j)^2)) =
      S₀ b R L₁+4*log n*S₁ b R L₂ := by
    unfold S₀ S₁;rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl;intro j _;ring
  rw [eq,show (n:ℝ)*((S₀ b R L₁+4*S₁ b R L₂)*(log n/n))=(S₀ b R L₁+4*S₁ b R L₂)*log n by field_simp]
  nlinarith [mul_nonneg z₀ (sub_nonneg.mpr lg)]

def Γ (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) := gramOp (Γmat φ g b x)

theorem gram_norm (A : Params n d →L[ℝ] Space k) : ‖A.comp (A†)‖=‖A‖^2 := by
  simpa [←sq] using (A†).norm_adjoint_comp_self

theorem frame_transfer (A : Params n d →L[ℝ] Space k) (G : Space k →L[ℝ] Space k)
    (l τ : ℝ) (frame : ∀ y, l*‖y‖^2 ≤ inner ℝ y (G y))
    (near : ‖A.comp (A†)-G‖≤τ) (y : Space k) :
    (l-τ)*‖y‖^2 ≤ ‖(A†) y‖^2 := by
  let D := A.comp (A†)-G
  have m := (abs_real_inner_le_norm y (D y)).trans (mul_le_mul_of_nonneg_left
    ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_right near (norm_nonneg y))) (norm_nonneg y))
  have e : inner ℝ y (D y) = ‖(A†) y‖^2 - inner ℝ y (G y) := by
    change inner ℝ y (A ((A†) y)-G y) = _
    rw [inner_sub_right,← A.adjoint_inner_left,real_inner_self_eq_norm_sq]
  rw [e] at m
  linarith [(abs_le.mp m).1,frame y]

/-- The smooth rate under iid Gaussian initialization. The lower frame
bound and fixed step test concern the actual population matrix Γ. -/
theorem smooth_movement_in_probability (hk : 0<k) {φ g : ℝ → ℝ} {L₁ L₂ : ℝ}
    (act : Activation φ g L₁ L₂) (b : Fin k → ℝ) (bp : ∀ j, 0≤b j)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖≤1) (y : Space k)
    (l h : ℝ) (lp : 0<l) (hp : 0<h) (step : h*‖Γ φ g b x‖<1)
    (frame : ∀ v, l*‖v‖^2 ≤ inner ℝ v (Γ φ g b x v)) (η : ℝ) (ηp : 0<η) :
    ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      let F := fun ω : Draws d => TwoLayerNetwork.residual φ b x y (packed n ω)
      let J := fun ω z => jac φ g b x (packed n ω+z)
      let A := fun ω => jac φ g b x (packed n ω)
      (law d).real {ω | ¬Endpoint (F ω) (J ω) (A ω) h (L*scale n)} ≤ η := by
  let G := Γ φ g b x
  let τ := min (l/2) (min 1 ((1-h*‖G‖)/(2*h)))
  have margin : 0<1-h*‖G‖ := sub_pos.mpr step
  have τp : 0<τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have small₁ : τ ≤ l/2 := min_le_left _ _
  have small₂ : τ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have small₃ : τ ≤ (1-h*‖G‖)/(2*h) := (min_le_right _ _).trans (min_le_right _ _)
  let U := sqrt (‖G‖+1)
  let C := 2*(∑ j, Cmat φ b x j j)+2*‖y‖^2
  let V := sqrt (|C|/(η/3)+1)
  let m := l/2
  let R := 4*(U+1)*V/m
  let q := 1-h*m/4
  have mpos : 0<m := by dsimp [m]; positivity
  have up : 0<U := by dsimp [U];positivity
  have vp : 0<V := by dsimp [V];positivity
  have rpos : 0<R := by dsimp [R];positivity
  have Vcut : C/V^2 ≤ η/3 := by
    change C/(sqrt _)^2 ≤ η/3
    rw [sq_sqrt (by positivity)];apply (div_le_iff₀ (by positivity)).mpr
    have eq : η/3*(|C|/(η/3)+1) = |C|+η/3 := by field_simp
    rw [eq];linarith [le_abs_self C]
  let D := fun n => (delta b R L₁ L₂ n:ℝ)
  let c := R/sqrt m+4*V/m
  let B := 2*(V/sqrt m)*c+c^2
  have c0 : 0≤c := by dsimp [c];positivity
  have B0 : 0≤B := by dsimp [B];positivity
  let L := B*rowConstant b R L₁ L₂
  have az : Tendsto D atTop (𝓝 0) := by
    change Tendsto (fun n => rowConstant b R L₁ L₂*scale n) atTop (𝓝 0)
    simpa only [mul_zero] using scale_zero.const_mul (rowConstant b R L₁ L₂)
  have zz : Tendsto (fun n => (2*U+D n)*D n) atTop (𝓝 0) := by simpa using (az.const_add (2*U)).mul az
  have ll := (tendstoInMeasure_iff_measureReal_norm.mp (gram_law act b x)) τ τp
  have tails : Tendsto (fun n : ℕ => 2/(n:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop.const_mul 2
  have logs := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have e3 : 0<η/3 := by positivity
  refine ⟨L,mul_nonneg B0 (sqrt_nonneg _),?_⟩
  filter_upwards [eventually_ge_atTop 1,logs.eventually_ge_atTop 1,az.eventually_lt_const zero_lt_one,
    zz.eventually_lt_const (show 0<m/4 by positivity),ll.eventually_lt_const e3,tails.eventually_lt_const e3]
    with n hn logn dn tiny gramBad maxBad
  intro F J A
  let B₁ := {ω : Draws d | τ≤‖gram φ g b x (packed n ω)-G‖}
  let B₂ := {ω : Draws d | ∃ i : Fin n, sqrt (4*log n) ≤ |readout (packed n ω) i|}
  let B₃ := {ω : Draws d | V^2≤‖F ω 0‖^2}
  have p₁ : (law d).real B₁ ≤ η/3 := gramBad.le
  have p₂ : (law d).real B₂ ≤ η/3 := (readout_max n hn).trans maxBad.le
  have p₃ : (law d).real B₃ ≤ η/3 := (residual_tail act b x y n hn (sq_pos_of_pos vp)).trans Vcut
  have union := (measureReal_union_le (μ:=law d) (B₁∪B₂) B₃).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add p₁ p₂)) p₃)
  apply (measureReal_mono ?_).trans (union.trans_eq (by ring))
  intro ω miss
  by_contra outside
  have close : ‖gram φ g b x (packed n ω)-G‖ ≤ τ := le_of_not_ge (fun z => outside (Or.inl (Or.inl z)))
  have cap (i) : |readout (packed n ω) i|≤sqrt (4*log n) := le_of_not_ge (fun z => outside (Or.inl (Or.inr ⟨i,z⟩)))
  have res : ‖F ω 0‖≤V := (sq_le_sq₀ (norm_nonneg _) vp.le).mp (le_of_not_ge (fun z => outside (Or.inr z)))
  have upper : ‖A ω‖^2 ≤ ‖G‖+τ := by
    rw [← gram_norm]
    have s := norm_sub_norm_le (gram φ g b x (packed n ω)) G
    change ‖gram φ g b x (packed n ω)‖ ≤ _;linarith
  have An : ‖A ω‖≤U := (le_sqrt (norm_nonneg _) (by positivity)).mpr (upper.trans (by linarith))
  have fr (v : Space k) : m*‖v‖^2 ≤ ‖((A ω)†) v‖^2 := (mul_le_mul_of_nonneg_right
    (show m≤l-τ by dsimp [m];linarith) (sq_nonneg _)).trans (frame_transfer _ G l τ frame close v)
  have hstep : h*‖A ω‖^2 ≤ 1 := by
    have e := (le_div_iff₀ (show 0<2*h by positivity)).mp small₃
    nlinarith only [mul_le_mul_of_nonneg_left upper hp.le,e,margin]
  let one : Space k := EuclideanSpace.single ⟨0,hk⟩ 1
  have onen : ‖one‖=1 := by simp [one]
  have low := (fr one).trans (pow_le_pow_left₀ (norm_nonneg _) (((A ω)†).le_opNorm one) 2)
  rw [onen,one_pow,mul_one,LinearIsometryEquiv.norm_map,mul_one] at low
  have hm : h*m≤1 := (mul_le_mul_of_nonneg_left low hp.le).trans hstep
  have q0 : 0≤q := by dsimp [q];linarith
  have q1 : q<1 := by dsimp [q];linarith [mul_pos hp mpos]
  have initial := frame_contraction (A ω) h m hp.le hstep hm fr
  have sd := ((mul_le_mul_of_nonneg_right
    (show 2*‖A ω‖+D n ≤ 2*U+D n by linarith) (delta b R L₁ L₂ n).2).trans tiny.le)
  change (2*‖A ω‖+D n)*D n ≤ m/4 at sd
  have contraction : ‖linearStep (A ω) h‖ + h*(2*‖A ω‖+D n)*D n ≤ q := by
    dsimp [q];linarith [mul_le_mul_of_nonneg_left sd hp.le]
  have capacity : h*(‖A ω‖+D n)*‖F ω 0‖/(1-q) ≤ R := by
    rw [show 1-q=h*m/4 by dsimp [q];ring]
    calc _ = 4*(‖A ω‖+D n)*‖F ω 0‖/m := by field_simp
         _ ≤ R := by dsimp [R];gcongr
  have Ctl : BallControl (F ω) (J ω) (A ω) h R q (delta b R L₁ L₂ n) :=
    smooth_ball _ φ g act.first act.L₁_nonneg act.L₂_nonneg (sqrt_nonneg _) act.lipschitz act.bounded b bp x hx
      y (packed n ω) cap (smooth_mass n hn logn b R L₁ L₂) hp q0 q1 contraction capacity
  apply miss (endpoint_mono (endpoint_bound _ _ _ _ mpos hp rpos.le fr res Ctl) ?_)
  change 2*(V/sqrt m)*(D n*c)+(D n*c)^2 ≤ L*scale n
  have dq := mul_le_mul_of_nonneg_left dn.le (delta b R L₁ L₂ n).2
  change D n*D n ≤ D n*1 at dq
  calc _ ≤ B*D n := by dsimp [B];nlinarith only [mul_le_mul_of_nonneg_right dq (sq_nonneg c)]
       _ = _ := (mul_assoc B (rowConstant b R L₁ L₂) (scale n)).symm

end SmoothTrainingLimit
