module

public import FeatureFlowPerturbation
import all FeatureFlowPerturbation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

/-! Moving tangent operators and population errors in the two-factor model. -/
@[expose] public section
noncomputable section
open Set Metric Real Filter Topology
open scoped NNReal Matrix Matrix.Norms.L2Operator
namespace FeatureFlowTangent
open FeatureFlowPerturbation
abbrev Vec := EuclideanSpace ℝ (Fin 2)

def flat (A : Mat) : EuclideanSpace ℝ (Fin 2 × Fin 2) := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
def frob (A : Mat) := ‖flat A‖
def tangent (z : Factors) (E : Mat) : Mat := (z.1*star z.1)*E+E*(star z.2*z.2)

private theorem flat_sub (A B : Mat) : flat (A-B)=flat A-flat B := by ext; rfl
private theorem flat_add (A B : Mat) : flat (A+B)=flat A+flat B := by ext; rfl
private theorem frob_add (A B : Mat) : frob (A+B)≤frob A+frob B := by
  unfold frob;rw [flat_add];exact norm_add_le _ _

private def col (A : Mat) (j : Fin 2) : Vec := WithLp.toLp 2 (fun i => A i j)
private theorem frob_sq (A : Mat) : frob A^2=∑ j, ‖col A j‖^2 := by
  simp [frob,EuclideanSpace.real_norm_sq_eq,flat,col,Fintype.sum_prod_type];ring
private theorem frob_star (A : Mat) : frob (star A) = frob A := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.real_norm_sq_eq,flat,Fintype.sum_prod_type,Matrix.star_apply];ring
private theorem frob_mul (A B : Mat) : frob (A*B)≤‖A‖*frob B := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  change frob (A*B)^2≤(‖A‖*frob B)^2
  rw [frob_sq,mul_pow,frob_sq,Finset.mul_sum]
  apply Finset.sum_le_sum;intro j _
  have eq : col (A*B) j=Matrix.toEuclideanCLM (𝕜:=ℝ) A (col B j) := by ext; rfl
  rw [eq,←mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((Matrix.toEuclideanCLM (𝕜:=ℝ) A).le_opNorm _) 2
private theorem frob_mul_right (A B : Mat) : frob (A*B)≤frob A*‖B‖ := by
  simpa [←star_mul,mul_comm,frob_star] using frob_mul (star B) (star A)

theorem frob_le (A : Mat) : frob A≤sqrt 2*‖A‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change frob A^2≤(sqrt 2*‖A‖)^2
  rw [frob_sq,mul_pow,sq_sqrt (by norm_num)]
  have b (j : Fin 2) : ‖col A j‖≤‖A‖ := by
    let e : Vec := WithLp.toLp 2 (Pi.single j (1:ℝ))
    have eq : Matrix.toEuclideanCLM (𝕜:=ℝ) A e=col A j := by ext; simp [e,col,Matrix.mulVec_single]
    have h := (Matrix.toEuclideanCLM (𝕜:=ℝ) A).le_opNorm e
    rw [eq] at h
    simpa [e,Matrix.l2_opNorm_toEuclideanCLM] using h
  convert Finset.sum_le_sum (s:=Finset.univ) (g:=fun _ : Fin 2 => ‖A‖^2)
    (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (b j) 2) using 1;simp

theorem population_error_difference (S X Y : Mat) :
    |frob (S-X)-frob (S-Y)|≤sqrt 2*‖X-Y‖ := by
  have h := abs_norm_sub_norm_le (flat (S-X)) (flat (S-Y))
  rw [←flat_sub,show (S-X)-(S-Y)=Y-X by abel] at h
  exact h.trans ((frob_le _).trans_eq (by rw [norm_sub_rev]))

theorem tangent_difference (x y : Factors) (E : Mat) :
    frob (tangent x E-tangent y E) ≤ (‖x.1*star x.1-y.1*star y.1‖+‖star x.2*x.2-star y.2*y.2‖)*frob E := by
  let A := x.1*star x.1-y.1*star y.1
  let B := star x.2*x.2-star y.2*y.2
  rw [show tangent x E-tangent y E=A*E+E*B by dsimp [tangent,A,B];noncomm_ring]
  exact (frob_add _ _).trans ((add_le_add (frob_mul A E) (frob_mul_right E B)).trans_eq (by dsimp [A,B];ring))

theorem independent_observables (S : Mat) {z ref : ℝ → Factors} {H : ℝ} (hH : 0≤H)
    (flow : IsFlow S z H) (aligned : IsFlow S ref H) (R : ℝ≥0)
    (margin : ∀ t∈Icc 0 H, ‖ref t‖+1≤R)
    (small : dist (z 0) (ref 0)*exp (constant S R*H)<1) (t : ℝ) (ht : t∈Icc 0 H) :
    let d := dist (z 0) (ref 0)*exp (constant S R*t)
    |frob (S-prediction (z t))-frob (S-prediction (ref t))|≤sqrt 2*(2*R*d) ∧
    ∀ E, frob (tangent (z t) E-tangent (ref t) E)≤4*R*d*frob E := by
  intro d
  have h := independent_factor_stability S hH flow aligned R margin small t ht
  refine ⟨(population_error_difference _ _ _).trans (mul_le_mul_of_nonneg_left h.2 (sqrt_nonneg _)),?_⟩
  have dlo : d<1 := (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (constant S R).2)) dist_nonneg).trans_lt small
  have hh := margin t ht
  have normx : ‖z t‖≤R := (norm_le_norm_sub_add (z t) (ref t)).trans (by rw [←dist_eq_norm];linarith only [h.1,dlo,hh])
  have normy : ‖ref t‖≤R := by linarith
  have dx : ‖z t-ref t‖≤d := by rw [←dist_eq_norm];exact h.1
  have f : ‖(z t).1-(ref t).1‖≤d := (norm_fst_le (z t-ref t)).trans dx
  have w : ‖(z t).2-(ref t).2‖≤d := (norm_snd_le (z t-ref t)).trans dx
  let x := z t
  let y := ref t
  have bound (A B : Mat) (xa : ‖A‖≤R) (yb : ‖B‖≤R) (AB : ‖A-B‖≤d) :
      ‖A*star A-B*star B‖≤2*R*d := by
    have h := norm_mul_sub A (star A) B (star B)
    rw [norm_star,←star_sub,norm_star] at h
    exact h.trans ((add_le_add (mul_le_mul AB xa (norm_nonneg _) ((norm_nonneg _).trans AB))
      (mul_le_mul yb AB (norm_nonneg _) R.2)).trans_eq (by ring))
  have a := bound x.1 y.1 ((norm_fst_le _).trans normx) ((norm_fst_le _).trans normy) f
  have b := bound (star x.2) (star y.2) (by simpa using (norm_snd_le _).trans normx) (by simpa using (norm_snd_le _).trans normy) (by simpa [←star_sub] using w)
  simp only [star_star] at b
  intro E
  exact (tangent_difference x y E).trans (mul_le_mul_of_nonneg_right (by linarith only [a,b]) (norm_nonneg _))

private def atten (s : Fin 2 → ℝ) (t : ℝ) : Mat := Matrix.diagonal fun i => exp (-s i*t)

private theorem precision_form (s : Fin 2 → ℝ) (D : Mat) (t : ℝ) :
    precision s D t=atten s t*D*atten s t+
      Matrix.diagonal (fun i => (1-(exp (-s i*t))^2)/s i) := by
  ext i j
  simp only [precision,atten,Matrix.of_apply,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [show -(s i+s j)*t= -s i*t + -s j*t by ring,exp_add]
  by_cases h : i=j
  · subst j; simp;ring
  · simp [h];ring

private theorem rotate_sub (θ : ℝ) (d : Fin 2 → ℝ) (c : ℝ) :
    rotatedMatrix θ d - c • (1:Mat)=rotatedMatrix θ (fun i => d i-c) := by
  obtain ⟨_,right⟩ := rotation_orthogonal θ
  have diag : (Matrix.diagonal fun i => d i-c : Mat)=Matrix.diagonal d-c • 1 := by
    ext i j;by_cases h : i=j <;> simp [h]
  rw [rotatedMatrix,rotatedMatrix,diag]
  simp [mul_sub,sub_mul,right]

private theorem precision_lower (s d : Fin 2 → ℝ) (θ t c : ℝ) (ht : 0≤t)
    (hs : ∀ i,0<s i) (invS : ∀ i,c≤1/s i) (init : ∀ i,c≤d i) :
    (precision s (rotatedMatrix θ d) t-c • (1:Mat)).PosSemidef := by
  let F := atten s t
  let z (i : Fin 2) := (1-exp (-s i*t)^2)*(1/s i-c)
  have pos : (rotatedMatrix θ (fun i => d i-c)).PosSemidef :=
    (Matrix.PosSemidef.diagonal (show (0:Fin 2→ℝ)≤fun i => d i-c from fun i => sub_nonneg.mpr (init i))).mul_mul_conjTranspose_same _
  have zd (i : Fin 2) : 0≤z i := by
    have le1 : exp (-s i*t)≤1 := exp_le_one_iff.mpr (by nlinarith only [mul_nonneg (hs i).le ht])
    exact mul_nonneg (sub_nonneg.mpr (pow_le_one₀ (exp_nonneg _) le1)) (sub_nonneg.mpr (invS i))
  have eq : precision s (rotatedMatrix θ d) t-c • (1:Mat) =
      F*rotatedMatrix θ (fun i => d i-c)*star F+Matrix.diagonal z := by
    rw [←rotate_sub,precision_form,show star F=F from diag_star _]
    change F*rotatedMatrix θ d*F+_-_=_
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one]
    ext i j
    rw [show F*F=Matrix.diagonal (fun i => exp (-s i*t)*exp (-s i*t)) from Matrix.diagonal_mul_diagonal ..]
    by_cases h : i=j
    · subst j;simp [z];ring
    · simp [z,h]
  rw [eq]
  exact (pos.mul_mul_conjTranspose_same F).add (Matrix.PosSemidef.diagonal zd)

private theorem inverse_norm {P B : Mat} {s : ℝ} (sp : 0<s) (inv : P*B=1)
    (H : (P-(1/s) • (1:Mat)).PosSemidef) : ‖B‖≤s := by
  let L := Matrix.toEuclideanCLM (n:=Fin 2) (𝕜:=ℝ)
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ sp.le
  intro x
  let y := L B x
  have yx : L P y=x := by
    change (L P*L B) x=x
    rw [←map_mul,inv,map_one];rfl
  have test : 0 ≤ inner ℝ y (L (P-(1/s) • (1:Mat)) y) := by
    rw [Matrix.inner_toEuclideanCLM]
    simpa using H.dotProduct_mulVec_nonneg y.ofLp
  simp only [map_sub,map_smul,map_one,sub_apply,smul_apply,
    one_apply_eq_self,yx,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq] at test
  have cs := real_inner_le_norm y x
  change ‖y‖≤s*‖x‖
  by_cases zero : y=0
  · rw [zero,norm_zero];positivity
  · have yp := norm_pos_iff.mpr zero
    have sm := mul_le_mul_of_nonneg_left (show 1/s*‖y‖^2≤‖y‖*‖x‖ by linarith) sp.le
    field_simp at sm
    exact sm

private theorem precision_difference (d : Fin 2 → ℝ) (θ : ℝ) :
    ‖rotatedMatrix θ d-Matrix.diagonal d‖= |d 1-d 0| * |sin θ| := by
  let A := rotatedMatrix θ d-Matrix.diagonal d
  let h := (d 1-d 0)*sin θ
  have entry : A = !![h*sin θ,-h*cos θ;-h*cos θ,-h*sin θ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A,rotatedMatrix,rotation,h,Matrix.mul_apply,
      Matrix.star_apply,Matrix.vecMul,dotProduct,Matrix.diagonal_apply,Fin.sum_univ_two] <;>
      ring_nf <;> nlinarith only [congrArg (fun v : ℝ => d 0*v) (sin_sq_add_cos_sq θ),congrArg (fun v : ℝ => d 1*v) (sin_sq_add_cos_sq θ)]
  have sqr : star A*A=h^2 • (1:Mat) := by
    rw [entry]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Matrix.star_apply,Fin.sum_univ_two] <;>
      nlinarith only [congrArg (fun v : ℝ => h^2*v) (sin_sq_add_cos_sq θ)]
  have n := Matrix.l2_opNorm_conjTranspose_mul_self A
  change ‖star A*A‖=‖A‖*‖A‖ at n
  rw [sqr,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_one,mul_one] at n
  change ‖A‖=_
  rw [←abs_mul]
  exact (sq_eq_sq₀ (norm_nonneg A) (abs_nonneg _)).mp (by rw [sq_abs];dsimp [h] at n;linarith only [n,sq ‖A‖])

private theorem attenuation_bound (s : Fin 2→ℝ) {r t : ℝ} (lower : ∀ i,r≤s i) (ht : 0≤t) :
    ‖atten s t‖≤exp (-r*t) := by
  rw [atten,Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (exp_nonneg _)).mpr fun i => by
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right (lower i) ht])

private theorem rotate_zero (p : Fin 2→ℝ) : rotatedMatrix 0 p=Matrix.diagonal p := by
  have e : rotation 0=1 := by ext i j;fin_cases i <;> fin_cases j <;> simp [rotation]
  simp [rotatedMatrix,e]

/-- All three bounds against the moving aligned reference have the paper's
constants. Both training paths are genuine solutions of the two-factor ODE. -/
theorem rotated_observables (s p : Fin 2→ℝ) (θ smax smin : ℝ)
    (positive : ∀ i,0<s i) (range : ∀ i,smin≤s i ∧ s i≤smax) (hp : ∀ i,0<p i ∧ p i≤smax)
    {z ref : ℝ→Factors} {t : ℝ} (ht : 0≤t)
    (fz : IsFlow (Matrix.diagonal s) z t) (fr : IsFlow (Matrix.diagonal s) ref t)
    (iz : z 0=(rotatedFactor θ p,star (rotatedFactor θ p))) (ir : ref 0=(rotatedFactor 0 p,star (rotatedFactor 0 p))) :
    let M := smax^2*|1/p 1-1/p 0| * |sin θ| *exp (-2*smin*t)
    ‖prediction (z t)-prediction (ref t)‖≤M ∧
    (∀ E, frob (tangent (z t) E-tangent (ref t) E)≤2*M*frob E) ∧
    |frob (Matrix.diagonal s-prediction (z t))-frob (Matrix.diagonal s-prediction (ref t))|≤sqrt 2*M := by
  intro M
  let d := fun i => 1/p i
  let B := prediction (z t)
  let C := prediction (ref t)
  let P := precision s (rotatedMatrix θ d) t
  let Q := precision s (Matrix.diagonal d) t
  let F := atten s t
  have sp := (positive 0).trans_le (range 0).2
  have it : t∈Icc 0 t := ⟨ht,le_rfl⟩
  have each {v : ℝ→Factors} (a : ℝ) (iv : v 0=(rotatedFactor a p,star (rotatedFactor a p)))
      (fv : IsFlow (Matrix.diagonal s) v t) :
      precision s (rotatedMatrix a d) t * prediction (v t)=1 ∧ ‖prediction (v t)‖≤smax ∧
      (v t).2=star (v t).1 := by
    have init : (v 0).2=star (v 0).1 := by rw [iv]
    have inv : initialInverse a p*prediction (v 0)=1 := by
      rw [iv,prediction,rotatedFactor_product p (fun i => (hp i).1.le) a]
      exact initialInverse_mul p (fun i => (hp i).1.ne') a
    have prod := precision_mul_product (fun i => (positive i).ne') ht fv init _ inv t it
    refine ⟨prod,inverse_norm sp prod ?_,balanced_factors (diag_star _) ht fv init t it⟩
    exact precision_lower s d a t (1/smax) ht positive
      (fun i => one_div_le_one_div_of_le (positive i) (range i).2)
      (fun i => one_div_le_one_div_of_le (hp i).1 (hp i).2)
  obtain ⟨pB,bN,bal⟩ := each θ iz fz
  obtain ⟨qC,cN,balr⟩ := each 0 ir fr
  rw [rotate_zero] at qC
  change P*B=1 at pB
  change Q*C=1 at qC
  have bP := mul_eq_one_comm.mp pB
  have eq : B-C=B*(Q-P)*C := by
    calc
      _ = B*(Q*C)-(B*P)*C := by rw [qC,bP,mul_one,one_mul]
      _ = _ := by noncomm_ring
  have dq : Q-P=F*(Matrix.diagonal d-rotatedMatrix θ d)*F := by
    dsimp [P,Q,F]; rw [precision_form,precision_form];noncomm_ring
  have df : ‖F‖≤exp (-smin*t) := attenuation_bound s (fun i => (range i).1) ht
  have dd : ‖Matrix.diagonal d-rotatedMatrix θ d‖ = |d 1-d 0| * |sin θ| :=
    (norm_sub_rev ..).trans (precision_difference d θ)
  have pdelta : ‖Q-P‖≤exp (-smin*t)*(|d 1-d 0| * |sin θ|)*exp (-smin*t) := by
    rw [dq]
    apply (norm_mul_le ..).trans
    apply mul_le_mul _ df (norm_nonneg _) (by positivity)
    apply (norm_mul_le ..).trans
    exact mul_le_mul df dd.le (norm_nonneg _) (exp_nonneg _)
  have diff : ‖B-C‖≤M := by
    rw [eq]
    apply (norm_mul_le ..).trans
    apply (mul_le_mul ( (norm_mul_le ..).trans (mul_le_mul bN pdelta (norm_nonneg _) sp.le)) cN (norm_nonneg _) (by positivity)).trans_eq
    dsimp [M,d]
    rw [show -2*smin*t= -smin*t+ -smin*t by ring,exp_add]
    ring
  refine ⟨diff,fun E => ?_,(population_error_difference _ _ _).trans (mul_le_mul_of_nonneg_left diff (sqrt_nonneg _))⟩
  apply (tangent_difference (z t) (ref t) E).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  dsimp [B,C,prediction] at diff
  rw [bal,balr] at diff ⊢
  simp only [star_star]
  linarith

/-- Existence from the prescribed rotation and alignment, jointly for the
entire nonnegative time axis with one common pair of trajectories. -/
theorem exists_rotated_observables (s p : Fin 2→ℝ) (θ smax smin : ℝ)
    (positive : ∀ i,0<s i) (range : ∀ i,smin≤s i ∧ s i≤smax) (hp : ∀ i,0<p i ∧ p i≤smax) :
    ∃ z ref : ℝ→Factors,
      z 0=(rotatedFactor θ p,star (rotatedFactor θ p)) ∧ ref 0=(rotatedFactor 0 p,star (rotatedFactor 0 p)) ∧
      (∀ t,0≤t → HasDerivAt z (field (Matrix.diagonal s) (z t)) t ∧ HasDerivAt ref (field (Matrix.diagonal s) (ref t)) t) ∧
      ∀ t,0≤t → let M := smax^2*|1/p 1-1/p 0| * |sin θ| *exp (-2*smin*t)
        ‖prediction (z t)-prediction (ref t)‖≤M ∧ (∀ E, frob (tangent (z t) E-tangent (ref t) E)≤2*M*frob E) ∧
        |frob (Matrix.diagonal s-prediction (z t))-frob (Matrix.diagonal s-prediction (ref t))|≤sqrt 2*M := by
  obtain ⟨z,hz,fz⟩ := exists_global_factor_flow (Matrix.diagonal s) (rotatedFactor θ p,star (rotatedFactor θ p))
  obtain ⟨v,hv,fv⟩ := exists_global_factor_flow (Matrix.diagonal s) (rotatedFactor 0 p,star (rotatedFactor 0 p))
  exact ⟨z,v,hz,hv,fun t ht => ⟨fz t ht,fv t ht⟩,fun t ht => rotated_observables s p θ smax smin positive range hp ht
    (fun t ht => fz t ht.1) (fun t ht => fv t ht.1) hz hv⟩

end FeatureFlowTangent
