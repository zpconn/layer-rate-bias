module

public import Movement
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Nonlinear full-batch GD on whitened coordinates, and two-layer gate counts. -/
@[expose] public section
noncomputable section
namespace NonlinearBudget
open Set Filter Metric
open scoped Topology InnerProduct NNReal

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- F is the actual residual evaluated at the displacement from initialization.
Backpropagation may select a derivative at a kink. -/
def gd (F : E → H) (J : E → E →L[ℝ] H) (h : ℝ) : ℕ → E
  | 0 => 0
  | t+1 => gd F J h t + (-h) • ((J (gd F J h t))†) (F (gd F J h t))

def linearStep (A : E →L[ℝ] H) (h : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - h • A.comp (A†)

/-- All analytic hypotheses are local to one fixed ball, and the strict
contraction is required only of the initial Gram plus its perturbation. -/
structure BallControl (F : E → H) (J : E → E →L[ℝ] H) (A : E →L[ℝ] H)
    (h R q : ℝ) (δ : ℝ≥0) : Prop where
  continuous : Continuous F
  step_pos : 0 < h
  ratio_nonneg : 0 ≤ q
  ratio_lt : q < 1
  secant : ApproximatesLinearOn F A (closedBall 0 R) δ
  jacobian : ∀ x, ‖x‖ ≤ R → ‖J x - A‖ ≤ δ
  contraction : ‖linearStep A h‖ + h*(2*‖A‖+δ)*δ ≤ q
  capacity : h*(‖A‖+δ)*‖F 0‖/(1-q) ≤ R

omit [CompleteSpace E] [CompleteSpace H] in
/-- The ordinary mean-value theorem supplies the secant condition throughout
a ball when the network is smooth there. -/
theorem smooth_secant {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {R : ℝ} {δ : ℝ≥0} (diff : ∀ x ∈ closedBall 0 R, HasFDerivAt F (J x) x)
    (close : ∀ x ∈ closedBall 0 R, ‖J x-A‖ ≤ δ) :
    ApproximatesLinearOn F A (closedBall 0 R) δ :=
  fun _ hx _ hy => (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x h => (diff x h).hasFDerivWithinAt) close hy hx

private theorem adjoint_close (J A : E →L[ℝ] H) : ‖J†-A†‖ = ‖J-A‖ := by
  rw [← map_sub,LinearIsometryEquiv.norm_map]

private theorem move_bound {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) (x : E) (hx : ‖x‖ ≤ R) :
    ‖(-h) • ((J x)†) (F x)‖ ≤ h*(‖A‖+δ)*‖F x‖ := by
  have j : ‖J x‖ ≤ ‖A‖+δ := by linarith [(norm_sub_norm_le (J x) A).trans (C.jacobian x hx)]
  rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg C.step_pos.le]
  have op := ((J x)†).le_opNorm (F x)
  rw [LinearIsometryEquiv.norm_map] at op
  have h1 := op.trans (mul_le_mul_of_nonneg_right j (norm_nonneg _))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h1 C.step_pos.le

private theorem one_step {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) (x : E) (hx : ‖x‖ ≤ R)
    (hv : ‖x + (-h) • ((J x)†) (F x)‖ ≤ R) : ‖F (x + (-h) • ((J x)†) (F x))‖ ≤ q*‖F x‖ := by
  let v := x+(-h)•((J x)†) (F x)
  let e := F v-F x-A (v-x)
  let d := A (((J x)†-A†) (F x))
  have rem : ‖e‖ ≤ δ*(h*(‖A‖+δ)*‖F x‖) := by
    have b := C.secant v (mem_closedBall_zero_iff.mpr hv) x (mem_closedBall_zero_iff.mpr hx)
    exact b.trans (mul_le_mul_of_nonneg_left (by simpa [v] using move_bound C x hx) δ.2)
  have drv : ‖d‖ ≤ ‖A‖*(δ*‖F x‖) := by
    apply (A.le_opNorm _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (((J x)†-A†).le_opNorm _).trans
    exact mul_le_mul_of_nonneg_right ((adjoint_close _ _).le.trans (C.jacobian x hx)) (norm_nonneg _)
  have eq : F v = (e+linearStep A h (F x)) + (-h) • d := by
    dsimp [e,d,v,linearStep]
    simp [map_sub,smul_sub]
    abel
  change ‖F v‖ ≤ _
  rw [eq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg C.step_pos.le]
  have hD := mul_le_mul_of_nonneg_left drv C.step_pos.le
  have hR := (norm_add_le e ((linearStep A h) (F x))).trans (add_le_add rem ((linearStep A h).le_opNorm (F x)))
  have hq := mul_le_mul_of_nonneg_right C.contraction (norm_nonneg (F x))
  linarith only [hD,hR,hq]

private theorem geometric_sum {q : ℝ} (hq : 0 ≤ q) (hq' : q < 1) (t : ℕ) :
    ∑ i ∈ Finset.range t, q^i ≤ 1/(1-q) := by
  rw [one_div,← tsum_geometric_of_lt_one hq hq']
  exact (summable_geometric_of_lt_one hq hq').sum_le_tsum _ (fun i _ => pow_nonneg hq i)

/-- Confinement is proved before each call to the local secant bound. The limit
interpolates and the actual entire displacement lies in the original ball. -/
theorem convergence {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) :
    (∀ t, ‖gd F J h t‖ ≤ R ∧ ‖F (gd F J h t)‖ ≤ q^t*‖F 0‖) ∧
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧ ‖D‖ ≤ R := by
  let u := gd F J h
  let s := h*(‖A‖+δ)*‖F 0‖
  have pos : 0 ≤ s := by dsimp [s]; positivity [C.step_pos]
  have cap (t : ℕ) : s*(∑ i ∈ Finset.range t,q^i) ≤ R := by
    apply (mul_le_mul_of_nonneg_left (geometric_sum C.ratio_nonneg C.ratio_lt t) pos).trans
    simpa [s,div_eq_mul_inv] using C.capacity
  have length (t : ℕ) : ‖u t‖ ≤ s*(∑ i ∈ Finset.range t,q^i) ∧ ‖F (u t)‖ ≤ q^t*‖F 0‖ := by
    induction t with
    | zero => simp [u,gd]
    | succ t ih =>
      have hx := ih.1.trans (cap t)
      have b := (move_bound C (u t) hx).trans (mul_le_mul_of_nonneg_left ih.2
        (mul_nonneg C.step_pos.le (add_nonneg (norm_nonneg _) δ.2)))
      have nx : ‖u (t+1)‖ ≤ s*(∑ i ∈ Finset.range (t+1),q^i) := by
        rw [Finset.sum_range_succ,mul_add]
        apply (norm_add_le _ _).trans
        apply add_le_add ih.1 (b.trans_eq ?_)
        dsimp [s]; ring
      refine ⟨nx,(one_step C (u t) hx (nx.trans (cap _))).trans ?_⟩
      simpa only [pow_succ',mul_assoc] using mul_le_mul_of_nonneg_left ih.2 C.ratio_nonneg
  have every := fun t => And.intro ((length t).1.trans (cap t)) (length t).2
  refine ⟨every,?_⟩
  have cauchy := cauchySeq_of_le_geometric (f := u) q s C.ratio_lt (fun t => by
    rw [dist_comm,dist_eq_norm,show u (t+1)=u t+(-h)•((J (u t))†) (F (u t)) from rfl,add_sub_cancel_left]
    have b := (move_bound C (u t) (every t).1).trans (mul_le_mul_of_nonneg_left (every t).2
      (mul_nonneg C.step_pos.le (add_nonneg (norm_nonneg _) δ.2)))
    exact b.trans_eq (by dsimp [s];ring))
  obtain ⟨D,lim⟩ := cauchySeq_tendsto_of_complete cauchy
  have rlim : Tendsto (fun t => F (u t)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun t => (every t).2)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one C.ratio_nonneg C.ratio_lt).mul_const ‖F 0‖
  exact ⟨D,lim,tendsto_nhds_unique ((C.continuous.tendsto D).comp lim) rlim,
    le_of_tendsto' lim.norm (fun t => (every t).1)⟩


/-- The endpoint guarantee retains the orthogonal sum of row-space interpolation
error and accumulated out-of-row movement. B is the inverse on the row space. -/
theorem limiting_movement {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ)
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (B : H →L[ℝ] E)
    (inv : ∀ x, B (A x) = S.starProjection x) (row : ∀ y, (A†) y ∈ S)
    (star : E) (hstar : star ∈ S) (fit : A star = -F 0) :
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧
      ‖D-star‖^2 ≤ (‖B‖*(δ*R))^2 + (h*δ*‖F 0‖/(1-q))^2 := by
  let u := gd F J h
  obtain ⟨each,D,lim,hit,bound⟩ := convergence C
  have leak (T : ℕ) : (∑ t ∈ Finset.range T, h*‖((J (u t))†-A†) (F (u t))‖) ≤ h*δ*‖F 0‖/(1-q) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T,(h*δ*‖F 0‖)*q^t := by
        apply Finset.sum_le_sum
        intro t _
        have op := (((J (u t))†-A†).le_opNorm (F (u t))).trans
          (mul_le_mul ((adjoint_close _ _).le.trans (C.jacobian _ (each t).1)) (each t).2
            (norm_nonneg _) δ.2)
        exact (mul_le_mul_of_nonneg_left op C.step_pos.le).trans_eq (by ring)
      _ = (h*δ*‖F 0‖)*(∑ t ∈ Finset.range T,q^t) := (Finset.mul_sum ..).symm
      _ ≤ _ := by
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
          (geometric_sum C.ratio_nonneg C.ratio_lt T) (show 0 ≤ h*δ*‖F 0‖ by positivity [C.step_pos])
  have finite (T : ℕ) : ‖u T-star‖^2 ≤ (‖B‖*‖A (u T)+F 0‖)^2+(h*δ*‖F 0‖/(1-q))^2 := by
    have f := TrainingPath.gd_squared_error S A B inv star (F 0) hstar fit
      (fun t => (J (u t))†) (A†) row u (fun t => F (u t)) (fun _ => h)
      (fun _ => C.step_pos.le) rfl (fun _ => rfl) T
    exact f.trans (add_le_add_right (pow_le_pow_left₀
      (Finset.sum_nonneg fun _ _ => mul_nonneg C.step_pos.le (norm_nonneg _)) (leak T) 2) _)
  have lu : Tendsto u atTop (𝓝 D) := lim
  have le := le_of_tendsto_of_tendsto' ((lu.sub_const star).norm.pow 2)
    ((((A.continuous.tendsto D).comp lu).add_const (F 0)).norm.const_mul ‖B‖ |>.pow 2
      |>.add_const ((h*δ*‖F 0‖/(1-q))^2)) finite
  have R0 : 0 ≤ R := (norm_nonneg _).trans bound
  have ep := C.secant D (mem_closedBall_zero_iff.mpr bound) 0 (by simpa using R0)
  have id : ‖F D-F 0-A (D-0)‖ = ‖A D+F 0‖ := by
    rw [hit,sub_zero,zero_sub,← neg_add',norm_neg,add_comm]
  rw [id,sub_zero] at ep
  have er := ep.trans (mul_le_mul_of_nonneg_left bound δ.2)
  exact ⟨D,lim,hit,le.trans (add_le_add_left (pow_le_pow_left₀
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_le_mul_of_nonneg_left er (norm_nonneg _)) 2) _)⟩

/-- The manuscript's squared whitened budget, including a second whitening
operator when the optimizer and report metrics differ. -/
theorem squared_budget {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ)
    (S : Submodule ℝ E) [S.HasOrthogonalProjection] (B : H →L[ℝ] E)
    (inv : ∀ x, B (A x) = S.starProjection x) (row : ∀ y, (A†) y ∈ S)
    (star : E) (hstar : star ∈ S) (fit : A star = -F 0) (W : E →L[ℝ] E) :
    let ε := Real.sqrt ((‖B‖*(δ*R))^2+(h*δ*‖F 0‖/(1-q))^2)
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧
      |‖W D‖^2-‖W star‖^2| ≤ 2*‖W star‖*(‖W‖*ε)+(‖W‖*ε)^2 := by
  intro ε
  obtain ⟨D,lim,hit,err⟩ := limiting_movement C S B inv row star hstar fit
  exact ⟨D,lim,hit,TrainingPath.budget_error W _ _ ε
    ((Real.le_sqrt (norm_nonneg _) (by positivity)).mpr err)⟩

/-- The deterministic counting step of the nonsmooth two-layer estimate.
Normalize a preactivation by its input norm. If it was farther than ε from
zero initially, a change of sign costs at least ε² in squared hidden movement. -/
theorem gate_count {n : ℕ} (z₀ z : Fin n → ℝ) (d : Fin n → ℝ)
    (ε R : ℝ) (hε : 0 < ε) (move : ∀ i, |z i-z₀ i| ≤ d i)
    (radius : ∑ i, (d i)^2 ≤ R^2) :
    let crossing := Finset.univ.filter (fun i => z₀ i*z i ≤ 0)
    let near := Finset.univ.filter (fun i => |z₀ i| ≤ ε)
    (crossing.card:ℝ) ≤ near.card + R^2/ε^2 := by
  classical
  intro crossing near
  let far := crossing \ near
  have paid (i) (hi : i ∈ far) : ε^2 ≤ (d i)^2 := by
    have cr : z₀ i*z i ≤ 0 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
    have away : ε < |z₀ i| := by
      by_contra! h; apply (Finset.mem_sdiff.mp hi).2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    have gap : |z₀ i| ≤ |z i-z₀ i| := by
      rcases le_total (z₀ i) 0 with hn|hp
      · have nz : z₀ i < 0 := lt_of_le_of_ne hn (by intro e; rw [e,abs_zero] at away; linarith)
        have p := nonneg_of_mul_nonpos_right cr nz
        rw [abs_of_nonpos hn,abs_of_nonneg (by linarith : 0 ≤ z i-z₀ i)]
        linarith
      · have zp : 0 < z₀ i := lt_of_le_of_ne hp (by intro e; rw [←e,abs_zero] at away; linarith)
        have p := nonpos_of_mul_nonpos_right cr zp
        rw [abs_of_nonneg hp,abs_of_nonpos (by linarith : z i-z₀ i ≤ 0)]
        linarith
    exact pow_le_pow_left₀ hε.le (away.le.trans (gap.trans (move i))) 2
  have cost : (far.card:ℝ)*ε^2 ≤ R^2 := by
    calc _ = ∑ _ ∈ far, ε^2 := by simp
         _ ≤ ∑ i ∈ far,(d i)^2 := Finset.sum_le_sum paid
         _ ≤ ∑ i,(d i)^2 := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
         _ ≤ _ := radius
  have size : crossing.card ≤ near.card+far.card := by
    have h := Finset.card_sdiff_add_card_inter crossing near
    have k := Finset.card_le_card (Finset.inter_subset_right (s₁ := crossing) (s₂ := near))
    dsimp [far]; omega
  have cs : (crossing.card:ℝ) ≤ near.card+(far.card:ℝ) := by exact_mod_cast size
  exact cs.trans (add_le_add_right ((le_div_iff₀ (sq_pos_of_pos hε)).mpr cost) _)


/-- A strict initial residual contraction makes the empirical Gram invertible,
including when the parameter dimension is larger than the sample dimension. -/
theorem gram_ker [FiniteDimensional ℝ H] (A : E →L[ℝ] H) (h : ℝ)
    (strict : ‖linearStep A h‖ < 1) : (A.comp (A†)).ker = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have zero : A ((A†) v) = 0 := hv
  have same : linearStep A h v = v := by simp [linearStep,zero]
  have b := (linearStep A h).le_opNorm v
  rw [same] at b
  by_contra hn
  have pos := norm_pos_iff.mpr hn
  nlinarith [mul_pos (sub_pos.mpr strict) pos]

/-- The inverse Gram, constructed from contraction without any separately
supplied pseudoinverse hypothesis. -/
def gramEquiv [FiniteDimensional ℝ H] (A : E →L[ℝ] H) (h : ℝ)
    (strict : ‖linearStep A h‖ < 1) : H ≃L[ℝ] H :=
  ContinuousLinearEquiv.ofBijective (A.comp (A†)) (gram_ker A h strict)
    (LinearMap.ker_eq_bot_iff_range_eq_top.mp (gram_ker A h strict))

theorem gram_strict {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) : ‖linearStep A h‖ < 1 := by
  have pos : 0 ≤ h*(2*‖A‖+δ)*δ := by positivity [C.step_pos]
  linarith [C.contraction,C.ratio_lt]

/-- Actual squared displacement versus the empirical inverse-Gram quadratic
form. The inverse and reference interpolant are constructed in the theorem. -/
theorem vector_and_quadratic_budget [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) :
    let K := gramEquiv A h (gram_strict C)
    let B := (A†).comp K.symm.toContinuousLinearMap
    let e := Real.sqrt ((‖B‖*(δ*R))^2+(h*δ*‖F 0‖/(1-q))^2)
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧ ‖D-B (-F 0)‖ ≤ e ∧
      |‖D‖^2-inner ℝ (F 0) (K.symm (F 0))| ≤ 2*‖B (F 0)‖*e+e^2 := by
  intro K B e
  let S := (A†).range
  have row (y : H) : (A†) y ∈ S := ⟨y,rfl⟩
  have cancel (y : H) : A (B y) = y := K.apply_symm_apply y
  have proj (x : E) : B (A x) = S.starProjection x := by
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (row _)
    rintro _ ⟨y,rfl⟩
    change inner ℝ (x-B (A x)) ((A†) y) = 0
    rw [A.adjoint_inner_right,map_sub,cancel,sub_self,inner_zero_left]
  obtain ⟨D,lim,hit,err⟩ := limiting_movement C S B proj row (B (-F 0)) (row _) (cancel _)
  have close : ‖D - B (-F 0)‖ ≤ e := (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr err
  have bound := (TrainingPath.budget_error (ContinuousLinearMap.id ℝ E) D (B (-F 0)) e close)
  have normB : ‖B (F 0)‖^2 = inner ℝ (F 0) (K.symm (F 0)) := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (B (F 0)) ((A†) (K.symm (F 0))) = _
    rw [A.adjoint_inner_right,cancel]
  refine ⟨D,lim,hit,close,?_⟩
  have direct : |‖D‖^2-‖B (-F 0)‖^2| ≤ 2*‖B (-F 0)‖*e+e^2 := by
    let I := ContinuousLinearMap.id ℝ E
    have small : ‖I‖ ≤ 1 := I.opNorm_le_bound zero_le_one (fun x => by simp [I])
    have en : 0 ≤ e := (norm_nonneg _).trans close
    have le : ‖I‖*e ≤ e := by simpa using mul_le_mul_of_nonneg_right small en
    apply bound.trans
    exact add_le_add (mul_le_mul_of_nonneg_left le (by positivity))
      (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) en) le 2)
  simpa only [map_neg,norm_neg,normB] using direct

theorem quadratic_budget [FiniteDimensional ℝ E] [FiniteDimensional ℝ H]
    {F : E → H} {J : E → E →L[ℝ] H} {A : E →L[ℝ] H}
    {h R q : ℝ} {δ : ℝ≥0} (C : BallControl F J A h R q δ) :
    let K := gramEquiv A h (gram_strict C)
    let B := (A†).comp K.symm.toContinuousLinearMap
    let e := Real.sqrt ((‖B‖*(δ*R))^2+(h*δ*‖F 0‖/(1-q))^2)
    ∃ D, Tendsto (gd F J h) atTop (𝓝 D) ∧ F D = 0 ∧
      |‖D‖^2-inner ℝ (F 0) (K.symm (F 0))| ≤ 2*‖B (F 0)‖*e+e^2 := by
  obtain ⟨D,lim,fit,_,error⟩ := vector_and_quadratic_budget C
  exact ⟨D,lim,fit,error⟩

/-- Co-coercivity of an empirical least-squares Gram gives an elementary
contraction margin at every step h≤1/‖A‖², including the reciprocal step. -/
theorem frame_contraction (A : E →L[ℝ] H) (h l : ℝ) (hp : 0≤h)
    (step : h*‖A‖^2 ≤ 1) (hl : h*l ≤ 1)
    (frame : ∀ y, l*‖y‖^2 ≤ ‖(A†) y‖^2) : ‖linearStep A h‖ ≤ 1-h*l/2 := by
  have qp : 0 ≤ 1-h*l/2 := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ qp
  intro v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg qp (norm_nonneg v))).mp
  change ‖v-h • A ((A†) v)‖^2 ≤ _
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp,
    mul_pow,← A.adjoint_inner_left,real_inner_self_eq_norm_sq]
  have b := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm ((A†) v)) 2
  rw [mul_pow] at b
  have hb := mul_le_mul_of_nonneg_left b (sq_nonneg h)
  have hx := mul_le_mul_of_nonneg_right step (mul_nonneg hp (sq_nonneg ‖(A†) v‖))
  have hy := mul_le_mul_of_nonneg_left (frame v) hp
  nlinarith only [hb,hx,hy,sq_nonneg (h*l*‖v‖)]

/-- Norm of the transported inverse in the movement bound, using only the
initial lower frame constant. -/
theorem inverse_norm [FiniteDimensional ℝ H] (A : E →L[ℝ] H) (h : ℝ)
    (strict : ‖linearStep A h‖ < 1) (l : ℝ) (hl : 0<l)
    (frame : ∀ y, l*‖y‖^2 ≤ ‖(A†) y‖^2) :
    ‖(A†).comp (gramEquiv A h strict).symm.toContinuousLinearMap‖ ≤ 1/Real.sqrt l := by
  let K := gramEquiv A h strict
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  let z := K.symm y
  let a := (A†) z
  have cancel : A a=y := K.apply_symm_apply y
  have id : ‖a‖^2 = inner ℝ y z := by
    rw [← real_inner_self_eq_norm_sq]; change inner ℝ a ((A†) z) = _
    rw [A.adjoint_inner_right,cancel]
  have cauchy := (le_abs_self (inner ℝ y z)).trans (abs_real_inner_le_norm y z)
  rw [← id] at cauchy
  change ‖a‖ ≤ 1/Real.sqrt l * ‖y‖
  by_cases hz : ‖z‖ = 0
  · have zero := norm_eq_zero.mp hz
    simp [a,zero]; positivity
  have zp := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
  have zb : l*‖z‖ ≤ ‖y‖ := le_of_mul_le_mul_right
    (show l*‖z‖*‖z‖ ≤ ‖y‖*‖z‖ by nlinarith only [frame z,cauchy]) zp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,div_pow,one_pow,Real.sq_sqrt hl.le,div_mul_eq_mul_div,one_mul]
  apply (le_div_iff₀ hl).mpr
  have aa := mul_le_mul_of_nonneg_right cauchy hl.le
  nlinarith only [aa,mul_le_mul_of_nonneg_left zb (norm_nonneg y)]

end NonlinearBudget
