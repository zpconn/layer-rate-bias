module

public import TwoLayerInitialization
import Mathlib.Tactic

/-! Width-uniform initial prediction and Jacobian bounds under the unconditioned
Gaussian initialization. Readout sign symmetry cancels the off-diagonal terms
in the output second moment. -/
@[expose] public section
noncomputable section
namespace TwoLayerMoments
open MeasureTheory ProbabilityTheory Set TwoLayerNetwork TwoLayerInitialization TwoLayerBudget
open scoped NNReal InnerProduct
variable {d n k : ℕ}

def flipReadout (i : Fin n) : Params n d ≃ₗᵢ[ℝ] Params n d :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun p => if p=(i,0) then .neg ℝ else .refl ℝ ℝ)

theorem flip_coord (z : Params n d) (i : Fin n) (p : Fin n × Fin (d+1)) :
    (flipReadout i z) p = if p=(i,0) then -z p else z p := by
  simp only [flipReadout,LinearIsometryEquiv.piLpCongrRight_apply,PiLp.toLp_apply]
  split_ifs <;> rfl

theorem flip_hidden (z : Params n d) (i j : Fin n) :
    TwoLayerNetwork.hidden (flipReadout i z) j = TwoLayerNetwork.hidden z j := by
  ext l
  change (flipReadout i z) (j,l.succ) = _
  simp [flip_coord,TwoLayerNetwork.hidden]

def atom (φ : ℝ → ℝ) (b : ℝ) (x : Space d) (i : Fin n) (z : Params n d) :=
  readout z i*φ (b*inner ℝ (TwoLayerNetwork.hidden z i) x)

theorem atom_cross_zero (φ : ℝ → ℝ) (meas : Measurable φ) (b : ℝ) (x : Space d)
    (i j : Fin n) (neq : i≠j) :
    ∫ z, atom φ b x i z*atom φ b x j z ∂stdGaussian (Params n d) = 0 := by
  let F := fun z => atom φ b x i z*atom φ b x j z
  have mF : Measurable F := by unfold F atom readout TwoLayerNetwork.hidden; fun_prop
  have e : ∀ z, F (flipReadout i z) = -F z := by
    intro z; simp [F,atom,readout,flip_coord,flip_hidden,Ne.symm neq]
  have h := integral_map (μ := stdGaussian (Params n d)) (by fun_prop : AEMeasurable (flipReadout i)
    (stdGaussian (Params n d))) (mF.aestronglyMeasurable (μ := (stdGaussian (Params n d)).map (flipReadout i)))
  rw [stdGaussian_map] at h
  simp_rw [e] at h
  rw [integral_neg] at h
  change ∫ z, F z ∂stdGaussian (Params n d) = 0
  linarith

def gaussianFourth := ∫ x : ℝ, x^4 ∂gaussianReal 0 1

private theorem gauss4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ℝ)
    (law : HasLaw G (gaussianReal 0 1) μ) :
    Integrable (fun z => G z^4) μ ∧ ∫ z, G z^4 ∂μ = gaussianFourth := by
  have m : MemLp G 4 μ := law.memLp (memLp_id_gaussianReal' 4 (by norm_num))
  have h := (m.integrable_norm_pow (by decide : (4:ℕ)≠0))
  have p (x : ℝ) : ‖x‖^4=x^4 := by rw [Real.norm_eq_abs,show 4=2*2 by decide,pow_mul,sq_abs,pow_mul]
  simp_rw [p] at h
  exact ⟨h,law.integral_comp (f := fun x : ℝ => x^4) (by fun_prop)⟩

/-- The second moment of a single unit is bounded even without using
independence between its readout and its scalar preactivation. -/
theorem atom_second (α b : ℝ) (hα : 0≤α) (hα' : α≤1) (x : Space d) (hx : ‖x‖=1) (i : Fin n) :
    let F := atom (leaky α) b x i
    MemLp F 2 (stdGaussian (Params n d)) ∧
    (∫ z, F z^2 ∂stdGaussian (Params n d)) ≤ b^2*gaussianFourth := by
  intro F
  let μ := stdGaussian (Params n d)
  let A := fun z : Params n d => readout z i
  let G := fun z : Params n d => inner ℝ (TwoLayerNetwork.hidden z i) x
  have a := gauss4 μ A (readout_law i)
  have g := gauss4 μ G (preactivation_law i x hx)
  let U := fun z => (b^2/2)*(A z^4+G z^4)
  have iu : Integrable U μ := (a.1.add g.1).const_mul _
  have eu : ∫ z, U z ∂μ = b^2*gaussianFourth := by
    rw [show U = _ from rfl,integral_const_mul,integral_add a.1 g.1,a.2,g.2]; ring
  have point (z) : F z^2 ≤ U z := by
    have lip := leaky_lipschitz α (b*G z) 0 hα hα'
    rw [show leaky α 0=0 by simp [leaky],sub_zero,sub_zero] at lip
    have L : (leaky α (b*G z))^2 ≤ (b*G z)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) lip 2
    have H := mul_le_mul_of_nonneg_left L (sq_nonneg (A z))
    change (A z*leaky α (b*G z))^2 ≤ (b^2/2)*(A z^4+G z^4)
    nlinarith only [H,mul_nonneg (sq_nonneg b) (sq_nonneg ((A z)^2-(G z)^2))]
  have lip : LipschitzWith 1 (leaky α) := LipschitzWith.of_dist_le_mul fun u v => by
    simpa [Real.dist_eq] using leaky_lipschitz α u v hα hα'
  have ml := lip.continuous.measurable
  have mf : Measurable F := by change Measurable (fun z : Params n d => readout z i*leaky α (b*inner ℝ (TwoLayerNetwork.hidden z i) x)); unfold readout TwoLayerNetwork.hidden; fun_prop
  have fi : Integrable (fun z => F z^2) μ := iu.mono' (by fun_prop) (ae_of_all _ fun z => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (F z))] using point z)
  exact ⟨(memLp_two_iff_integrable_sq mf.aestronglyMeasurable).mpr fi,(integral_mono fi iu point).trans_eq eu⟩


/-- The cross terms vanish by a sign symmetry of the exact seed law. The
initial prediction second moment is consequently bounded uniformly in width. -/
theorem initial_prediction_second (α b : ℝ) (hα : 0≤α) (hα' : α≤1) (x : Space d) (hx : ‖x‖=1)
    (hn : 0<n) :
    let f := fun z : Params n d => pred (leaky α) b x (readout z) (TwoLayerNetwork.hidden z)
    MemLp f 2 (stdGaussian (Params n d)) ∧
    (∫ z, f z^2 ∂stdGaussian (Params n d)) ≤ b^2*gaussianFourth := by
  intro f
  let μ := stdGaussian (Params n d)
  let V := atom (leaky α) b x (n := n)
  have a (i : Fin n) := atom_second α b hα hα' x hx i
  have cs (i j : Fin n) : Integrable (fun z => V i z*V j z) μ :=
    (a i).1.integrable_mul (a j).1
  have id (z) : f z^2 = (∑ i, ∑ j, V i z*V j z)/n := by
    change ((∑ i, V i z)/Real.sqrt n)^2 = _
    rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _),sq,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have mf := memLp_finsetSum (μ:=μ) Finset.univ (fun i _ => (a i).1)
  have main : MemLp f 2 μ := by
    simpa only [f,pred,atom,div_eq_mul_inv] using mf.mul_const (Real.sqrt n)⁻¹
  refine ⟨main,?_⟩
  simp_rw [id]
  rw [integral_div,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => cs i j))]
  simp_rw [integral_finsetSum _ (fun j _ => cs _ j)]
  have ml : Measurable (leaky α) := (show LipschitzWith 1 (leaky α) from
    LipschitzWith.of_dist_le_mul (fun u v => by simpa [Real.dist_eq] using leaky_lipschitz α u v hα hα')).continuous.measurable
  apply (div_le_iff₀ (by exact_mod_cast hn : 0<(n:ℝ))).mpr
  have row (i : Fin n) : ∑ j, (∫ z, V i z*V j z ∂μ) ≤ b^2*gaussianFourth := by
    rw [Finset.sum_eq_single i]
    · simpa only [←sq] using (a i).2
    · intro j _ hj; exact atom_cross_zero (leaky α) ml b x i j hj.symm
    · simp
  exact (Finset.sum_le_sum (s := Finset.univ) (fun i _ => row i)).trans_eq (by simp [mul_comm])

/-- An explicit width-uniform Markov bound for the initial residual in the
normalization used by the training theorem. -/
theorem residual_initial_tail (α : ℝ) (hα : 0≤α) (hα' : α≤1) (b : Fin k → ℝ)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) (y : Space k) (hn : 0<n) (U : ℝ) (hU : 0<U) :
    (stdGaussian (Params n d)).real {z | U ≤ ‖residual (leaky α) b x y z 0‖^2} ≤
      (2*(∑ j, (b j)^2)*gaussianFourth + 2*‖y‖^2)/U := by
  let μ := stdGaussian (Params n d)
  let f := fun j (z : Params n d) => pred (leaky α) (b j) (x j) (readout z) (TwoLayerNetwork.hidden z)
  let G := fun z => ∑ j, (2*(f j z)^2+2*(y j)^2)
  have e (j) := initial_prediction_second α (b j) hα hα' (x j) (hx j) hn
  have sqint (j) : Integrable (fun z => f j z^2) μ := (memLp_two_iff_integrable_sq (e j).1.aestronglyMeasurable).mp (e j).1
  have each (j) : Integrable (fun z => 2*(f j z)^2+2*(y j)^2) μ :=
    ((sqint j).const_mul 2).add (integrable_const _)
  have gInt : Integrable G μ := integrable_finsetSum _ (fun j _ => each j)
  have point (z : Params n d) : ‖residual (leaky α) b x y z 0‖^2 ≤ G z := by
    rw [EuclideanSpace.real_norm_sq_eq]; apply Finset.sum_le_sum;intro j _
    change (pred (leaky α) (b j) (x j) (readout (z+0)) (TwoLayerNetwork.hidden (z+0))-y j)^2 ≤ _
    rw [add_zero]; change (f j z-y j)^2 ≤ _; nlinarith [sq_nonneg (f j z+y j)]
  apply (measureReal_mono (fun z hz => le_trans hz (point z))).trans
  apply (le_div_iff₀ hU).mpr
  have mark := mul_meas_ge_le_integral_of_nonneg (μ:=μ) (f:=G)
    (ae_of_all _ fun z => (sq_nonneg _).trans (point z)) gInt U
  rw [mul_comm]
  apply mark.trans
  rw [show G = _ from rfl,integral_finsetSum _ (fun j _ => each j),EuclideanSpace.real_norm_sq_eq]
  calc _ ≤ ∑ j, (2*((b j)^2*gaussianFourth)+2*(y j)^2) := by
        apply Finset.sum_le_sum;intro j _
        rw [integral_add ((sqint j).const_mul _) (integrable_const _),integral_const_mul,integral_const]
        simp only [probReal_univ,one_smul]
        linarith [(e j).2]
       _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul]; ring


theorem row_upper (α b : ℝ) (α0 : 0≤α) (α1 : α≤1) (x : Space d) (hx : ‖x‖=1)
    (z : Params n d) (s : Fin n → ℝ) (sl : ∀ i, Slope α (pre b x z i) (s i)) :
    ‖rawRow (leaky α) b x (readout z) (TwoLayerNetwork.hidden z) s‖^2 ≤
      b^2*(∑ i, ((inner ℝ (TwoLayerNetwork.hidden z i) x)^2+(readout z i)^2)) := by
  let Z := rawRow (leaky α) b x (0 : Fin n → ℝ) (0 : Fin n → Space d) s
  have null : Z=0 := by ext p; rcases p with ⟨i,l⟩;refine Fin.cases ?_ (fun j => ?_) l <;> simp [Z,rawRow,leaky]
  have eq := row_identity (leaky α) b x (0 : Fin n → ℝ) (readout z) (0 : Fin n → Space d)
    (TwoLayerNetwork.hidden z) s s
  rw [show rawRow (leaky α) b x (0 : Fin n → ℝ) (0 : Fin n → Space d) s = 0 from null,sub_zero] at eq
  rw [eq,Finset.mul_sum]
  apply Finset.sum_le_sum;intro i _
  have f := leaky_lipschitz α (b*inner ℝ (TwoLayerNetwork.hidden z i) x) 0 α0 α1
  rw [show leaky α 0=0 by simp [leaky],sub_zero,sub_zero] at f
  have fb := pow_le_pow_left₀ (abs_nonneg _) f 2
  rw [sq_abs,sq_abs,mul_pow] at fb
  have ss := pow_le_pow_left₀ (α0.trans (sl i).1) (sl i).2.1 2
  simp only [Pi.zero_apply,inner_zero_left,mul_zero,show leaky α 0=0 by simp [leaky],
    sub_zero,zero_mul,norm_smul,Real.norm_eq_abs,hx,mul_one,sq_abs,mul_pow,one_pow] at ss ⊢
  nlinarith only [fb,mul_le_mul_of_nonneg_left ss (mul_nonneg (sq_nonneg b) (sq_nonneg (readout z i)))]

theorem matrix_upper (r : Fin k → Params n d) (hn : 0<n) :
    ‖matrixOp r‖^2 ≤ (∑ j, ‖r j‖^2)/n := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  let t := (∑ j, ‖r j‖^2)/(n:ℝ)
  have ht : 0≤t := div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) np.le
  let δ : ℝ≥0 := ⟨Real.sqrt t,Real.sqrt_nonneg _⟩
  have mass : (∑ j, ‖r j-(0:Params n d)‖^2) ≤ n*(δ:ℝ)^2 := by
    simp only [sub_zero]
    change _ ≤ (n:ℝ)*(Real.sqrt t)^2
    rw [Real.sq_sqrt ht]; dsimp [t]; field_simp; rfl
  have eq : matrixOp (fun _ : Fin k => (0:Params n d)) = 0 := by
    ext v j; simp [matrix_apply]
  have le := frobenius r (fun _ => 0) δ mass
  rw [eq,sub_zero] at le
  exact (pow_le_pow_left₀ (norm_nonneg _) le 2).trans_eq (Real.sq_sqrt ht)

private theorem gauss2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ℝ)
    (law : HasLaw G (gaussianReal 0 1) μ) :
    Integrable (fun z => G z^2) μ ∧ ∫ z, G z^2 ∂μ = 1 := by
  have m : MemLp G 2 μ := law.memLp (memLp_id_gaussianReal' 2 (by norm_num))
  refine ⟨(memLp_two_iff_integrable_sq m.aestronglyMeasurable).mp m,(law.integral_comp
    (f := fun x : ℝ => x^2) (by fun_prop)).trans ?_⟩
  have b := variance_eq_integral (μ := gaussianReal 0 1) (measurable_id'.aemeasurable (α := ℝ))
  simpa [variance_fun_id_gaussianReal,integral_id_gaussianReal] using b.symm

/-- Width-uniform upper tail of the actual initial operator norm, for every
selection of compatible gates (including nonmeasurable conventions at zero). -/
theorem gram_upper_tail (α : ℝ) (hα : 0≤α) (hα' : α≤1) (b : Fin k → ℝ)
    (x : Fin k → Space d) (hx : ∀ j, ‖x j‖=1) (hn : 0<n)
    (s : Params n d → Fin k → Fin n → ℝ) (g : ∀ z, gate α b x z (s z)) (U : ℝ) (hU : 0<U) :
    (stdGaussian (Params n d)).real {z | U ≤ ‖matrixOp (rows (leaky α) b x z (s z))‖^2}
      ≤ (2*∑ j, (b j)^2)/U := by
  let μ := stdGaussian (Params n d)
  let a := fun i (z : Params n d) => readout z i
  let V := fun j i (z : Params n d) => inner ℝ (TwoLayerNetwork.hidden z i) (x j)
  let W := fun z : Params n d => (∑ j, (b j)^2*∑ i, (V j i z^2+a i z^2))/(n:ℝ)
  have M (z) : ‖matrixOp (rows (leaky α) b x z (s z))‖^2 ≤ W z :=
    (matrix_upper _ hn).trans (div_le_div_of_nonneg_right (Finset.sum_le_sum (s:=Finset.univ)
      (fun j _ => row_upper α (b j) hα hα' (x j) (hx j) z _ (g z j))) (Nat.cast_nonneg n))
  have af (i) := gauss2 μ (a i) (readout_law i)
  have vf (j i) := gauss2 μ (V j i) (preactivation_law i (x j) (hx j))
  have atomI (j : Fin k) (i : Fin n) : Integrable (fun z => V j i z^2+a i z^2) μ := (vf j i).1.add (af i).1
  have rowI (j : Fin k) : Integrable (fun z => (b j)^2*(∑ i, (V j i z^2+a i z^2))) μ :=
    (integrable_finsetSum Finset.univ (fun i _ => atomI j i)).const_mul ((b j)^2)
  have int : Integrable W μ := (integrable_finsetSum _ (fun j _ => rowI j)).div_const _
  have mean : ∫ z, W z ∂μ = 2*∑ j, (b j)^2 := by
    rw [show W = _ from rfl,integral_div,integral_finsetSum _ (fun j _ => rowI j)]
    simp_rw [integral_const_mul,integral_finsetSum _ (fun i _ => atomI _ i),
      integral_add (vf _ _).1 (af _).1,(af _).2,(vf _ _).2]
    simp [← Finset.sum_mul]; field_simp; norm_num
  apply (measureReal_mono (fun z hz => le_trans hz (M z))).trans
  apply (le_div_iff₀ hU).mpr
  rw [mul_comm,← mean]
  exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun z => (sq_nonneg _).trans (M z))) int U

end TwoLayerMoments
