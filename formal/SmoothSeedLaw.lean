module

public import TwoLayerLimit
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.StrongLaw
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Tactic

/-! The iid Gaussian neuron coupling for a smooth two-layer network.
Both initial population matrices are actual Gaussian expectations. -/
@[expose] public section
noncomputable section
namespace SmoothSeedLaw
open TwoLayerNetwork TwoLayerBudget MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal InnerProduct Topology
variable {d k : ℕ}
abbrev Neuron (d : ℕ) := ℝ × Space d
abbrev Draws (d : ℕ) := ℕ → Neuron d
def neuronLaw (d : ℕ) := (gaussianReal 0 1).prod (stdGaussian (Space d))
instance : IsProbabilityMeasure (neuronLaw d) := inferInstanceAs
  (IsProbabilityMeasure ((gaussianReal 0 1).prod (stdGaussian (Space d))))
def law (d : ℕ) := Measure.infinitePi (fun _ : ℕ => neuronLaw d)
instance : IsProbabilityMeasure (law d) := inferInstanceAs (IsProbabilityMeasure
  (Measure.infinitePi fun _ : ℕ => neuronLaw d))

def packed (n : ℕ) (ω : Draws d) : Params n d := WithLp.toLp 2 fun p =>
  Fin.cases (ω p.1).1 (fun j => (ω p.1).2 j) p.2

@[simp] theorem packed_a (n : ℕ) (ω : Draws d) (i : Fin n) : readout (packed n ω) i=(ω i).1 := rfl
@[simp] theorem packed_w (n : ℕ) (ω : Draws d) (i : Fin n) : TwoLayerNetwork.hidden (packed n ω) i=(ω i).2 := rfl

theorem eval_law (i : ℕ) : HasLaw (fun ω : Draws d => ω i) (neuronLaw d) (law d) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => neuronLaw d) i).hasLaw

theorem a_law (i : ℕ) : HasLaw (fun ω : Draws d => (ω i).1) (gaussianReal 0 1) (law d) :=
  (measurePreserving_fst (μ := gaussianReal 0 1) (ν := stdGaussian (Space d))).hasLaw.comp (eval_law i)

theorem iid_observable {T : Type*} [MeasurableSpace T] (f : Neuron d → T) (mf : Measurable f) :
    iIndepFun (fun i (ω : Draws d) => f (ω i)) (law d) ∧
      ∀ i : ℕ, IdentDistrib (fun ω : Draws d => f (ω i)) (fun ω => f (ω 0)) (law d) (law d) := by
  refine ⟨iIndepFun_infinitePi (fun _ => mf),?_⟩
  intro i
  exact ((eval_law i).identDistrib (eval_law 0)).comp mf

theorem observable_lln {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
    [MeasurableSpace T] [BorelSpace T] (f : Neuron d → T) (mf : Measurable f)
    (hf : Integrable f (neuronLaw d)) : ∀ᵐ ω ∂law d,
      Tendsto (fun n : ℕ => (n:ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (ω i)) atTop
        (𝓝 (∫ t, f t ∂neuronLaw d)) := by
  obtain ⟨ind,ident⟩ := iid_observable f mf
  have h := strong_law_ae (μ := law d) (fun i ω => f (ω i)) ((eval_law 0).integrable_comp hf)
    (fun _ _ hij => ind.indepFun hij) ident
  simpa only [show (∫ ω : Draws d, f (ω 0) ∂law d) = ∫ t, f t ∂neuronLaw d from
    (eval_law 0).integral_comp hf.aestronglyMeasurable] using h

structure Activation (φ g : ℝ → ℝ) (L₁ L₂ : ℝ) : Prop where
  first : ∀ z, HasDerivAt φ (g z) z
  L₁_nonneg : 0≤L₁
  L₂_nonneg : 0≤L₂
  bounded : ∀ z, |g z|≤L₁
  lipschitz : ∀ u v, |g u-g v| ≤ L₂*|u-v|

theorem activation_of_second {φ g g₂ : ℝ → ℝ} {L₁ L₂ : ℝ} (h1 : 0≤L₁) (h2 : 0≤L₂)
    (f : ∀ z, HasDerivAt φ (g z) z) (gg : ∀ z, HasDerivAt g (g₂ z) z)
    (b1 : ∀ z, |g z|≤L₁) (b2 : ∀ z, |g₂ z|≤L₂) : Activation φ g L₁ L₂ where
  first := f
  L₁_nonneg := h1
  L₂_nonneg := h2
  bounded := b1
  lipschitz u v := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (gg z).hasDerivWithinAt) (fun z _ => b2 z) (mem_univ v) (mem_univ u)

def softplus (z : ℝ) := Real.log (1+Real.exp z)
def sigmoid (z : ℝ) := Real.exp z/(1+Real.exp z)

theorem softplus_activation : Activation softplus sigmoid 1 (1/4) := by
  apply activation_of_second (g₂ := fun z => Real.exp z/(1+Real.exp z)^2) (by norm_num) (by norm_num)
  · intro z
    change HasDerivAt (fun u : ℝ => Real.log (1+Real.exp u)) _ _
    simpa [sigmoid] using ((Real.hasDerivAt_exp z).const_add 1).log (by positivity)
  · intro z
    have der := (Real.hasDerivAt_exp z).div ((Real.hasDerivAt_exp z).const_add 1) (by positivity)
    convert der using 1
    · rfl
    · ring
  · intro z
    rw [sigmoid,abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr (by linarith)
  · intro z
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (1-Real.exp z)]

def H (φ : ℝ → ℝ) (b : ℝ) (x w : Space d) := φ (b*inner ℝ w x)
def signal (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (t : Neuron d) : Space k :=
  WithLp.toLp 2 (fun j => t.1*H φ (b j) (x j) t.2)
def Cmat (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) : Matrix (Fin k) (Fin k) ℝ :=
  fun j l => ∫ w, H φ (b j) (x j) w*H φ (b l) (x l) w ∂stdGaussian (Space d)
def atomEntry (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d)
    (i j : Fin k) (t : Neuron d) :=
  H φ (b i) (x i) t.2*H φ (b j) (x j) t.2 +
    (b i*b j*inner ℝ (x i) (x j))*(t.1^2*(H g (b i) (x i) t.2*H g (b j) (x j) t.2))
def Γmat (φ g : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) : Matrix (Fin k) (Fin k) ℝ :=
  fun j l => Cmat φ b x j l + (b j*b l*inner ℝ (x j) (x l))*
    ∫ w, H g (b j) (x j) w*H g (b l) (x l) w ∂stdGaussian (Space d)

theorem feature_mem {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : ℝ) (x : Space d) : MemLp (H φ b x) 2 (stdGaussian (Space d)) := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr fun z => (h.first z).continuousAt
  have lip (u v : ℝ) : |φ u-φ v|≤L₁*|u-v| := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (h.first z).hasDerivWithinAt) (fun z _ => h.bounded z) (mem_univ v) (mem_univ u)
  let T : Space d →L[ℝ] ℝ := b • innerSL ℝ x
  have m := (IsGaussian.memLp_dual (stdGaussian (Space d)) T 2 (by norm_num)).norm.const_mul L₁
  have upper := m.add (memLp_const (|φ 0|))
  refine upper.mono' (by unfold H;fun_prop) (ae_of_all _ fun w => ?_)
  have eq : T w = b*inner ℝ w x := by simp [T,real_inner_comm]
  change |φ (b*inner ℝ w x)| ≤ L₁*‖T w‖+|φ 0|
  rw [eq,Real.norm_eq_abs]
  have bnd := lip (b*inner ℝ w x) 0
  rw [sub_zero] at bnd
  have tri := abs_sub_le (φ (b*inner ℝ w x)) (φ 0) 0
  simp only [sub_zero] at tri
  exact tri.trans (add_le_add bnd le_rfl)

theorem g_continuous {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂) : Continuous g :=
  (show LipschitzWith ⟨L₂,h.L₂_nonneg⟩ g from LipschitzWith.of_dist_le_mul
    (fun u v => by rw [Real.dist_eq,Real.dist_eq];exact h.lipschitz u v)).continuous

theorem slope_mem {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : ℝ) (x : Space d) : MemLp (H g b x) 2 (stdGaussian (Space d)) := by
  have cg := g_continuous h
  exact (memLp_const L₁).mono' (by unfold H;fun_prop) (ae_of_all _ fun w => h.bounded _)

theorem normal_squared : Integrable (fun a : ℝ => a^2) (gaussianReal 0 1) ∧
    ∫ a : ℝ, a^2 ∂gaussianReal 0 1 = 1 := by
  have m := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)
  refine ⟨(memLp_two_iff_integrable_sq m.aestronglyMeasurable).mp m,?_⟩
  have t := variance_eq_integral (μ:=gaussianReal 0 1) (measurable_id'.aemeasurable (α:=ℝ))
  simpa [variance_fun_id_gaussianReal,integral_id_gaussianReal] using t.symm

theorem atom_integral {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) (i j : Fin k) :
    Integrable (atomEntry φ g b x i j) (neuronLaw d) ∧
      ∫ t, atomEntry φ g b x i j t ∂neuronLaw d = Γmat φ g b x i j := by
  let hprod := fun w => H φ (b i) (x i) w*H φ (b j) (x j) w
  let gprod := fun w => H g (b i) (x i) w*H g (b j) (x j) w
  have e₁ : Integrable hprod (stdGaussian (Space d)) := (feature_mem h _ _).integrable_mul (feature_mem h _ _)
  have e₂ : Integrable gprod (stdGaussian (Space d)) := (slope_mem h _ _).integrable_mul (slope_mem h _ _)
  have u : Integrable (fun t : Neuron d => hprod t.2) (neuronLaw d) := e₁.comp_snd _
  have v := normal_squared.1.mul_prod e₂
  let B := b i*b j*inner ℝ (x i) (x j)
  refine ⟨u.add (v.const_mul B),?_⟩
  change (∫ t : Neuron d, hprod t.2+B*(t.1^2*gprod t.2) ∂(gaussianReal 0 1).prod (stdGaussian (Space d))) = _
  unfold neuronLaw at u
  rw [integral_add u (v.const_mul B),integral_fun_snd,integral_const_mul,integral_prod_mul (fun a : ℝ => a^2) gprod,normal_squared.2]
  simp only [probReal_univ,one_smul,one_mul]
  rfl


theorem signal_cont {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : Continuous (signal φ b x) := by
  have hc : Continuous φ := continuous_iff_continuousAt.mpr fun z => (h.first z).continuousAt
  unfold signal H; fun_prop

theorem signal_mem {φ g : ℝ → ℝ} {L₁ L₂ : ℝ} (h : Activation φ g L₁ L₂)
    (b : Fin k → ℝ) (x : Fin k → Space d) : MemLp (signal φ b x) 2 (neuronLaw d) := by
  apply MemLp.of_eval_piLp
  intro i
  have fm := feature_mem h (b i) (x i)
  have fi := (memLp_two_iff_integrable_sq fm.aestronglyMeasurable).mp fm
  have c := signal_cont h b x
  apply (memLp_two_iff_integrable_sq ((EuclideanSpace.proj i : Space k →L[ℝ] ℝ).continuous.comp c).aestronglyMeasurable).mpr
  unfold neuronLaw
  have aa := normal_squared.1.mul_prod fi
  convert aa using 1
  ext t; change (t.1*H φ (b i) (x i) t.2)^2 = _;ring

theorem signal_mean (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (i : Fin k) :
    ∫ t, signal φ b x t i ∂neuronLaw d = 0 := by
  change (∫ t : ℝ × Space d, t.1*H φ (b i) (x i) t.2 ∂(gaussianReal 0 1).prod (stdGaussian (Space d)))=0
  rw [integral_prod_mul (fun a : ℝ => a) (H φ (b i) (x i)),integral_id_gaussianReal,zero_mul]

theorem signal_second (φ : ℝ → ℝ) (b : Fin k → ℝ) (x : Fin k → Space d) (i j : Fin k) :
    ∫ t, signal φ b x t i*signal φ b x t j ∂neuronLaw d = Cmat φ b x i j := by
  let f := fun w => H φ (b i) (x i) w*H φ (b j) (x j) w
  have eq (t : Neuron d) : signal φ b x t i*signal φ b x t j = t.1^2*f t.2 := by
    dsimp [signal,f];ring
  simp_rw [eq]
  unfold neuronLaw
  rw [integral_prod_mul (fun a : ℝ => a^2) f,normal_squared.2,one_mul]
  rfl

end SmoothSeedLaw
