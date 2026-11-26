module

public import CirclePathSelection
public import CircleEulerPolygon
public import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-! Integral support inequalities for a differential inclusion. These are
closed conditions in locally uniform path topology. For locally Lipschitz
paths in finite dimensions they characterize the almost-everywhere inclusion. -/

@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace CircleInclusionExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every velocity over this open portion of state space obeys a strict
linear upper bound. Upper hemicontinuity makes the portion open. -/
def safeRegion (F : E → Set E) (l : E →L[ℝ] ℝ) (c : ℝ) : Set E :=
  F ⁻¹' Iic (l ⁻¹' Iio c)

theorem isOpen_safeRegion {F : E → Set E} (hF : UpperHemicontinuous F)
    (l : E →L[ℝ] ℝ) (c : ℝ) : IsOpen (safeRegion F l c) :=
  (upperHemicontinuous_iff_isOpen_preimage_Iic.mp hF) _ (isOpen_Iio.preimage l.continuous)

/-- Increment tests run over all compact subintervals in the horizon. -/
def SupportPath (F : E → Set E) (T : ℝ) (p : C(ℝ,E)) : Prop :=
  ∀ (l : E →L[ℝ] ℝ) (c a b : ℝ), 0 ≤ a → a ≤ b → b ≤ T →
    MapsTo p (Icc a b) (safeRegion F l c) → l (p b - p a) ≤ c * (b-a)

theorem isClosed_supportPath {F : E → Set E} (hF : UpperHemicontinuous F) (T : ℝ) :
    IsClosed {p : C(ℝ,E) | SupportPath F T p} := by
  simp only [SupportPath, Set.ofPred_forall]
  iterate 7 apply isClosed_iInter; intro _
  rename_i l c a b _ _ _
  simp only [imp_iff_not_or]
  change IsClosed ({p : C(ℝ,E) | MapsTo p (Icc a b) (safeRegion F l c)}ᶜ ∪
    {p : C(ℝ,E) | l (p b - p a) ≤ c * (b-a)})
  exact ((ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (isOpen_safeRegion hF l c)).isClosed_compl).union
    (isClosed_le (l.continuous.comp ((continuous_eval_const b).sub (continuous_eval_const a)))
      continuous_const)

private theorem increment_le_of_velocity {p : C(ℝ,E)} {a b c : ℝ}
    (l : E →L[ℝ] ℝ) (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval p a b)
    (bound : ∀ᵐ t : ℝ, t ∈ Icc a b → ∃ v, HasDerivAt p v t ∧ l v ≤ c) :
    l (p b - p a) ≤ c * (b-a) := by
  have scalar_ac := l.lipschitzWith.comp_absolutelyContinuousOnInterval hac
  let g : ℝ → ℝ := l ∘ p
  have hder : deriv g ≤ᵐ[volume.restrict (Icc a b)] (fun _ => c) := by
    change ∀ᵐ t ∂volume.restrict (Icc a b), deriv g t ≤ c
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [bound] with t ht ht'
    obtain ⟨v, hd, hv⟩ := ht ht'
    have d : HasDerivAt g (l v) t := l.hasFDerivAt.comp_hasDerivAt t hd
    simpa [d.deriv] using hv
  have hbnd := intervalIntegral.integral_mono_ae_restrict hab scalar_ac.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a b) hder
  rw [scalar_ac.integral_deriv_eq_sub, intervalIntegral.integral_const] at hbnd
  simpa only [Function.comp_apply, map_sub, smul_eq_mul, mul_comm] using hbnd

/-- A true absolutely continuous solution satisfies every support test.
Integration takes place only over the tested interval. -/
theorem supportPath_of_inclusion {F : E → Set E} {T : ℝ} {p : C(ℝ,E)}
    (hac : AbsolutelyContinuousOnInterval p 0 T)
    (incl : ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (p t), HasDerivAt p v t) :
    SupportPath F T p := by
  intro l c a b ha hab hb maps
  have sub : uIcc a b ⊆ uIcc 0 T := by
    simpa [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))] using Icc_subset_Icc ha hb
  apply increment_le_of_velocity l hab (hac.mono sub)
  filter_upwards [incl] with t ht hab'
  obtain ⟨v,hv,hp'⟩ := ht ⟨ha.trans hab'.1,hab'.2.trans hb⟩
  exact ⟨v,hp',(show l v < c from maps hab' hv).le⟩

/-- At a differentiability point in the interior of the time interval, the
support tests force the derivative into the closed convex velocity fiber.
The proof separates a proposed derivative outside the fiber and tests
right-hand difference quotients on a neighborhood of the current state. -/
theorem derivative_mem_of_supportPath {F : E → Set E} (hF : UpperHemicontinuous F)
    (hconv : ∀ x, Convex ℝ (F x)) (hclosed : ∀ x, IsClosed (F x))
    {p : C(ℝ,E)} {T t : ℝ} (hp : SupportPath F T p) (ht : t ∈ Ioo 0 T)
    {v : E} (hd : HasDerivAt p v t) : v ∈ F (p t) := by
  by_contra hv
  obtain ⟨l,c,hf,hlen⟩ := geometric_hahn_banach_closed_point (hconv _) (hclosed _) hv
  have hp_safe : t ∈ p ⁻¹' safeRegion F l c := hf
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp
    (((isOpen_safeRegion hF l c).preimage p.continuous).mem_nhds hp_safe)
  have H : ∀ᶠ b : ℝ in 𝓝[>] t, slope (l ∘ p) t b ≤ c := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds ht.2),
      nhdsWithin_le_nhds (ball_mem_nhds t hε)] with b hbt hbT hb
    have hbt' : t < b := hbt
    have hb' : b-t < ε := by simpa [Real.dist_eq, abs_of_pos (sub_pos.mpr hbt')] using hb
    have maps : MapsTo p (Icc t b) (safeRegion F l c) := by
      intro s hs
      apply hball
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1)]
      linarith [hs.2]
    have hinc := hp l c t b ht.1.le hbt'.le (show b < T from hbT).le maps
    rw [slope_def_field]
    exact (div_le_iff₀ (sub_pos.mpr hbt')).mpr (by simpa only [Function.comp_apply, map_sub] using hinc)
  have d : HasDerivAt (l ∘ p) (l v) t := l.hasFDerivAt.comp_hasDerivAt t hd
  exact (not_le.mpr hlen) (le_of_tendsto (d.tendsto_slope.mono_left (nhdsGT_le_nhdsNE t)) H)

/-- Rademacher's theorem gives the almost-everywhere differential inclusion
from the increment tests, on the actual path and with no selected derivative
assumed. Endpoints have zero Lebesgue measure. -/
theorem inclusion_of_lipschitz_supportPath [FiniteDimensional ℝ E] {F : E → Set E}
    (hF : UpperHemicontinuous F) (hconv : ∀ x, Convex ℝ (F x)) (hclosed : ∀ x, IsClosed (F x))
    {p : C(ℝ,E)} {T : ℝ} {L : ℝ≥0} (hlip : LipschitzOnWith L p (Icc 0 T))
    (support : SupportPath F T p) :
    ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (p t), HasDerivAt p v t := by
  filter_upwards [hlip.ae_differentiableWithinAt_of_mem (μ := volume),
      volume.ae_ne (0:ℝ), volume.ae_ne T] with t hdiff hzero hend ht
  have ht' : t ∈ Ioo 0 T := ⟨lt_of_le_of_ne ht.1 hzero.symm, lt_of_le_of_ne ht.2 hend⟩
  have hd := ((hdiff ht).differentiableAt (Icc_mem_nhds ht'.1 ht'.2)).hasDerivAt
  exact ⟨_, derivative_mem_of_supportPath hF hconv hclosed support ht' hd, hd⟩

/-- Uniform limits of actual differential-inclusion solutions with a common
speed bound on a fixed interval are actual solutions on that interval. -/
theorem isClosed_lipschitz_solutions [FiniteDimensional ℝ E] {F : E → Set E}
    (hF : UpperHemicontinuous F) (hconv : ∀ x, Convex ℝ (F x)) (hclosed : ∀ x, IsClosed (F x))
    {T : ℝ} (hT : 0 ≤ T) (L : ℝ≥0) :
    IsClosed {p : C(ℝ,E) | LipschitzOnWith L p (Icc 0 T) ∧
      ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (p t), HasDerivAt p v t} := by
  have eq : {p : C(ℝ,E) | LipschitzOnWith L p (Icc 0 T) ∧
      ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (p t), HasDerivAt p v t} =
      {p : C(ℝ,E) | LipschitzOnWith L p (Icc 0 T)} ∩ {p | SupportPath F T p} := by
    ext p
    constructor
    · rintro ⟨hlip, hincl⟩
      have hlip' : LipschitzOnWith L p (uIcc 0 T) := by simpa [uIcc_of_le hT] using hlip
      exact ⟨hlip, supportPath_of_inclusion hlip'.absolutelyContinuousOnInterval hincl⟩
    · rintro ⟨hlip, hsup⟩
      exact ⟨hlip, inclusion_of_lipschitz_supportPath hF hconv hclosed hlip hsup⟩
  rw [eq]
  exact ((isClosed_setOfPred_lipschitzOnWith L (Icc 0 T)).preimage
    (continuous_pi fun t => (continuous_eval_const t : Continuous (fun p : C(ℝ,E) => p t)))).inter
    (isClosed_supportPath hF T)

/-- Extend a nonnegative-time trajectory constantly to negative times. -/
def realPath (p : C(ℝ≥0,E)) : C(ℝ,E) := p.comp ⟨Real.toNNReal, Real.lipschitzWith_toNNReal.continuous⟩

omit [NormedSpace ℝ E] in
private theorem realPath_lipschitz {p : C(ℝ≥0,E)} {L : ℝ≥0} (h : LipschitzWith L p) :
    LipschitzWith L (realPath p) := by
  change LipschitzWith L (p ∘ Real.toNNReal)
  simpa only [mul_one] using h.comp Real.lipschitzWith_toNNReal

omit [NormedSpace ℝ E] in
/-- The compact-open topology on the positive-time path is compatible with
constant continuation to the negative real axis. -/
theorem continuous_realPath : Continuous (realPath (E := E)) :=
  ContinuousMap.continuous_precomp _

def testedPrefix (F : E → Set E) (n : ℕ) : Set C(ℝ≥0,E) :=
  {p | SupportPath F (n:ℝ) (realPath p)}

theorem isClosed_prefix {F : E → Set E} (hF : UpperHemicontinuous F) (n : ℕ) :
    IsClosed (testedPrefix F n) := (isClosed_supportPath hF _).preimage continuous_realPath

theorem supportPath_mono {F : E → Set E} {T S : ℝ} {p : C(ℝ,E)}
    (hp : SupportPath F T p) (h : S ≤ T) : SupportPath F S p :=
  fun l c a b ha hab hb => hp l c a b ha hab (hb.trans h)

theorem prefix_nested (F : E → Set E) (n : ℕ) : testedPrefix F (n+1) ⊆ testedPrefix F n :=
  fun _ hp => supportPath_mono hp (by exact_mod_cast Nat.le_succ n)

/-- A finite-horizon test depends only on the path up to the horizon. -/
theorem prefix_local (F : E → Set E) (n : ℕ) (p q : C(ℝ≥0,E))
    (eq : EqOn p q (Iic (n:ℝ≥0))) (hp : p ∈ testedPrefix F n) : q ∈ testedPrefix F n := by
  intro l c a b ha hab hb hq
  have h (t : ℝ) (ht : t ≤ n) : realPath p t = realPath q t := by
    apply eq
    exact (Real.toNNReal_le_iff_le_coe).mpr (by exact_mod_cast ht)
  rw [← h b hb, ← h a (hab.trans hb)]
  exact hp l c a b ha hab hb fun t ht => h t (ht.2.trans hb) ▸ hq ht

/-- A bound on all velocities along a support-tested path controls its
Lipschitz constant directly. The norming functional can be chosen separately
for each pair of times. -/
theorem lipschitz_of_support_bound {F : E → Set E} {T : ℝ} {p : C(ℝ,E)}
    (hp : SupportPath F T p) (L : ℝ≥0)
    (bound : ∀ t ∈ Icc 0 T, ∀ v ∈ F (p t), ‖v‖ ≤ L) :
    LipschitzOnWith (L+1) p (Icc 0 T) := by
  have inc (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ T) (hab : a ≤ b) :
      ‖p b-p a‖ ≤ ((L:ℝ)+1)*(b-a) := by
    obtain ⟨l, hl, normeq⟩ := exists_dual_vector'' ℝ (p b - p a)
    have hnorm : l (p b - p a) = ‖p b-p a‖ := by simpa using normeq
    rw [← hnorm]
    apply hp l _ a b ha hab hb
    intro t ht v hv
    have hvL := bound t ⟨ha.trans ht.1,ht.2.trans hb⟩ v hv
    have hval : l v ≤ ‖v‖ := (le_abs_self _).trans <| (l.le_opNorm _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) hl)
    change l v < (L:ℝ)+1
    linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rcases le_total a b with hab | hba
  · simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_one,
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub, norm_sub_rev (p a) (p b)] using inc a b ha.1 hb.2 hab
  · simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_add, NNReal.coe_one,
      abs_of_nonneg (sub_nonneg.mpr hba)] using inc b a hb.1 ha.2 hba

/-- For a field with compact velocity graph on compact sets, a support-tested
continuous path is automatically Lipschitz on the tested interval. -/
theorem supportPath_lipschitz {F : E → Set E}
    (compact : ∀ K : Set E, IsCompact K →
      IsCompact ({q : E × E | q.2 ∈ F q.1} ∩ Prod.fst ⁻¹' K))
    {T : ℝ} {p : C(ℝ,E)} (hp : SupportPath F T p) :
    ∃ L : ℝ≥0, LipschitzOnWith L p (Icc 0 T) := by
  have hK := compact (p '' Icc 0 T) (isCompact_Icc.image p.continuous)
  obtain ⟨R,hr⟩ := (Metric.isBounded_iff_subset_ball (0:E)).mp
    (hK.image continuous_snd).isBounded
  refine ⟨R.toNNReal+1, lipschitz_of_support_bound hp R.toNNReal ?_⟩
  intro t ht v hv
  have h := hr (show v ∈ Prod.snd '' ({q : E × E | q.2 ∈ F q.1} ∩ Prod.fst ⁻¹' (p '' Icc 0 T))
    from ⟨(p t, v), ⟨hv, t, ht, rfl⟩, rfl⟩)
  exact (show ‖v‖ < R by simpa [mem_ball] using h).le.trans (Real.le_coe_toNNReal _)

omit [NormedSpace ℝ E] in
/-- Pull an interval Lipschitz estimate on the real-time extension back to
the original nonnegative time domain without a change of constant. -/
theorem lipschitz_nonnegTime {p : C(ℝ≥0,E)} {T L : ℝ≥0}
    (h : LipschitzOnWith L (realPath p) (Icc 0 (T:ℝ))) :
    LipschitzOnWith L p (Iic T) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have h' := h.dist_le_mul (a:ℝ) ⟨a.2,ha⟩ (b:ℝ) ⟨b.2,hb⟩
  simpa only [realPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Real.toNNReal_coe, NNReal.dist_eq, Real.dist_eq] using h'

/-- For upper hemicontinuous closed convex compact-on-compact velocity
graphs, the closed increment tests imply an actual absolutely continuous
solution without any pre-assumed modulus of continuity. -/
theorem actual_of_supportPath [FiniteDimensional ℝ E] {F : E → Set E}
    (hF : UpperHemicontinuous F) (hconv : ∀ z, Convex ℝ (F z))
    (hclosed : ∀ z, IsClosed (F z))
    (compact : ∀ K : Set E, IsCompact K →
      IsCompact ({q : E × E | q.2 ∈ F q.1} ∩ Prod.fst ⁻¹' K))
    {p : C(ℝ,E)} {T : ℝ} (hT : 0 ≤ T) (hp : SupportPath F T p) :
    AbsolutelyContinuousOnInterval p 0 T ∧
    ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (p t), HasDerivAt p v t := by
  obtain ⟨L, hL⟩ := supportPath_lipschitz compact hp
  exact ⟨(show LipschitzOnWith L p (uIcc 0 T) by rwa [uIcc_of_le hT]).absolutelyContinuousOnInterval,
    inclusion_of_lipschitz_supportPath hF hconv hclosed hL hp⟩

/-- A locally uniform limit of approximate trajectories solves all support
tests when their anchor states approach the current states uniformly. No
continuity or measurability of the anchor maps is needed. -/
theorem supportPath_of_approximants {F : E → Set E} (hF : UpperHemicontinuous F)
    {p : C(ℝ≥0,E)} {u : ℕ → C(ℝ≥0,E)} (conv : Tendsto u atTop (𝓝 p))
    (anchor : ℕ → ℝ≥0 → E) (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (close : ∀ n t, dist (anchor n t) (u n t) ≤ err n) {L : ℝ≥0}
    (lip : ∀ n, LipschitzWith L (u n))
    (incl : ∀ n, ∀ᵐ t : ℝ, 0 < t → ∃ v ∈ F (anchor n t.toNNReal),
      HasDerivAt (realPath (u n)) v t) (T : ℝ) : SupportPath F T (realPath p) := by
  intro l c a b ha hab _ maps
  let K := Real.toNNReal '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image Real.lipschitzWith_toNNReal.continuous
  have hKU : p '' K ⊆ safeRegion F l c := by
    rintro _ ⟨_,⟨t,ht,rfl⟩,rfl⟩
    exact maps ht
  obtain ⟨δ, hδ, thick⟩ := (hK.image p.continuous).exists_thickening_subset_open
    (isOpen_safeRegion hF l c) hKU
  have unif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp conv) K hK
  have near : ∀ᶠ n in atTop, ∀ t ∈ K, anchor n t ∈ safeRegion F l c := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp unif (δ/2) (half_pos hδ),
      herr.eventually_lt_const (half_pos hδ)] with n hn he t ht
    apply thick
    refine Metric.mem_thickening_iff.mpr ⟨p t, ⟨t,ht,rfl⟩, (dist_triangle _ (u n t) _).trans_lt ?_⟩
    rw [dist_comm (u n t) (p t)]
    linarith [hn t ht, close n t]
  have limit_at (t : ℝ) : Tendsto (fun n => realPath (u n) t) atTop (𝓝 (realPath p t)) :=
    (continuous_eval_const t.toNNReal).continuousAt.tendsto.comp conv
  apply le_of_tendsto ((l.continuous.continuousAt.tendsto).comp ((limit_at b).sub (limit_at a)))
  filter_upwards [near] with n hn
  apply increment_le_of_velocity l hab (realPath_lipschitz (lip n)).lipschitzOnWith.absolutelyContinuousOnInterval
  filter_upwards [incl n, volume.ae_ne (0:ℝ)] with t ht hz ht'
  obtain ⟨v,hv,hd⟩ := ht (lt_of_le_of_ne (ha.trans ht'.1) hz.symm)
  exact ⟨v, hd, (show l v < c from hn t.toNNReal ⟨t,ht',rfl⟩ hv).le⟩

/-- Compactness produces a global Lipschitz differential-inclusion solution
from a sequence of uniformly Lipschitz Euler polygons with vanishing anchor
error and prescribed initial state. -/
theorem exists_solution_of_approximants [FiniteDimensional ℝ E] [ProperSpace E]
    {F : E → Set E} (hF : UpperHemicontinuous F) (hconv : ∀ z, Convex ℝ (F z))
    (hclosed : ∀ z, IsClosed (F z)) (x : E) {L : ℝ≥0} (u : ℕ → C(ℝ≥0,E))
    (initial : ∀ n, u n 0 = x) (lip : ∀ n, LipschitzWith L (u n))
    (anchor : ℕ → ℝ≥0 → E) (err : ℕ → ℝ) (herr : Tendsto err atTop (𝓝 0))
    (close : ∀ n t, dist (anchor n t) (u n t) ≤ err n)
    (incl : ∀ n, ∀ᵐ t : ℝ, 0 < t → ∃ v ∈ F (anchor n t.toNNReal),
      HasDerivAt (realPath (u n)) v t) :
    ∃ p : C(ℝ≥0,E), p 0 = x ∧ LipschitzWith L p ∧
      ∀ T : ℝ, ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (realPath p t),
        HasDerivAt (realPath p) v t := by
  let S : Set C(ℝ≥0,E) := {p | p 0 = x} ∩ {p | LipschitzWith L p}
  have hS : IsClosed S := (isClosed_eq (continuous_eval_const 0) continuous_const).inter
    ((isClosed_setOfPred_lipschitzWith L).preimage
      (continuous_pi fun t => (continuous_eval_const t : Continuous (fun p : C(ℝ≥0,E) => p t))))
  have cS := CirclePathSelection.isCompact_global_paths S hS x 0
    (fun p hp => by have hx : p 0 = x := hp.1; simp [hx])
    (fun _ => ⟨L, fun _ hp => hp.2.lipschitzOnWith⟩)
  obtain ⟨p,hp,idx,hidx,hlim⟩ := cS.tendsto_subseq (x := u) (fun n => ⟨initial n, lip n⟩)
  refine ⟨p,hp.1,hp.2, fun T => inclusion_of_lipschitz_supportPath hF hconv hclosed
    (realPath_lipschitz hp.2).lipschitzOnWith ?_⟩
  exact supportPath_of_approximants hF hlim (fun n => anchor (idx n)) (err ∘ idx)
    (herr.comp hidx.tendsto_atTop) (fun n => close (idx n)) (fun n => lip (idx n))
    (fun n => incl (idx n)) T

/-- Global existence for an autonomous, bounded, upper hemicontinuous
differential inclusion with nonempty closed convex values in finite dimension. -/
theorem exists_solution_bounded_field [FiniteDimensional ℝ E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] (F : E → Set E) (hF : UpperHemicontinuous F)
    (hne : ∀ z, (F z).Nonempty) (hconv : ∀ z, Convex ℝ (F z))
    (hclosed : ∀ z, IsClosed (F z)) (L : ℝ≥0) (bound : ∀ z, ∀ v ∈ F z, ‖v‖ ≤ L)
    (x : E) :
    ∃ p : C(ℝ≥0,E), p 0 = x ∧ LipschitzWith L p ∧
      ∀ T : ℝ, ∀ᵐ t : ℝ, t ∈ Icc 0 T → ∃ v ∈ F (realPath p t),
        HasDerivAt (realPath p) v t := by
  obtain ⟨p,q,hx,hl,hq,hd⟩ := CircleEulerPolygon.polygons F hne L bound x
  apply exists_solution_of_approximants hF hconv hclosed x p hx hl q
    (fun n => (L:ℝ)/(n+1)) _ hq hd
  simpa only [div_eq_mul_inv, mul_zero, one_mul] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (L:ℝ)

end CircleInclusionExistence
