module

public import CircleFlowMoments
public import CircleTangentDrift
public import CircleAngularGeometry
import all CircleFlowMoments
import all CircleTangentDrift
import all CircleFlowPath
import all CircleAngularGeometry
import all CircleEscape
import all CircleEscapeBridge
import Mathlib.Tactic

/-! Dynamics of the angular population mean along the actual circle flow.
The angular integral of the canonical gate defines a supporting functional
to the single-neuron mean ReLU. This gives a path chain rule even when the
entire hidden weight visits zero. -/
public section
noncomputable section
namespace CircleMeanDynamics
open CircleFlowPath CircleTangentDrift CircleEscapeBridge Real MeasureTheory Set Filter
open scoped Topology
variable {m N : ℕ}

private def feature (z : State m) (j : Fin m) (u : ℝ) := max (pre z j (phase u)) 0
private def gate (z : State m) (j : Fin m) (u : ℝ) := actualGate (pre z j (phase u))
private def meanFeature (z : State m) (j : Fin m) := ‖(initial z).w j‖ / π

private theorem meanFeature_eq (z : State m) (j : Fin m) :
    ∫ u, feature z j u ∂angularLaw = meanFeature z j := by
  let w := (initial z).w j
  let f := fun t => CircleEscape.feature w (CircleAngularGeometry.point t)
  have eq (u : ℝ) : feature z j u = f (2*π*u) := by
    simp [feature,f,w,CircleEscape.feature,CircleAngularGeometry.point,phase,pre,initial,Complex.inner,Complex.mul_re]
  simp_rw [eq]
  rw [angularLaw,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left f (by positivity : 2*π ≠ 0)]
  simp only [mul_zero,mul_one,smul_eq_mul]
  have hw : (∫ t in 0..2*π, f t) = ‖w‖*2 := by
    simp_rw [f,CircleAngularGeometry.feature_eq]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_sub_right]
    convert congrArg (fun b : ℝ => ‖w‖ * b) (CircleAngularGeometry.integral_half (0-w.arg)) using 2
    ring_nf
  rw [hw]
  change (2*π)⁻¹*(‖w‖*2) = ‖w‖/π
  ring

private theorem feature_integrable (z : State m) (j : Fin m) :
    Integrable (feature z j) angularLaw := by
  change IntegrableOn (feature z j) (Ioc 0 1) volume
  exact (show Continuous (feature z j) by unfold feature pre phase; fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem gate_integrable (z : State m) (j : Fin m) (first : Bool) :
    Integrable (fun u => gate z j u*(if first then (phase u).1 else (phase u).2)) angularLaw := by
  have hg : Measurable (gate z j) := CircleTangentDrift.gate_meas z j
  apply (integrable_const (1:ℝ)).mono'
  · cases first <;> simp only [Bool.false_eq_true,↓reduceIte,phase] <;> fun_prop
  filter_upwards with u
  have bound : |gate z j u| ≤ 1 := by unfold gate actualGate; split <;> norm_num
  rw [Real.norm_eq_abs,abs_mul]
  cases first <;> simp [phase] <;> apply (mul_le_of_le_one_left (abs_nonneg _) bound).trans
  · exact abs_sin_le_one _
  · exact abs_cos_le_one _

private def support (z : State m) (j : Fin m) (q : State m) : ℝ :=
  (∫ u, gate z j u*(phase u).1 ∂angularLaw) * q (j,1) +
  (∫ u, gate z j u*(phase u).2 ∂angularLaw) * q (j,2)

private theorem gated_integrable (z : State m) (j : Fin m) (q : State m) :
    Integrable (fun u => gate z j u*pre q j (phase u)) angularLaw := by
  have h₁ := (gate_integrable z j true).mul_const (q (j,1))
  have h₂ := (gate_integrable z j false).mul_const (q (j,2))
  simpa [pre,mul_add,mul_assoc,Pi.add_def] using h₁.add h₂

private theorem support_eq (z : State m) (j : Fin m) (q : State m) :
    (∫ u, gate z j u*pre q j (phase u) ∂angularLaw) = support z j q := by
  simp only [pre,mul_add,← mul_assoc]
  have h₁ : Integrable (fun u => gate z j u*(phase u).1*q (j,1)) angularLaw := (gate_integrable z j true).mul_const _
  have h₂ : Integrable (fun u => gate z j u*(phase u).2*q (j,2)) angularLaw := (gate_integrable z j false).mul_const _
  rw [integral_add h₁ h₂,
    integral_mul_const,integral_mul_const]
  rfl

private theorem support_le (z q : State m) (j : Fin m) : support z j q ≤ meanFeature q j := by
  rw [← support_eq,← meanFeature_eq]
  apply integral_mono (gated_integrable _ _ _) (feature_integrable _ _)
  intro u
  dsimp only [gate,actualGate,feature]
  split <;> simp

private theorem support_self (z : State m) (j : Fin m) : support z j z = meanFeature z j := by
  rw [← support_eq,← meanFeature_eq]
  apply integral_congr_ae (ae_of_all _ _)
  intro u
  exact gate_times_input (actualGate_admissible _)

private theorem feature_ac {z : ℝ → State m} {T : ℝ}
    (hz : ∀ p, AbsolutelyContinuousOnInterval (fun t => z t p) 0 T) (j : Fin m) :
    AbsolutelyContinuousOnInterval (fun t => meanFeature (z t) j) 0 T := by
  have h₁ := Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval (hz (j,1))
  have h₂ := Complex.ofRealLI.isometry.lipschitzWith.comp_absolutelyContinuousOnInterval (hz (j,2))
  have h := h₁.fun_add (h₂.const_smul Complex.I)
  have q (t : ℝ) : (initial (z t)).w j = (z t (j,1):ℂ)+Complex.I*(z t (j,2):ℂ) := by
    apply Complex.ext <;> simp [initial,Complex.mul_re,Complex.mul_im]
  simp_rw [meanFeature,q,div_eq_inv_mul]
  exact (lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval h).const_mul _

private theorem mean_as_sum (z : State m) : CircleFlowMoments.mean z =
    (1/√(m:ℝ)) * ∑ j, z (j,0)*meanFeature z j := by
  change (1/√(m:ℝ))/π*(∑ j, z (j,0)*‖(initial z).w j‖) =
    (1/√(m:ℝ))*(∑ j, z (j,0)*(‖(initial z).w j‖/π))
  simp_rw [← mul_div_assoc,← Finset.sum_div]
  ring

theorem mean_ac {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    AbsolutelyContinuousOnInterval (fun s => CircleFlowMoments.mean (z s)) 0 T := by
  have h := (CircleFlowPath.acsum Finset.univ _ (fun (j : Fin m) _ => (F.ac (j,0)).fun_mul (feature_ac F.ac j))).const_mul (1/√(m:ℝ))
  simp_rw [mean_as_sum]
  exact h

private theorem feature_deriv {z : ℝ → State m} {t : ℝ} {v : State m}
    (hv : ∀ p, HasDerivAt (fun s => z s p) (v p) t) (j : Fin m)
    (hd : DifferentiableAt ℝ (fun s => meanFeature (z s) j) t) :
    HasDerivAt (fun s => meanFeature (z s) j) (support (z t) j v) t := by
  have hs : HasDerivAt (fun s => support (z t) j (z s)) (support (z t) j v) t :=
    ((hv (j,1)).const_mul _).add ((hv (j,2)).const_mul _)
  have hm : IsLocalMin (fun s => meanFeature (z s) j - support (z t) j (z s)) t := by
    apply Eventually.of_forall
    intro s
    dsimp only
    rw [support_self,sub_self]
    exact sub_nonneg.mpr (support_le _ _ _)
  have d := hm.hasDerivAt_eq_zero (hd.hasDerivAt.sub hs)
  exact hd.hasDerivAt.congr_deriv (sub_eq_zero.mp d)


private def angleDerivative (z v : State m) (j : Fin m) (u : ℝ) :=
  v (j,0)*feature z j u + z (j,0)*(gate z j u*pre v j (phase u))

private theorem angleDerivative_int (z v : State m) (j : Fin m) :
    Integrable (angleDerivative z v j) angularLaw :=
  ((feature_integrable z j).const_mul _).add ((gated_integrable z j v).const_mul _)

private theorem integrated_row (z v : State m) :
    (∫ u, pair (row (1/sqrt m) z (phase u) (fun j => gate z j u)) v ∂angularLaw) =
    (1/sqrt m)*∑ j, (v (j,0)*meanFeature z j+z (j,0)*support z j v) := by
  have hr (u : ℝ) : pair (row (1/sqrt m) z (phase u) (fun j => gate z j u)) v =
      (1/sqrt m)*∑ j, angleDerivative z v j u := by
    simp [row_action,angleDerivative,feature,mul_assoc]
  simp_rw [hr]
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => angleDerivative_int z v j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (∫ u, v (j,0)*feature z j u+z (j,0)*(gate z j u*pre v j (phase u)) ∂angularLaw) = _
  rw [integral_add ((feature_integrable z j).const_mul _) ((gated_integrable z j v).const_mul _),
    integral_const_mul,integral_const_mul,meanFeature_eq,support_eq]

private theorem integrated_contraction (hm : 0 < m) (z : State m) (g : Fin N → Fin m → ℝ)
    (a : Fin N → ℝ) (τ : ℝ) :
    (∫ u, pair (row (1/sqrt m) z (phase u) (fun j => gate z j u))
      (velocity τ (fun i => row (1/sqrt m) z (circleInput N i) (g i)) a) ∂angularLaw)
       = -(rowOp (populationRow τ z g) (rmsCoordinates a)) := by
  simp only [velocity_contraction]
  rw [integral_div,integral_neg, rowOp_rms]
  have hi (i : Fin N) : Integrable (fun u => angleEntry τ z z (circleInput N i) (g i) u*a i) angularLaw :=
    (angleEntry_integrable hm _ _ _ _ _).mul_const _
  change -(∫ u, ∑ i, angleEntry τ z z (circleInput N i) (g i) u*a i ∂angularLaw)/N = _
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_const]
  rw [neg_div]
  rfl

/-- A common gate represents both the grid dynamics and the angular population
mean at almost every physical time. The population test gate is the canonical
positive gate and the grid gates remain jointly compatible with the velocity. -/
theorem ae_joint_ode {z : ℝ → State m} {τ T : ℝ} (hm : 0 < m)
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    let r := fun s => rmsCoordinates (residual (circleInput N) (circleLabel N) (1/sqrt m) (z s))
    ∀ᵐ t : ℝ, t ∈ uIcc 0 T → ∃ g : Fin N → Fin m → ℝ,
      gridGates (z t) g ∧ HasDerivAt r (-(gramOp (gridGram τ (z t) g) (r t))) t ∧
      HasDerivAt (fun s => CircleFlowMoments.mean (z s)) (-(rowOp (populationRow τ (z t) g) (r t))) t := by
  intro r
  have hreg : ∀ᵐ t, ∀ j, t ∈ uIcc 0 T → DifferentiableAt ℝ (fun s => meanFeature (z s) j) t :=
    ae_all_iff.mpr fun j => (feature_ac F.ac j).ae_differentiableAt
  have hd : ∀ᵐ t, ∀ p, t ∈ uIcc 0 T → DifferentiableAt ℝ (fun s => z s p) t :=
    ae_all_iff.mpr fun p => (F.ac p).ae_differentiableAt
  filter_upwards [ae_residual_eq F,hreg,hd] with t h hreg hd
  intro ht
  obtain ⟨g,hg,vel,dr⟩ := h ht
  refine ⟨g,hg,?_,?_⟩
  · have dg (i : Fin N) := dr i
    simp_rw [vel,velocity_contraction] at dg
    apply (CircleTangentDrift.rms_deriv dg).congr_deriv
    ext i
    change (-(∑ j, _ * _)/N)/sqrt N = -(gramOp _ (r t) i)
    rw [gramOp_apply]
    dsimp [r,rmsCoordinates,gridGram]
    simp only [← mul_div_assoc, ← Finset.sum_div]
    ring
  · have hp (p : Coord m) : HasDerivAt (fun s => z s p) (curveVelocity z t p) t := (hd p ht).hasDerivAt
    have dh := (HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
      (hp (j,0)).mul (feature_deriv hp j (hreg j ht)))).const_mul (1/√(m:ℝ))
    simp_rw [mean_as_sum]
    apply dh.congr_deriv
    rw [← integrated_contraction hm (z t) g _ τ, ← vel, integrated_row]

end CircleMeanDynamics
