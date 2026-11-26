module

public import CircleActualTracking
public import CircleSharpInitialization
public import CircleSharpEvent
import all CircleGaussianTracking
public import CircleSpectralPathLength
import all CircleSpectralPathLength
import all CircleActualTracking
import all CircleFlowTracking
import all CircleFlowPath
import all CircleTangentDrift
import Mathlib.Tactic

/-! Integrated perturbation estimates for the actual compared circle flows.
The deterministic reference evolves under the frozen population Gram. -/
public section
noncomputable section
namespace CircleSharpTracking
open CircleFlowPath CircleTangentDrift CircleActualTracking Real MeasureTheory Set Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {N m : ℕ}

/-- An integrated dissipativity inequality for a forced Hilbert-space path.
The endpoint and integrated response are controlled by the same input.
A crossing of the origin is allowed: the scalar norm has derivative zero
at almost every such point by the differentiable local-minimum rule. -/
theorem integrated_response (w : ℝ → V) (f : ℝ → ℝ) {k T : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval (fun t => ‖w t‖) 0 T)
    (int : IntervalIntegrable f volume 0 T)
    (h : ∀ᵐ s : ℝ, s ∈ Icc 0 T → 0 ≤ f s ∧ ∃ v, HasDerivAt w v s ∧
      inner ℝ (w s) v ≤ -k*‖w s‖^2+‖w s‖*f s) :
    ‖w T‖ + k*(∫ s in (0:ℝ)..T, ‖w s‖) ≤ ‖w 0‖+∫ s in (0:ℝ)..T, f s := by
  have ha : IntervalIntegrable (fun s => ‖w s‖) volume 0 T := ac.continuousOn.intervalIntegrable
  have hi := intervalIntegral.integral_mono_ae_restrict hT
    (ac.intervalIntegrable_deriv.add (ha.const_mul k)) int
    ((ae_restrict_iff' measurableSet_Icc).mpr (by
      filter_upwards [h,ac.ae_differentiableAt] with s hs hd hm
      obtain ⟨hf,v,dv,ener⟩ := hs hm
      have d := hd (by rwa [uIcc_of_le hT])
      change deriv (fun t => ‖w t‖) s+k*‖w s‖ ≤ f s
      by_cases hz : w s = 0
      · have hm' : IsLocalMin (fun t => ‖w t‖) s :=
          Eventually.of_forall (fun t => by simp [hz])
        rw [hm'.hasDerivAt_eq_zero d.hasDerivAt,hz,norm_zero,mul_zero,add_zero]
        exact hf
      · have den := norm_pos_iff.mpr hz
        have eq : 2*‖w s‖*deriv (fun t => ‖w t‖) s = 2*inner ℝ (w s) v := by
          have h₁ := (d.hasDerivAt.pow 2).deriv
          have h₂ := dv.norm_sq.deriv
          simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using h₁.symm.trans h₂
        apply le_of_mul_le_mul_left (a := ‖w s‖) _ den
        nlinarith))
  change (∫ s in (0:ℝ)..T, deriv (fun t => ‖w t‖) s+k*‖w s‖) ≤ _ at hi
  rw [intervalIntegral.integral_add ac.intervalIntegrable_deriv (ha.const_mul k),
    ac.integral_deriv_eq_sub,intervalIntegral.integral_const_mul] at hi
  linarith

/-- Joint endpoint and integrated L¹-in-time error against a frozen trajectory. -/
theorem frozen_error_balance (r f : ℝ → V) (A₀ : V →L[ℝ] V) {lam e T : ℝ}
    (hT : 0 ≤ T) (he : 0 ≤ e)
    (ac : AbsolutelyContinuousOnInterval (fun s => ‖r s-f s‖) 0 T)
    (ar : IntervalIntegrable (fun s => ‖r s‖) volume 0 T) (start : r 0 = f 0)
    (coerc : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A₀ v))
    (ode : ∀ᵐ s : ℝ, s ∈ Icc 0 T → ∃ A : V →L[ℝ] V,
      HasDerivAt r (-A (r s)) s ∧ HasDerivAt f (-A₀ (f s)) s ∧ ‖A₀-A‖ ≤ e) :
    ‖r T-f T‖+lam*(∫ s in (0:ℝ)..T, ‖r s-f s‖) ≤ e*(∫ s in (0:ℝ)..T, ‖r s‖) := by
  have h := integrated_response (fun s => r s-f s) (fun s => e*‖r s‖) (k := lam)
    hT ac (ar.const_mul e) (by
    filter_upwards [ode] with s hs hm
    obtain ⟨A,dr,df,clos⟩ := hs hm
    refine ⟨mul_nonneg he (norm_nonneg _),_,dr.sub df,?_⟩
    have decomp : -A (r s)- -A₀ (f s) = -(A₀ (r s-f s))+(A₀-A) (r s) := by simp; abel
    rw [decomp,inner_add_right,inner_neg_right]
    have op := ((A₀-A).le_opNorm (r s)).trans (mul_le_mul_of_nonneg_right clos (norm_nonneg _))
    have cs := (real_inner_le_norm (r s-f s) ((A₀-A) (r s))).trans
      (mul_le_mul_of_nonneg_left op (norm_nonneg _))
    linarith [coerc (r s-f s)])
  simp only [start,sub_self,norm_zero,zero_add,intervalIntegral.integral_const_mul] at h
  exact h

/-- A nonautonomous grid Gram perturbs the *integrated* population
semigroup response by at most e/λ times the true residual integral. -/
theorem duhamel_length (r f : ℝ → V) (A₀ : V →L[ℝ] V) {lam e T U : ℝ}
    (hT : 0 ≤ T) (hlam : 0 < lam) (he : 0 ≤ e) (small : 2*e ≤ lam)
    (ac : AbsolutelyContinuousOnInterval (fun s => ‖r s-f s‖) 0 T)
    (ar : IntervalIntegrable (fun s => ‖r s‖) volume 0 T)
    (af : IntervalIntegrable (fun s => ‖f s‖) volume 0 T)
    (start : r 0 = f 0) (semigroup : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ U)
    (coerc : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (A₀ v))
    (ode : ∀ᵐ s : ℝ, s ∈ Icc 0 T → ∃ A : V →L[ℝ] V,
      HasDerivAt r (-A (r s)) s ∧ HasDerivAt f (-A₀ (f s)) s ∧ ‖A₀-A‖ ≤ e) :
    (∫ s in (0:ℝ)..T, ‖r s‖) ≤ 2*U := by
  have h := frozen_error_balance r f A₀ hT he ac ar start coerc ode
  have tri := intervalIntegral.integral_mono_on hT ar
    (ac.continuousOn.intervalIntegrable.add af) (fun s _ => by
      change ‖r s‖ ≤ ‖r s-f s‖+‖f s‖
      simpa using norm_sub_le_norm_sub_add_norm_sub (r s) (f s) 0)
  rw [intervalIntegral.integral_add ac.continuousOn.intervalIntegrable af] at tri
  have non := intervalIntegral.integral_nonneg (μ := volume) hT (fun s _ => norm_nonneg (r s))
  apply le_of_mul_le_mul_left (a := lam) _ hlam
  nlinarith [mul_le_mul_of_nonneg_left tri hlam.le, mul_le_mul_of_nonneg_left semigroup hlam.le,
    mul_le_mul_of_nonneg_right small non, norm_nonneg (r T-f T)]


/-- A full RMS residual path is absolutely continuous as a finite sum
of the actual coordinate paths along isometric coordinate injections. -/
theorem actual_grid_ac {z : ℝ → State m} {τ T : ℝ}
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) :
    AbsolutelyContinuousOnInterval (fun s => gridR N (z s)) 0 T := by
  let r (s : ℝ) := residual (circleInput N) (circleLabel N) (1/sqrt m) (z s)
  let term (i : Fin N) (s : ℝ) : EuclideanSpace ℝ (Fin N) :=
    PiLp.single 2 i (r s i / sqrt N)
  have each (i : Fin N) : AbsolutelyContinuousOnInterval (term i) 0 T := by
    have iso : Isometry (fun a : ℝ => (PiLp.single 2 i a : EuclideanSpace ℝ (Fin N))) :=
      Isometry.of_dist_eq (fun _ _ => PiLp.dist_single_same _ _ _ _ _)
    have a := ((residual_ac F i).const_mul (sqrt (N:ℝ))⁻¹)
    simpa only [term,r,div_eq_inv_mul,Function.comp_def] using iso.lipschitzWith.comp_absolutelyContinuousOnInterval a
  have sum (S : Finset (Fin N)) : AbsolutelyContinuousOnInterval (fun s => ∑ i ∈ S, term i s) 0 T := by
    induction S using Finset.induction_on with
    | empty => simpa using (show ContDiff ℝ 1 (fun _ : ℝ => (0:EuclideanSpace ℝ (Fin N))) by
        fun_prop).contDiffOn.absolutelyContinuousOnInterval (a := 0) (b := T)
    | insert i S hi ih => simpa [Finset.sum_insert hi] using (each i).fun_add ih
  apply (sum Finset.univ).congr
  intro s _
  ext i
  simp [term, gridR, rmsCoordinates, r]

private theorem frozen_ac {f : ℝ → V} (A : V →L[ℝ] V) (df : ∀ s, HasDerivAt f (-A (f s)) s)
    (T : ℝ) : AbsolutelyContinuousOnInterval f 0 T := by
  have d : Differentiable ℝ f := fun s => (df s).differentiableAt
  have ce : Continuous (deriv f) := by
    simp_rw [funext (fun s => (df s).deriv)]
    exact (A.continuous.comp d.continuous).neg
  exact (contDiff_one_iff_deriv.mpr ⟨d,ce⟩).contDiffOn.absolutelyContinuousOnInterval

/-- A deterministic initial CLM error is retained as `B`: an entrywise
bound is used only on the movement after initialization. This avoids a
logarithmic maximum in the fourth moment of the initial error. -/
theorem moving_operators {τ ρ B : ℝ} {z₀ z : State m} {g : Fin N → Fin m → ℝ}
    (K : Matrix (Fin N) (Fin N) ℝ) (kQ : Fin N → ℝ) (hn : 0 < N) (hm : 0 < m)
    (hτ : |τ| ≤ 2) (hρ : 0 ≤ ρ) (small : ρ ≤ 1) (tube : Tube ρ z₀ z)
    (ad : gridGates z g) (energy : meanEnergy z₀ ≤ 4)
    (marg : ∀ i : Fin N, marginMass z₀ ρ (circleInput N i) ≤ 32*ρ)
    (amarg : angularMargin z₀ ρ ≤ 32*ρ)
    (initA : ‖gramOp (gridGram τ z₀ (startGates z₀))-gramOp K‖ ≤ B)
    (initQ : ‖rowOp (populationRow τ z₀ (startGates z₀))-rowOp kQ‖ ≤ B) :
    ‖gramOp (gridGram τ z g)-gramOp K‖ ≤ B+234*ρ ∧
    ‖rowOp (populationRow τ z g)-rowOp kQ‖ ≤ B+234*ρ := by
  have good : GoodInit τ ρ (29*ρ) (gridGram τ z₀ (startGates z₀))
      (populationRow τ z₀ (startGates z₀) : Fin N → ℝ) z₀ := by
    refine ⟨energy,fun i => (marg i).trans_eq (by ring),amarg.trans_eq (by ring),?_,?_⟩ <;>
      intros <;> simp <;> linarith
  obtain ⟨a,q⟩ := good.track_ops hn hm hτ hρ small (by positivity) tube ad
  constructor
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add a initA).trans_eq (by ring))
  · exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add q initQ).trans_eq (by ring))

/-- A confined physical prefix pays only the integrated frozen-semigroup
response. The same bound applies to every measurable solution choice. -/
theorem sharp_prefix {τ T lam e U ρ : ℝ} {z : ℝ → State m} (K : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (f : ℝ → EuclideanSpace ℝ (Fin N))
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) (hT : 0 ≤ T)
    (hlam : 0 < lam) (he : 0 ≤ e) (small : 2*e ≤ lam)
    (start : gridR N (z 0) = f 0) (df : ∀ s, HasDerivAt f (-K (f s)) s)
    (Ubound : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ U)
    (gap : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (K v))
    (near : ∀ s ∈ Icc 0 T, Tube ρ (z 0) (z s) →
      ∀ g, gridGates (z s) g → ‖K-gramOp (gridGram τ (z s) g)‖ ≤ e)
    {t : ℝ} (ht : t ∈ Icc 0 T) (pref : ∀ s ∈ Ico 0 t, Tube ρ (z 0) (z s)) :
    (∫ s in (0:ℝ)..t, ‖gridR N (z s)‖) ≤ 2*U := by
  have inc : uIcc 0 t ⊆ uIcc 0 T := by rw [uIcc_of_le ht.1,uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2
  have ar := (actual_grid_ac F).mono inc
  have af := (frozen_ac K df T).mono inc
  have afT := (frozen_ac K df T).continuousOn.norm
  have ac := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (ar.fun_sub af)
  refine duhamel_length _ f K ht.1 hlam he small ac ar.continuousOn.norm.intervalIntegrable
    af.continuousOn.norm.intervalIntegrable start ?_ gap ?_
  · exact (intervalIntegral.integral_mono_interval (le_refl 0) ht.1 ht.2
      (ae_of_all _ (fun s => norm_nonneg (f s))) afT.intervalIntegrable).trans Ubound
  · filter_upwards [ae_grid_hilbert_ode F,volume.ae_ne t] with s hs ne hm
    have hmem : s ∈ Icc 0 T := ⟨hm.1,hm.2.trans ht.2⟩
    obtain ⟨g,ad,dr⟩ := hs (by simpa [uIcc_of_le hT] using hmem)
    exact ⟨_,dr,df s,near s hmem (pref s ⟨hm.1,lt_of_le_of_ne hm.2 ne⟩) g ad⟩


/-- Pair a scalar AC observable with a time-integrable speed majorant. -/
theorem endpoint_variation {y q : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (ac : AbsolutelyContinuousOnInterval y 0 T) (int : IntervalIntegrable q volume 0 T)
    (v : ∀ᵐ s : ℝ, s ∈ Ioc 0 T → |deriv y s| ≤ C*q s) :
    |y T-y 0| ≤ C*∫ s in (0:ℝ)..T, q s := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le (f := deriv y) hT
    (by simpa only [Real.norm_eq_abs] using v) (int.const_mul C)
  simpa only [Real.norm_eq_abs,ac.integral_deriv_eq_sub,intervalIntegral.integral_const_mul] using hh

/-- Close the actual finite-neuron tube using the integrated semigroup budget
`U`. A strict coordinate prefix gives a non-strict Euclidean tube, which is
exactly the hypothesis needed by the moving-kernel estimate. -/
theorem spectral_tube {z : ℝ → State m} {τ T lam e U ρ : ℝ}
    (K : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
    (f : ℝ → EuclideanSpace ℝ (Fin N))
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z)
    (hn : 0 < N) (hτ : |τ| ≤ 2) (hT : 0 ≤ T) (hlam : 0 < lam) (he : 0 ≤ e) (small : 2*e ≤ lam)
    (hρ : 0 ≤ ρ) (cap : ρ ≤ 1) (budget : 8*U/sqrt m < ρ/2) (nz : ∀ i, 0 < length (z 0) i)
    (start : gridR N (z 0) = f 0) (df : ∀ s, HasDerivAt f (-K (f s)) s)
    (Ubound : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ U)
    (gap : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (K v))
    (near : ∀ s ∈ Icc 0 T, Tube ρ (z 0) (z s) →
      ∀ g, gridGates (z s) g → ‖K-gramOp (gridGram τ (z s) g)‖ ≤ e) :
    (∀ s ∈ Icc 0 T, Tube ρ (z 0) (z s)) ∧ (∫ s in (0:ℝ)..T, ‖gridR N (z s)‖) ≤ 2*U := by
  let S (p : Coord m) := Icc 0 T ∩
    {s : ℝ | (ρ/2)*length (z 0) p.1 ≤ |z s p-z 0 p|}
  have compact (p : Coord m) : IsCompact (S p) := by
    have cont : ContinuousOn (fun s => |z s p-z 0 p|) (Icc 0 T) := by
      simpa [uIcc_of_le hT] using ((F.ac p).continuousOn.sub continuousOn_const).abs
    exact isCompact_Icc.of_isClosed_subset
      (cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici) inter_subset_left
  have noexit : ¬ (⋃ p, S p).Nonempty := by
    intro bad
    obtain ⟨t, ht, first⟩ := (isCompact_iUnion compact).exists_isMinOn bad continuous_id.continuousOn
    obtain ⟨p,hp⟩ := mem_iUnion.mp ht
    have htime : t ∈ Icc 0 T := hp.1
    have pre (s : ℝ) (hs : s ∈ Ico 0 t) : Tube ρ (z 0) (z s) := by
      apply CircleActualTracking.tube_of_coords hρ
      intro j l
      by_contra! nd
      exact hs.2.not_ge (isMinOn_iff.mp first s (mem_iUnion.mpr
        ⟨(j,l), ⟨hs.1,hs.2.le.trans htime.2⟩,nd.le⟩))
    have integ := sharp_prefix K f F hT hlam he small start df Ubound gap near htime pre
    have subset : uIcc 0 t ⊆ uIcc 0 T := by rw [uIcc_of_le hT,uIcc_of_le htime.1]; exact Icc_subset_Icc_right htime.2
    have acl := (F.ac p).mono subset
    have ar := ((actual_grid_ac F).mono subset).continuousOn.norm.intervalIntegrable (μ := volume)
    let C := (4/sqrt m)*length (z 0) p.1
    have Cpos : 0 ≤ C := mul_nonneg (by positivity) (nz _).le
    have endpoint := endpoint_variation (C := C) htime.1 acl ar (by
      filter_upwards [F.compatible,volume.ae_ne t] with s hs neq hm
      have hst : s ∈ Ico 0 t := ⟨hm.1.le,lt_of_le_of_ne hm.2 neq⟩
      obtain ⟨g,ad,dz⟩ := hs (by rw [uIcc_of_le hT]; exact ⟨hm.1.le,hm.2.trans htime.2⟩)
      rw [(dz p).deriv]
      apply (coordinate_speed (z s) g _ hn hτ ad p.1 p.2).trans
      have cur := (CircleActualTracking.current_length (pre s hst) p.1).trans
        (mul_le_mul_of_nonneg_right (by linarith : 1+ρ ≤ 2) (nz _).le)
      change 2/sqrt m * ‖gridR N (z s)‖ * length (z s) p.1 ≤ C*‖gridR N (z s)‖
      exact (mul_le_mul_of_nonneg_left cur (by positivity : 0 ≤ 2/sqrt m * ‖gridR N (z s)‖)).trans_eq (by dsimp [C]; ring))
    have paid := endpoint.trans (mul_le_mul_of_nonneg_left integ Cpos)
    have size : C*(2*U) < ρ/2*length (z 0) p.1 := by
      convert mul_lt_mul_of_pos_right budget (nz p.1) using 1
      dsimp [C]
      ring
    exact (paid.trans_lt size).not_ge hp.2
  have all (s : ℝ) (hs : s ∈ Icc 0 T) : Tube ρ (z 0) (z s) := by
    apply CircleActualTracking.tube_of_coords hρ
    intro j l
    by_contra! bad
    exact noexit ⟨s,mem_iUnion.mpr ⟨(j,l),hs,bad.le⟩⟩
  exact ⟨all,sharp_prefix K f F hT hlam he small start df Ubound gap near ⟨hT,le_rfl⟩
    (fun s hs => all s ⟨hs.1,hs.2.le⟩)⟩



/-- If the normalized frozen row factors through its grid Gram, actual output
tracking against the *same-time* frozen prediction costs at most 6eU. The
grid residual endpoint also approximates the frozen residual by 2eU. -/
theorem sharp_observable {z : ℝ → State m} {τ T lam e U ρ b : ℝ}
    (K : Matrix (Fin N) (Fin N) ℝ) (kQ : Fin N → ℝ) (f : ℝ → EuclideanSpace ℝ (Fin N))
    (F : IsFlow (circleInput N) (circleLabel N) (1/sqrt m) τ T z) (hn : 0 < N) (hm : 0 < m)
    (hτ : |τ| ≤ 2) (hT : 0 ≤ T) (hlam : 0 < lam) (he : 0 ≤ e) (small : 2*e ≤ lam)
    (hρ : 0 ≤ ρ) (cap : ρ ≤ 1) (budget : 8*U/sqrt m < ρ/2) (nz : ∀ i, 0 < length (z 0) i)
    (start : gridR N (z 0) = f 0) (df : ∀ s, HasDerivAt f (-(gramOp K (f s))) s)
    (Ubound : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ U)
    (gap : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (gramOp K v))
    (near : ∀ s ∈ Icc 0 T, Tube ρ (z 0) (z s) → ∀ g, gridGates (z s) g →
      ‖gramOp K-gramOp (gridGram τ (z s) g)‖ ≤ e ∧ ‖rowOp (populationRow τ (z s) g)-rowOp kQ‖ ≤ e)
    (hb : |b| ≤ 1) (eig : rowOp kQ = (rowOp (fun _ : Fin N => b)).comp (gramOp K)) :
    let p := rowOp (fun _ : Fin N => b)
    ‖gridR N (z T)-f T‖ ≤ 2*e*U ∧
    |CircleFlowMoments.mean (z T) -
      (CircleFlowMoments.mean (z 0)-p (gridR N (z 0))+p (f T))| ≤ 6*e*U := by
  intro p
  let r (s : ℝ) := gridR N (z s)
  let Y (s : ℝ) := CircleFlowMoments.mean (z s)
  have pcap : ‖p‖ ≤ 1 := rowOp_norm hn zero_le_one (fun _ => hb)
  obtain ⟨tube,length⟩ := spectral_tube (gramOp K) f F hn hτ hT hlam he small hρ cap budget nz
    start df Ubound gap (fun s hs t g ad => (near s hs t g ad).1)
  have ar := actual_grid_ac F
  have ir : IntervalIntegrable (fun s => ‖r s‖) volume 0 T := ar.continuousOn.norm.intervalIntegrable
  have ac := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (ar.fun_sub (frozen_ac _ df T))
  have bal := frozen_error_balance r f (gramOp K) hT he ac ir start gap (by
    filter_upwards [ae_grid_hilbert_ode F] with s hs hm
    obtain ⟨g,ad,dr⟩ := hs (by simpa [uIcc_of_le hT] using hm)
    exact ⟨_,dr,df s,(near s hm (tube s hm) g ad).1⟩)
  have non : 0 ≤ ∫ s in (0:ℝ)..T, ‖r s-f s‖ := intervalIntegral.integral_nonneg hT (fun s _ => norm_nonneg _)
  have endpoint : ‖r T-f T‖ ≤ 2*e*U := by
    have paid := mul_le_mul_of_nonneg_left length he
    change e*(∫ s in (0:ℝ)..T, ‖r s‖) ≤ _ at paid
    nlinarith [mul_nonneg hlam.le non]
  refine ⟨endpoint,?_⟩
  have acy := (CircleMeanDynamics.mean_ac F).fun_sub (CircleActualTracking.row_ac F (fun _ => b))
  have tel := endpoint_variation (C := 2*e) hT acy ir (by
    filter_upwards [CircleMeanDynamics.ae_joint_ode hm F] with s hs ht
    have hmem : s ∈ Icc 0 T := ⟨ht.1.le,ht.2⟩
    obtain ⟨g,ad,dr,dy⟩ := hs (by simpa [uIcc_of_le hT] using hmem)
    obtain ⟨ga,ro⟩ := near s hmem (tube s hmem) g ad
    let A := gramOp (gridGram τ (z s) g)
    let q := rowOp (populationRow τ (z s) g)
    have proj := (p.opNorm_comp_le (gramOp K-A)).trans
      (mul_le_mul pcap ga (norm_nonneg _) zero_le_one)
    rw [ContinuousLinearMap.comp_sub,one_mul] at proj
    rw [eig] at ro
    have rowerr : ‖q-p.comp A‖ ≤ 2*e := (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add ro proj).trans_eq (by ring))
    have d := dy.sub (p.hasFDerivAt.comp_hasDerivAt s dr)
    rw [show deriv (fun t => Y t-p (r t)) s = _ from d.deriv]
    change |-(q (r s))-p (-(A (r s)))| ≤ _
    rw [map_neg,sub_neg_eq_add,show -(q (r s))+p (A (r s)) = -((q-p.comp A) (r s)) by simp; ring,abs_neg]
    exact ((q-p.comp A).le_opNorm _).trans (mul_le_mul_of_nonneg_right rowerr (norm_nonneg _)))
  have hp := (p.le_opNorm (r T-f T)).trans (mul_le_mul pcap endpoint (norm_nonneg _) zero_le_one)
  rw [Real.norm_eq_abs,one_mul] at hp
  change |Y T-(Y 0-p (r 0)+p (f T))| ≤ _
  rw [show Y T-(Y 0-p (r 0)+p (f T)) =
    ((Y T-p (r T))-(Y 0-p (r 0)))+p (r T-f T) by rw [map_sub]; ring]
  have paid := tel.trans (mul_le_mul_of_nonneg_left length (by positivity))
  exact (abs_add_le _ _).trans ((add_le_add paid hp).trans_eq (by ring))


/-- The frozen path area is at most initial RMS divided by the gap. This
allows taking the minimum with the sharper random Fourier bound. -/
theorem frozen_area_cap (f : ℝ → V) (K : V →L[ℝ] V) {T lam : ℝ} (ht : 0 ≤ T)
    (hlam : 0 < lam) (df : ∀ s, HasDerivAt f (-(K (f s))) s)
    (gap : ∀ v, lam*‖v‖^2 ≤ inner ℝ v (K v)) :
    (∫ s in (0:ℝ)..T, ‖f s‖) ≤ ‖f 0‖/lam := by
  have ac := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (frozen_ac K df T)
  have est := integrated_response f (fun _ => 0) (k := lam) ht ac (intervalIntegrable_const) (by
    filter_upwards with s _
    refine ⟨le_rfl,_,df s,?_⟩
    rw [inner_neg_right,mul_zero,add_zero]
    linarith [gap (f s)])
  simp only [intervalIntegral.integral_zero,add_zero] at est
  apply (le_div_iff₀ hlam).mpr
  linarith [norm_nonneg (f T)]

/-- A frozen eigenrow retains its exact transient. -/
theorem frozen_mode (f : ℝ → V) (K : V →L[ℝ] V) (p : V →L[ℝ] ℝ) {T γ : ℝ} (hT : 0 ≤ T)
    (hγ : 0 < γ) (df : ∀ s, HasDerivAt f (-(K (f s))) s) (eig : ∀ v, p (K v) = γ*p v) :
    p (f T) = exp (-(γ*T))*p (f 0) := by
  have ac := p.lipschitzWith.comp_absolutelyContinuousOnInterval (frozen_ac K df T)
  have est := CircleFlowTracking.projected_mode_tracking (C := 0) hT hγ le_rfl ac (by
    filter_upwards with s _
    rw [(p.hasFDerivAt.comp_hasDerivAt s (df s)).deriv,map_neg,eig]
    simp)
  simp only [zero_div,abs_nonpos_iff,sub_eq_zero] at est
  exact est

def randomRadius (N U : ℝ) := 32*(1+U)/N^16

/-- Explicit radius budget on the sharp event. -/
theorem radius_budget {D U B : ℝ} (hd : 32 ≤ D) (hU : 0 ≤ U) (capU : U ≤ (π*D)^2*D^2)
    (Bsmall : B ≤ 1/(4*(π*D)^2)) :
    1/D^16 ≤ randomRadius D U ∧ randomRadius D U ≤ 1 ∧
    8*U/D^16 < randomRadius D U/2 ∧ 2*(B+234*randomRadius D U) ≤ 1/(π*D)^2 := by
  have dp : 0 < D := by linarith
  have pp : π^2 ≤ 16 := by
    exact (pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2).trans_eq (by norm_num)
  have big := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hd 10
  have big4 : (1:ℝ) ≤ D^4 := one_le_pow₀ (by linarith : 1 ≤ D)
  have lim : 32*(1+U) ≤ 544*D^4 := by
    nlinarith [mul_le_mul_of_nonneg_right pp (show 0 ≤ D^4 by positivity)]
  have rad : randomRadius D U ≤ 544/D^12 := by
    unfold randomRadius
    rw [show D^16=D^4*D^12 by ring]
    field_simp
    linarith
  have small : 234*randomRadius D U ≤ 1/(4*(π*D)^2) := by
    apply (mul_le_mul_of_nonneg_left rad (by norm_num : (0:ℝ) ≤ 234)).trans
    rw [show D^12=D^2*D^10 by ring]
    field_simp
    nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold randomRadius
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · apply rad.trans
    rw [div_le_one (by positivity)]
    have pow12 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hd 12
    norm_num at pow12
    linarith
  · unfold randomRadius
    field_simp
    linarith
  · have hh := add_le_add Bsmall small
    calc
      _ ≤ 2*(1/(4*(π*D)^2)+1/(4*(π*D)^2)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring

/-- The constant Fourier component at the original horizon costs at most
N⁻¹⁶ even with an initial RMS as large as N². -/
theorem fast_transient {D γ : ℝ} (hd : 32 ≤ D) (hg : 1/π^2 ≤ γ) :
    exp (-(γ*(CircleFlowTracking.horizon D)))*D^2 ≤ 1/D^16 := by
  have hd1 : 1 ≤ D := by linarith
  have dp : 0 < D := by linarith
  have ceiling := Nat.le_ceil (2*π^2*D^2*log (2*sqrt (12*D)*D^3))
  change _ ≤ (CircleFlowTracking.horizon D : ℝ) at ceiling
  have logs : 3*log D ≤ log (2*sqrt (12*D)*D^3) := by
    rw [log_mul (by positivity) (by positivity),log_pow]
    have hs : (1:ℝ) ≤ sqrt (12*D) := le_sqrt_of_sq_le (by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith [log_nonneg (show 1 ≤ 2*sqrt (12*D) by linarith)]
  have rate : 18*log D ≤ γ*(CircleFlowTracking.horizon D) := by
    have hl := mul_le_mul_of_nonneg_left logs (by positivity : 0 ≤ 2*D^2)
    have lg := mul_le_mul_of_nonneg_left ceiling (by positivity : 0 ≤ 1/π^2)
    have cap := mul_le_mul_of_nonneg_right hg (show 0 ≤ (CircleFlowTracking.horizon D:ℝ) by positivity)
    have id : 1/π^2*(2*π^2*D^2*log (2*sqrt (12*D)*D^3)) =
        2*D^2*log (2*sqrt (12*D)*D^3) := by field_simp
    rw [id] at lg
    have hp : 3 ≤ D^2 := by nlinarith [sq_nonneg (D-32)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (log_nonneg hd1)]
  have e := exp_le_exp.mpr (neg_le_neg rate)
  rw [show exp (-(18*log D)) = (D^18)⁻¹ by
    rw [show 18*log D=log (D^18) by rw [log_pow]; norm_num,exp_neg,exp_log (by positivity)]] at e
  exact (mul_le_mul_of_nonneg_right e (sq_nonneg _)).trans_eq (by field_simp)


/-- Integral of the true frozen circle-network residual over the original
horizon. Any dominating random variable may be used in the pointwise result. -/
def frozenArea (N m : ℕ) [NeZero N] (τ : ℝ) (ω : State m) :=
  let a := CircleFlowPath.residual (circleInput N) (circleLabel N) (1/sqrt m) ω
  ∫ s in (0:ℝ)..(CircleFlowTracking.horizon N : ℝ), ‖CircleSpectralPathLength.referencePath τ a s‖

/-- Same-time population response on every nonnegative time interval. -/
theorem sharp_stopped_design (n : ℕ) (T : ℝ) (ht : 0≤T) (hN : 32 ≤ n+1) (ho : Odd (n+1))
    (τ : ℝ) (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2) (V₀ : ℝ) (z : ℝ → State ((n+1)^32))
    (F : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
      T z)
    (energy : meanEnergy (z 0) ≤ 4)
    (margins : ∀ ρ : ℝ, 1/((n:ℝ)+1)^16 ≤ ρ → ρ ≤ 1 →
      (∀ i : Fin (n+1), marginMass (z 0) ρ (circleInput (n+1) i) ≤ 32*ρ) ∧
        angularMargin (z 0) ρ ≤ 32*ρ)
    (nz : ∀ j, 0 < length (z 0) j)
    (init : ‖gridR (n+1) (z 0)‖ ≤ ((n:ℝ)+1)^2)
    (small : CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ (z 0) ≤ 1/(4*(π*((n:ℝ)+1))^2))
    (Vbound : (∫ s in (0:ℝ)..T, ‖CircleSpectralPathLength.referencePath τ
      (CircleSpectralPathLength.rawResidual (n+1) ((n+1)^32) (z 0)) s‖) ≤ V₀) :
    |CircleFlowMoments.mean (z T) -
      (CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) (z 0) +
        rowOp (fun _ : Fin (n+1) => CircleSpectrum.weight τ n)
          (CircleSpectralPathLength.referencePath τ (CircleSpectralPathLength.rawResidual (n+1) ((n+1)^32) (z 0)) T))| ≤
      6*CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ (z 0)*V₀ +
        44928*(1+V₀)*V₀/((n:ℝ)+1)^16 := by
  let D := (n:ℝ)+1
  let K := CircleGridSpectrum.sampledMatrix (N := n+1) τ
  let kQ := fun _ : Fin (n+1) => CircleSpectrum.k0 τ
  let a := CircleFlowPath.residual (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32:ℕ):ℝ)) (z 0)
  let f := CircleSpectralPathLength.referencePath τ a
  let lam := 1/(π*D)^2
  let B := CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ (z 0)
  have h3 : 3 ≤ n+1 := by omega
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast hN
  have dp : 0 < D := by linarith
  have h0 : 0 ≤ τ := by linarith
  have ht' : |τ| ≤ 2 := by rwa [abs_of_nonneg h0]
  have castN : ((n+1 : ℕ):ℝ) = D := by simp [D]
  have width : sqrt (((n+1)^32:ℕ):ℝ) = D^16 := by
    push_cast
    rw [show ((n:ℝ)+1)^32 = (((n:ℝ)+1)^16)^2 by ring,sqrt_sq (by positivity)]
  have start : gridR (n+1) (z 0) = f 0 := (CircleSpectralPathLength.referencePath_zero τ a).symm
  have df (s : ℝ) : HasDerivAt f (-(gramOp K (f s))) s :=
    CircleSpectralPathLength.referencePath_deriv τ h0 hτ' a s
  have gap (v : EuclideanSpace ℝ (Fin (n+1))) : lam*‖v‖^2 ≤ inner ℝ v (gramOp K v) := by
    simpa only [K,lam,castN] using CircleGridSpectrum.gramOp_gap h3 ho τ hτ hτ' v
  have lp : 0 < lam := by dsimp [lam]; positivity
  have areaNN : 0 ≤ ∫ s in (0:ℝ)..T, ‖f s‖ := intervalIntegral.integral_nonneg ht (fun _ _ => norm_nonneg _)
  change (∫ s in (0:ℝ)..T, ‖f s‖) ≤ V₀ at Vbound
  have arcap := frozen_area_cap f _ ht lp df gap
  rw [← start] at arcap
  have arcap' := arcap.trans (div_le_div_of_nonneg_right init lp.le)
  have upper : D^2/lam=(π*D)^2*D^2 := by dsimp [lam]; field_simp
  let U := min V₀ ((π*D)^2*D^2)
  have area : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ U := le_min Vbound (arcap'.trans_eq upper)
  have up := areaNN.trans area
  let ρ := randomRadius D U
  obtain ⟨ρlo,ρhi,budget,ctrl⟩ := radius_budget d up (min_le_right _ _) small
  obtain ⟨gm,am⟩ := margins ρ ρlo ρhi
  have rhoNN : 0 ≤ ρ := (by positivity : 0 ≤ 1/D^16).trans ρlo
  have bop := CircleSharpInitialization.initial_operators_le (N := n+1) τ (z 0)
  have gr : ‖gramOp (gridGram τ (z 0) (startGates (z 0)))-gramOp K‖ ≤ B :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans bop
  have qr : ‖rowOp (populationRow τ (z 0) (startGates (z 0)))-rowOp kQ‖ ≤ B :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans bop
  have Bnn := (norm_nonneg _).trans gr
  let e := B+234*ρ
  have enn : 0 ≤ e := by dsimp [e]; positivity
  have bcap := weight_abs_le_one n τ h0
  have eps := sharp_observable K kQ f F (Nat.succ_pos _) (pow_pos (Nat.succ_pos _) _) ht' ht lp enn
    ctrl rhoNN ρhi (by rwa [width]) nz start df area gap (fun s _ tube g ad => by
      obtain ⟨a,q⟩ := moving_operators K kQ (Nat.succ_pos _) (pow_pos (Nat.succ_pos _) _)
        ht' rhoNN ρhi tube ad energy gm am gr qr
      exact ⟨by rwa [norm_sub_rev],q⟩) bcap (CircleGridSpectrum.population_row_factorization n h3 ho τ hτ hτ')
  let p := rowOp (fun _ : Fin (n+1) => CircleSpectrum.weight τ n)
  let Z := CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) (z 0)
  have same : |CircleFlowMoments.mean (z T)-(Z+p (f T))| ≤ 6*e*U := by
    dsimp only [Z,p]
    rw [← actual_reference h3]
    exact eps.2
  have price : 6*e*U ≤ 6*B*V₀ + 44928*(1+V₀)*V₀/D^16 := by
    have UU : U ≤ V₀ := min_le_left _ _
    have u2 := mul_le_mul (add_le_add_right UU 1) UU up (by linarith : 0 ≤ 1+V₀)
    have b := mul_le_mul_of_nonneg_left UU (by positivity : 0 ≤ 6*B)
    calc
      _ = 6*B*U+44928*(1+U)*U/D^16 := by dsimp [e,ρ,randomRadius]; ring
      _ ≤ _ := add_le_add b (by
        rw [mul_assoc (44928:ℝ),mul_assoc (44928:ℝ)]
        gcongr)
  exact same.trans price

/-- Sharp good-seed statement for the actual network. `V₀` need only bound
the frozen path integral: clipping at its crude dissipative bound makes the
random tube radius admissible without any pointwise assumption on `V₀`.
The only smallness required of the initial tangent error is a quarter gap. -/
theorem sharp_design_endpoint (n : ℕ) (hN : 32 ≤ n+1) (ho : Odd (n+1))
    (τ : ℝ) (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2) (V₀ : ℝ) (z : ℝ → State ((n+1)^32))
    (F : IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
      (CircleFlowTracking.horizon (n+1)) z)
    (energy : meanEnergy (z 0) ≤ 4)
    (margins : ∀ ρ : ℝ, 1/((n:ℝ)+1)^16 ≤ ρ → ρ ≤ 1 →
      (∀ i : Fin (n+1), marginMass (z 0) ρ (circleInput (n+1) i) ≤ 32*ρ) ∧
        angularMargin (z 0) ρ ≤ 32*ρ)
    (nz : ∀ j, 0 < length (z 0) j)
    (init : ‖gridR (n+1) (z 0)‖ ≤ ((n:ℝ)+1)^2)
    (small : CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ (z 0) ≤ 1/(4*(π*((n:ℝ)+1))^2))
    (Vbound : frozenArea (n+1) ((n+1)^32) τ (z 0) ≤ V₀) :
    |CircleFlowMoments.mean (z (CircleFlowTracking.horizon (n+1))) -
      CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) (z 0)| ≤
      6*CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ (z 0)*V₀ +
        44928*(1+V₀)*V₀/((n:ℝ)+1)^16 + 1/((n:ℝ)+1)^16 := by
  let D := (n:ℝ)+1
  let T : ℝ := CircleFlowTracking.horizon ((n:ℝ)+1)
  let K := CircleGridSpectrum.sampledMatrix (N := n+1) τ
  let p := rowOp (fun _ : Fin (n+1) => CircleSpectrum.weight τ n)
  let a := CircleFlowPath.residual (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32:ℕ):ℝ)) (z 0)
  let f := CircleSpectralPathLength.referencePath τ a
  have h3 : 3 ≤ n+1 := by omega
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast hN
  have ht : 0 ≤ T := Nat.cast_nonneg _
  have h0 : 0 ≤ τ := by linarith
  have dc : (n:ℝ)+1 = D := rfl
  have tt : (CircleFlowTracking.horizon ((n:ℝ)+1) : ℝ) = T := by simp [T]
  have start : gridR (n+1) (z 0) = f 0 := (CircleSpectralPathLength.referencePath_zero τ a).symm
  have df (s : ℝ) : HasDerivAt f (-(gramOp K (f s))) s :=
    CircleSpectralPathLength.referencePath_deriv τ h0 hτ' a s
  have bcap := weight_abs_le_one n τ h0
  have pcap : ‖p‖ ≤ 1 := rowOp_norm (Nat.succ_pos _) zero_le_one (fun _ => bcap)
  let γ := CircleGridSpectrum.aliasValue (CircleGridSpectrum.tangentCoeff τ) (0:ZMod (n+1))
  have γpos : 0 < γ := by
    exact lt_of_lt_of_le (by positivity : 0 < 1/(π*((n+1:ℕ):ℝ))^2)
      (CircleGridSpectrum.tangent_gap h3 ho τ hτ hτ' 0)
  have γmin : 1/π^2 ≤ γ := by
    have wb := CircleGridSpectrum.weight_from_grid_alias n h3 ho τ h0 hτ'
    have l := (le_abs_self _).trans bcap
    rw [wb, div_le_one γpos] at l
    exact (div_le_div_of_nonneg_right (by linarith : 1 ≤ 2+τ) (sq_nonneg π)).trans l
  have transient := frozen_mode f (gramOp K) p ht γpos df (CircleGridSpectrum.gramOp_eigenrow τ _ h0 hτ')
  have px := (p.le_opNorm (f 0)).trans (mul_le_mul pcap ((by rw [← start]; exact init) : ‖f 0‖ ≤ D^2)
    (norm_nonneg _) zero_le_one)
  rw [one_mul,Real.norm_eq_abs] at px
  have stop : |p (f T)| ≤ 1/D^16 := by
    rw [transient,abs_mul,abs_of_pos (exp_pos _)]
    apply (mul_le_mul_of_nonneg_left px (exp_pos _).le).trans
    simpa only [dc,tt] using fast_transient d γmin
  let Z := CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) (z 0)
  have vb : (∫ s in (0:ℝ)..T, ‖f s‖) ≤ V₀ := by
    simpa only [frozenArea,Nat.cast_add,Nat.cast_one] using Vbound
  have same := sharp_stopped_design n T ht hN ho τ hτ hτ' V₀ z F energy margins nz init small vb
  change |CircleFlowMoments.mean (z (CircleFlowTracking.horizon ((n:ℝ)+1)))-Z| ≤ _
  rw [tt,show CircleFlowMoments.mean (z T)-Z = (CircleFlowMoments.mean (z T)-(Z+p (f T)))+p (f T) by ring]
  exact (abs_add_le _ _).trans (add_le_add same stop)


/-- A Borel event under the actual Gaussian law on which the sharp
data-dependent error bound holds for every admissible path family starting
at each seed. The only remaining input is an upper bound on the frozen
Fourier path, which can be supplied by the spectral path-length theorem. -/
theorem gaussian_sharp_endpoint (n k : ℕ) (hN : 36864 ≤ n+1) (hk : k+17 ≤ n+1)
    (ho : Odd (n+1)) (τ : ℝ) (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2)
    (V₀ : State ((n+1)^32) → ℝ) (vdom : ∀ ω, frozenArea (n+1) ((n+1)^32) τ ω ≤ V₀ ω) :
    ∃ G : Set (State ((n+1)^32)), MeasurableSet G ∧
      (CircleEscapeBridge.seedLaw ((n+1)^32)).real Gᶜ ≤ 14/((n:ℝ)+1)^k ∧
      ∀ ω ∈ G, ∀ z : ℝ → State ((n+1)^32), z 0 = ω →
        IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
          (CircleFlowTracking.horizon ((n:ℝ)+1)) z →
        |CircleFlowMoments.mean (z (CircleFlowTracking.horizon ((n:ℝ)+1))) -
          CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) ω| ≤
          6*CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ ω*V₀ ω +
          44928*(1+V₀ ω)*V₀ ω/((n:ℝ)+1)^16 + 1/((n:ℝ)+1)^16 := by
  have hh : |τ| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; exact hτ'
  obtain ⟨G,meas,tail,inside⟩ := CircleSharpEvent.design_event (n+1) k hN hk hh
  refine ⟨G,meas,by simpa using tail,?_⟩
  intro ω hw z init F
  obtain ⟨nz,en,rd,B,marg⟩ := inside ω hw
  have h32 : 32 ≤ n+1 := by omega
  let D := (n:ℝ)+1
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast h32
  have dp : 0 < D := by linarith
  have pp := pow_le_pow_left₀ pi_pos.le pi_lt_four.le 2
  have big := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) d 5
  have cmp : 4/D^7 ≤ 1/(4*(π*D)^2) := by
    rw [show D^7=D^2*D^5 by ring]
    field_simp
    nlinarith only [pp,big]
  subst ω
  refine sharp_design_endpoint n h32 ho τ hτ hτ' _ z F en (by simpa using marg) nz ?_ ?_ (vdom _)
  · simpa only [gridR,CircleGaussianTracking.initialRms,Nat.cast_add,Nat.cast_one] using rd
  · apply LE.le.trans _ cmp
    simpa only [Nat.cast_add,Nat.cast_one] using B


/-- The preceding event with its actual finite-width Gaussian Fourier budget.
Both factors on its right hand side are now concrete seed functions with
separately verified fourth moments. -/
theorem gaussian_spectral_endpoint (n k : ℕ) (hN : 36864 ≤ n+1) (hk : k+17 ≤ n+1)
    (ho : Odd (n+1)) (τ : ℝ) (hτ : 1/2 ≤ τ) (hτ' : τ ≤ 2)
    :
    let V₀ := CircleSpectralPathLength.seedBudget ho ((n+1)^32)
    ∃ G : Set (State ((n+1)^32)), MeasurableSet G ∧
      (CircleEscapeBridge.seedLaw ((n+1)^32)).real Gᶜ ≤ 14/((n:ℝ)+1)^k ∧
      ∀ ω ∈ G, ∀ z : ℝ → State ((n+1)^32), z 0 = ω →
        IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
          (CircleFlowTracking.horizon ((n:ℝ)+1)) z →
        |CircleFlowMoments.mean (z (CircleFlowTracking.horizon ((n:ℝ)+1))) -
          CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) ω| ≤
          6*CircleSharpInitialization.initialError (n+1) ((n+1)^32) τ ω*V₀ ω +
          44928*(1+V₀ ω)*V₀ ω/((n:ℝ)+1)^16 + 1/((n:ℝ)+1)^16 := by
  intro V₀
  exact gaussian_sharp_endpoint n k hN hk ho τ hτ hτ' V₀ (fun ω =>
    CircleSpectralPathLength.seedBudget_dominates ho hτ hτ' (Nat.cast_nonneg _) ω)

/-- The baseline and both compared rates fit simultaneously from the same
Gaussian draw, at the original physical horizon and with polynomial failure
of any fixed order. The Borel event works for every compatible continuation
of the three flows, including different continuations at the same rate. -/
theorem joint_fit_original_horizon (n k : ℕ) (hN : 36864 ≤ n+1)
    (hk : k+17 ≤ n+1) (ho : Odd (n+1)) :
    ∃ G : Set (State ((n+1)^32)), MeasurableSet G ∧
      (CircleEscapeBridge.seedLaw ((n+1)^32)).real Gᶜ ≤ 44/((n:ℝ)+1)^k ∧
      ∀ ω ∈ G, ∀ τ : ℝ, (τ = 1/2 ∨ τ = 1 ∨ τ = 2) →
        ∀ z : ℝ → State ((n+1)^32), z 0 = ω →
          IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
            (CircleFlowTracking.horizon ((n:ℝ)+1)) z →
          ‖gridR (n+1) (z (CircleFlowTracking.horizon ((n:ℝ)+1)))‖ ≤ 1/((n:ℝ)+1)^3 ∧
          |CircleFlowMoments.mean (z (CircleFlowTracking.horizon ((n:ℝ)+1))) -
            CircleEscapeBridge.reference (n+1) ((n+1)^32) (CircleSpectrum.weight τ n) ω| ≤
            (1+176*π^2)/((n:ℝ)+1)^3 := by
  let μ := CircleEscapeBridge.seedLaw ((n+1)^32)
  let D := (n:ℝ)+1
  let I (τ : ℝ) := {ω : State ((n+1)^32) | ¬GoodInit τ (designRadius D) (designTolerance D)
    (CircleGridSpectrum.sampledMatrix τ) (fun _ : Fin (n+1) => CircleSpectrum.k0 τ) ω}
  obtain ⟨G₀,_,mass,inside⟩ := CircleSharpEvent.design_event (n+1) k hN hk (τ:=1) (by norm_num)
  let B := ((G₀ᶜ ∪ I (1/2)) ∪ I 1) ∪ I 2
  have h32 : 32 ≤ n+1 := by omega
  have d : 32 ≤ D := by dsimp [D]; exact_mod_cast h32
  have rp : 0 ≤ designRadius D := by dsimp [designRadius,D]; positivity
  have ri := (design_bounds d).1
  have tail (τ : ℝ) (hτ : |τ| ≤ 2) : μ.real (I τ) ≤ 10/D^k := by
    simpa only [I,D,μ,designTolerance,Nat.cast_add,Nat.cast_one] using
      CircleSharpEvent.initialization_power (n+1) k hN (by omega) hτ rp ri
  have m0 : μ.real G₀ᶜ ≤ 14/D^k := by simpa only [μ,D,Nat.cast_add,Nat.cast_one] using mass
  refine ⟨(toMeasurable μ B)ᶜ,(measurableSet_toMeasurable μ B).compl,?_,?_⟩
  · change μ.real ((toMeasurable μ B)ᶜ)ᶜ ≤ 44/D^k
    rw [compl_compl,measureReal_def,measure_toMeasurable,←measureReal_def]
    have h1 := (measureReal_union_le (μ:=μ) G₀ᶜ (I (1/2))).trans
      (add_le_add m0 (tail (1/2) (by norm_num)))
    have h2 := (measureReal_union_le (μ:=μ) (G₀ᶜ ∪ I (1/2)) (I 1)).trans
      (add_le_add h1 (tail 1 (by norm_num)))
    exact ((measureReal_union_le (μ:=μ) ((G₀ᶜ ∪ I (1/2)) ∪ I 1) (I 2)).trans
      (add_le_add h2 (tail 2 (by norm_num)))).trans_eq (by ring)
  · intro ω hg τ allowed z start F
    have hb : ω ∉ B := fun h => hg (subset_toMeasurable μ B h)
    have h : ω ∈ G₀ ∧ ω ∉ I (1/2) ∧ ω ∉ I 1 ∧ ω ∉ I 2 := by
      simpa only [B,mem_union,mem_compl_iff,not_or,not_not,and_assoc] using hb
    obtain ⟨nz,_,rd,_,_⟩ := inside ω h.1
    have hi : ω ∉ I τ := by
      rcases allowed with rfl|rfl|rfl
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2
    have ok : GoodInit τ (designRadius D) (designTolerance D)
        (CircleGridSpectrum.sampledMatrix τ) (fun _ : Fin (n+1) => CircleSpectrum.k0 τ) ω :=
      not_not.mp hi
    have bounds : 1/2 ≤ τ ∧ τ ≤ 2 := by rcases allowed with rfl|rfl|rfl <;> norm_num
    subst ω
    exact design_endpoint n h32 ho τ bounds.1 bounds.2 z F ok
      (by simpa only [gridR,CircleGaussianTracking.initialRms,Nat.cast_add,Nat.cast_one] using rd) nz

/-- With failure at most 44/N¹⁵⁸, any choice of three same-seed
realizations both fits all three grids and agrees to 2/N³ between every
pair in the normalized Euclidean training coordinates. -/
theorem three_rate_fit_and_disagreement (n : ℕ) (hN : 36864 ≤ n+1) (ho : Odd (n+1))
    (z : ℝ → State ((n+1)^32) → ℝ → State ((n+1)^32))
    (start : ∀ τ ω, z τ ω 0 = ω)
    (flow : ∀ τ, (τ = 1/2 ∨ τ = 1 ∨ τ = 2) → ∀ ω,
      IsFlow (circleInput (n+1)) (circleLabel (n+1)) (1/sqrt (((n+1)^32 : ℕ):ℝ)) τ
        (CircleFlowTracking.horizon ((n:ℝ)+1)) (z τ ω)) :
    let T : ℝ := CircleFlowTracking.horizon ((n:ℝ)+1)
    ∃ G : Set (State ((n+1)^32)), MeasurableSet G ∧
      (CircleEscapeBridge.seedLaw ((n+1)^32)).real Gᶜ ≤ 44/((n:ℝ)+1)^158 ∧
      ∀ ω ∈ G, ∀ τ : ℝ, (τ = 1/2 ∨ τ = 1 ∨ τ = 2) →
        ‖gridR (n+1) (z τ ω T)‖ ≤ 1/((n:ℝ)+1)^3 ∧
        ∀ τ' : ℝ, (τ' = 1/2 ∨ τ' = 1 ∨ τ' = 2) →
          ‖gridR (n+1) (z τ ω T)-gridR (n+1) (z τ' ω T)‖ ≤ 2/((n:ℝ)+1)^3 := by
  intro T
  obtain ⟨G,mg,p,inside⟩ := joint_fit_original_horizon n 158 hN (by omega) ho
  refine ⟨G,mg,p,?_⟩
  intro ω hω τ hτ
  have bound (s : ℝ) (hs : s = 1/2 ∨ s = 1 ∨ s = 2) :=
    (inside ω hω s hs (z s ω) (start s ω) (flow s hs ω)).1
  refine ⟨bound τ hτ,?_⟩
  intro s hs
  exact (norm_sub_le _ _).trans ((add_le_add (bound τ hτ) (bound s hs)).trans_eq (by ring))

end CircleSharpTracking
