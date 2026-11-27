module
public import CircleFiniteCoefficient
public import CircleClosedForms
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! Higher-order correction to the finite-grid population coefficient. -/
@[expose] public section
noncomputable section
namespace CircleCoefficientExpansion
open Real Filter Topology CircleSpectrum CircleFiniteCoefficient CircleClosedForms

private def A (s : ℝ) := 1/6-s/120+s^2/5040-s^3/362880
private def B (s : ℝ) := 1/2-s/24+s^2/720-s^3/40320
private def P (s : ℝ) := 1/40-s/1600-31*s^2/448000+13*s^3/69120000
private def a (x : ℝ) := (x-sin x)/x^3
private def b (x : ℝ) := (1-cos x)/x^2
private def u (x : ℝ) := (a x-A (x^2))/x^8
private def v (x : ℝ) := (b x-B (x^2))/x^8
private def D (s z : ℝ) := (5-2*s*z)*(4-s*z)

private theorem sin_jet (x : ℝ) : taylorWithinEval sin 11 Set.univ 0 x =
    x-x^3*A (x^2)-x^11/39916800 := by
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    Nat.factorial, iteratedDeriv_succ, A, Nat.reduceAdd, Finset.sum_range_succ]
  ring

private theorem cos_jet (x : ℝ) : taylorWithinEval cos 10 Set.univ 0 x =
    1-x^2*B (x^2)-x^10/3628800 := by
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_univ,
    Nat.factorial, iteratedDeriv_succ, B, Nat.reduceAdd, Finset.sum_range_succ]
  ring
private theorem u_limit : Tendsto u (𝓝[≠] 0) (𝓝 (1/39916800)) := by
  have h := Real.taylor_tendsto (n:=11) (f:=sin) (x₀:=0) convex_univ (Set.mem_univ 0) contDiff_sin.contDiffOn
  simp only [nhdsWithin_univ,sub_zero,sin_jet] at h
  have h' := ((tendsto_const_nhds (x:=(1/39916800:ℝ))).sub (h.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))))
  rw [sub_zero] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h0 : x≠0 := hx
  dsimp [u,a]
  field_simp [h0]
  ring

private theorem v_limit : Tendsto v (𝓝[≠] 0) (𝓝 (1/3628800)) := by
  have h := Real.taylor_tendsto (n:=10) (f:=cos) (x₀:=0) convex_univ (Set.mem_univ 0) contDiff_cos.contDiffOn
  simp only [nhdsWithin_univ,sub_zero,cos_jet] at h
  have h' := ((tendsto_const_nhds (x:=(1/3628800:ℝ))).sub (h.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))))
  rw [sub_zero] at h'
  apply h'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h0 : x≠0 := hx
  dsimp [v,b]
  field_simp [h0]
  ring

private def R (s : ℝ) := 1493*s^0/580608000
    -296383*s^1/1219276800000
    +2771*s^2/203212800000
    -422447*s^3/877879296000000
    +11929*s^4/1024192512000000
    -6413*s^5/36870930432000000
    +647*s^6/442451165184000000
    -13*s^7/4550926270464000000
private theorem cancellation (s : ℝ) : 6*A s * B s - P s * D s (A s) = s^4 * R s := by
  unfold A B P D R
  ring

private def correction (s U V : ℝ) :=
  let z := A s + s^4*U
  let w := B s + s^4*V
  (R s + 6*(U*w+A s*V) - P s*U*(-13*s+2*s^2*(z+A s))) / D s z

private theorem corrected (s U V : ℝ) (hD : D s (A s+s^4*U)≠0) :
    6*(A s+s^4*U)*(B s+s^4*V) / D s (A s+s^4*U) - P s = s^4*correction s U V := by
  unfold correction
  field_simp [hD]
  unfold D at *
  have cancel := cancellation s
  unfold D at cancel
  linear_combination cancel

private def phase (n : ℕ) := π/((n:ℝ)+1)

private theorem exact_product (n : ℕ) :
    let x := phase n
    ((n:ℝ)+1)^2*(weight (1/2) n-weight 2 n)*D (x^2) (a x) = π^2*6*a x*b x := by
  intro x
  let q := angle n
  have hq : 0 < q := by dsimp [q,angle]; positivity
  have hπ : π = 2*q*((n:ℝ)+1) := by dsimp [q,angle]; field_simp
  have hx : x = 2*q := by dsimp [x,phase,q,angle]; field_simp
  have hq' : q < π := by
    dsimp [q,angle]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith [pi_pos,mul_nonneg pi_pos.le (Nat.cast_nonneg (α:=ℝ) n)]
  have hs : sin q ≠ 0 := (sin_pos_of_pos_of_lt_pi hq hq').ne'
  have ha := aliasA_nonneg n
  have hb := aliasB_pos n
  have den : (1+aliasA n+aliasB n/5)*(1+aliasA n+aliasB n/2)≠0 := by positivity
  rw [weight_difference, mul_div_assoc', div_mul_eq_mul_div, div_eq_iff den]
  obtain ⟨hA,hB⟩ := alias_closed_forms n
  rw [hA,hB,hx,hπ]
  simp only [T₁,T₂,cot_eq_cos_div_sin,D,a,b,sin_two_mul,cos_two_mul_eq_one_sub, show angle n=q from rfl]
  field_simp [hs,hq.ne']
  ring

/-- The eighth-order rescaled remainder has a finite limit. In particular, after
the displayed sixth-order term the error is O(N⁻⁸), with N=n+1. -/
theorem expansion :
    Tendsto (fun n : ℕ =>
      let N := (n:ℝ)+1
      N^8 * (N^2*(weight (1/2) n-weight 2 n) -
        (π^2/40-π^4/(1600*N^2)-31*π^6/(448000*N^4)+13*π^8/(69120000*N^6))))
      atTop (𝓝 (6221*π^10/42577920000)) := by
  let x := phase
  have hx0 : Tendsto x atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => π/((n:ℝ)+1)) atTop (𝓝 0)
    simpa [x,phase,div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul π)
  have hx (n : ℕ) : 0<x n := by dsimp [x,phase]; positivity
  have punct : Tendsto x atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx0,Eventually.of_forall fun n => (hx n).ne'⟩
  have harg := (hx0.pow 2).prodMk_nhds ((u_limit.comp punct).prodMk_nhds (v_limit.comp punct))
  let c (p : ℝ × ℝ × ℝ) := correction p.1 p.2.1 p.2.2
  have cont : ContinuousAt c (0^2,1/39916800,1/3628800) := by
    dsimp [c,correction,D,A,B,P,R]
    fun_prop (disch := norm_num)
  have h := (cont.tendsto.comp harg).const_mul (π^10)
  have cv : π^10*c (0^2,1/39916800,1/3628800) = 6221*π^10/42577920000 := by
    norm_num [c,correction,D,A,B,P,R]
    ring
  rw [cv] at h
  apply h.congr'
  filter_upwards with n
  let s := (x n)^2
  have hA : A s+s^4*u (x n) = a (x n) := by
    dsimp only [s,u]
    field_simp [(hx n).ne']
    ring
  have hB : B s+s^4*v (x n) = b (x n) := by
    dsimp only [s,v]
    field_simp [(hx n).ne']
    ring
  have hπ : x n ≤ π := by
    dsimp [x,phase]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_nonneg pi_pos.le (Nat.cast_nonneg (α:=ℝ) n)]
  have small : s*a (x n) ≤ 1 := by
    dsimp only [s,a]
    field_simp [(hx n).ne']
    apply (div_le_iff₀ (hx n)).2
    linarith [sin_nonneg_of_nonneg_of_le_pi (hx n).le hπ]
  have hn : D s (a (x n))≠0 := by
    unfold D
    exact mul_ne_zero (by linarith) (by linarith)
  have id := corrected s (u (x n)) (v (x n)) (by rw [hA]; exact hn)
  rw [hA,hB] at id
  have ex := exact_product n
  change ((n:ℝ)+1)^2*(weight (1/2) n-weight 2 n)*D s (a (x n)) = _ at ex
  have un := (eq_div_iff hn).2 ex
  dsimp only [c,Function.comp_apply,Prod.mk.injEq]
  change π^10 * correction s (u (x n)) (v (x n)) = _
  rw [un]
  rw [show π^2*6*a (phase n)*b (phase n)/D s (a (x n)) =
    π^2*(6*a (x n)*b (x n)/D s (a (x n))) by dsimp [x]; ring]
  have poly : π^2*P s = π^2/40-π^4/(1600*((n:ℝ)+1)^2)-
      31*π^6/(448000*((n:ℝ)+1)^4)+13*π^8/(69120000*((n:ℝ)+1)^6) := by
    dsimp [P,s,x,phase]
    field_simp
  rw [←poly,←mul_sub,id]
  dsimp [s,x,phase]
  field_simp

end CircleCoefficientExpansion
