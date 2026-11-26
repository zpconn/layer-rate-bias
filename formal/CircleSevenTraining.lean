module

public import CircleSevenGrouped
public import CircleGroupedWidth
import all CircleSevenDesign
import all CircleSevenGrouped
import all CircleSevenSpectrum
import all CircleFiniteWidth
import all CircleFiniteConfidence
import all CircleGroupedDynamics
import all CircleGroupedWidth
import Mathlib.Tactic

/-! The three concrete Gaussian initialization guarantees at the seven-point design. -/
@[expose] public section
noncomputable section
namespace CircleSevenTraining
open Real MeasureTheory Set Filter Topology CircleSevenDesign CircleSevenGrouped CircleSevenSpectrum
  CircleFiniteConfidence CircleRateTrajectory CircleEscapeBridge CircleWidthTracking CircleFlowPath

private theorem grid : gridScale 7 (1/20) = h := by norm_num [gridScale,h]
private theorem signed : signedScale 7 b (1/20) = v := by norm_num [signedScale,rowScale,v]
private theorem gap_eq : CircleFiniteWidth.gap 7 = gap := by unfold CircleFiniteWidth.gap gap;ring
private theorem drift_eq : CircleGroupedDynamics.drift 7 b = drift := rfl
private theorem D_eq : CircleFiniteWidth.D 7 (1/20) = ordinaryD := by
  rw [CircleFiniteWidth.D,gap_eq];norm_num [CircleFiniteWidth.R,ordinaryD]
private theorem coeff : CircleSpectrum.weight 1 6=b := weight_one

private theorem scalar (D C k : ℝ) :
    (max (2*D) (max (sqrt (36/(1/20))) (max (k*((7:ℝ)+1)/((1/20)*(2*D)))
      (max (2*(h+36*(2*D))/gap) ((2*(7:ℝ)^2*D/(1/20))*(v+C*(2*D)))))))^2=
      requiredWidth D C k := by
  unfold requiredWidth
  rw [show (36:ℝ)/(1/20)=720 by norm_num,
    show k*((7:ℝ)+1)/((1/20)*(2*D))=k*160/(2*D) by ring,
    show 2*(7:ℝ)^2*D/(1/20)=1960*D by ring]
  simp only [max_assoc]

private theorem angular_width (D : ℝ) :
    (CircleGroupedWidth.width 6 D (1/20) (1/20))^2=requiredWidth D drift 135 := by
  unfold CircleGroupedWidth.width
  norm_num only [Nat.reduceAdd] 
  rw [coeff,grid,signed,gap_eq,drift_eq]
  convert scalar D drift 135 using 1; norm_num

private theorem original_width :
    (CircleFiniteWidth.width 6 (1/20) (1/20))^2=requiredWidth ordinaryD (36*(1+b)) 10 := by
  unfold CircleFiniteWidth.width CircleFiniteWidth.A
  norm_num only [Nat.reduceAdd]
  rw [coeff,grid,signed,gap_eq,D_eq,show (1+b)*36*(2*ordinaryD)=36*(1+b)*(2*ordinaryD) by ring]
  convert scalar ordinaryD (36*(1+b)) 10 using 1; norm_num

private theorem cap : CircleFiniteWidth.cap 7 (1/2) (1/20) (1/20)=19966 := by
  unfold CircleFiniteWidth.cap CircleFiniteWidth.tol CircleFiniteWidth.R
  rw [gap_eq]
  convert horizon using 2; norm_num

/-- At least 95% of the original joint Gaussian seeds achieve both advertised
errors at iteration 19966 and converge to an interpolating parameter vector. -/
def Guarantee (m : ℕ) : Prop :=
  ∃ E : Set (Seed m), MeasurableSet E ∧ (seedLaw m).real Eᶜ≤1/20 ∧ ∀ z∈E,
    rms (1/2) 7 z 19966≤1/343 ∧
    |learnerMean (1/2) 7 z 19966-reference 7 m (CircleSpectrum.weight 1 6) z|≤1/980 ∧
    ∃ w : State m, Tendsto (iterateAt 7 (1/2) z) atTop (𝓝 w) ∧ ‖CircleActualTracking.gridR 7 w‖=0

private theorem extract {m : ℕ} {D : ℝ} (z : Seed m) (h : CircleGroupedWidth.Trained 6 (1/2) (1/20) (1/20) D z) :
    rms (1/2) 7 z 19966≤1/343 ∧
    |learnerMean (1/2) 7 z 19966-reference 7 m (CircleSpectrum.weight 1 6) z|≤1/980 ∧
    ∃ w : State m, Tendsto (iterateAt 7 (1/2) z) atTop (𝓝 w) ∧ ‖CircleActualTracking.gridR 7 w‖=0 := by
  unfold CircleGroupedWidth.Trained at h
  norm_num only [Nat.reduceAdd] at h
  rw [cap] at h
  exact ⟨by norm_num at h ⊢;exact h.1,by norm_num at h ⊢;exact h.2.1,h.2.2.2⟩

private theorem from_sq {x : ℝ} {m M : ℕ} (h : x^2≤(M:ℝ)) (w : M≤m) : x≤sqrt (m:ℝ) := by
  have h' : x^2≤(m:ℝ) := h.trans (by exact_mod_cast w)
  exact (le_abs_self x).trans ((sq_le_sq₀ (abs_nonneg _) (sqrt_nonneg _)).mp
    (by rwa [sq_abs,sq_sqrt (Nat.cast_nonneg m)]))

theorem original {m : ℕ} (hw : 4*10^27≤m) : Guarantee m := by
  have bnd := sufficient_widths.1
  rw [←original_width] at bnd
  have g := CircleFiniteWidth.finite_width 6 m (by decide) (by decide)
    (η:=1/2) (δ:=1/20) (ε:=1/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (from_sq (by exact_mod_cast bnd) hw)
  obtain ⟨E,me,prob,test⟩ := g
  exact ⟨E,me,prob,fun z hz => extract z (test z hz)⟩

theorem angular {m : ℕ} (hw : 243*10^23≤m) : Guarantee m := by
  have bnd := sufficient_widths.2.1
  rw [←angular_width,←D_eq] at bnd
  obtain ⟨E,me,prob,test⟩ := CircleGroupedWidth.full_path 6 m (by decide) (by decide)
    (η:=1/2) (δ:=1/20) (ε:=1/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (from_sq (by exact_mod_cast bnd) hw)
  exact ⟨E,me,prob,fun z hz => extract z (test z hz)⟩

theorem grouped {m : ℕ} (hw : 407*10^16≤m) : Guarantee m := by
  have bnd := sufficient_widths.2.2
  rw [←angular_width] at bnd
  have fp : 0<CircleGroupedResidual.groupCost 7 3 sevenLevel sevenRate := by rw [cost_eq];linarith only [grouped_F.1]
  have deq : 2*sqrt (6/(1/20))*CircleGroupedResidual.groupCost 7 3 sevenLevel sevenRate=groupedD := by
    rw [cost_eq]; norm_num [groupedD]
  obtain ⟨E,me,prob,test⟩ := CircleGroupedWidth.grouped 6 m (by decide) (by decide)
    (η:=1/2) (δ:=1/20) (ε:=1/20) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    3 sevenLevel sevenRate level_le rate_pos rate_le_one (fun r => (rate_eigen r).le) fp
    (deq ▸ from_sq (by exact_mod_cast bnd) hw)
  exact ⟨E,me,prob,fun z hz => extract z (test z hz)⟩

private theorem log_bracket {x y k a c : ℕ} (hx : 0<x) (hy : 0<y) (hk : 0<k)
    (lower : 10^a*y^k<x^k) (upper : x^k<10^c*y^k) :
    (a:ℝ)/k<log ((x:ℝ)/y)/log 10 ∧ log ((x:ℝ)/y)/log 10<(c:ℝ)/k := by
  have xp : (0:ℝ)<x := Nat.cast_pos.mpr hx
  have yp : (0:ℝ)<y := Nat.cast_pos.mpr hy
  have kp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have ten : 0<log (10:ℝ) := log_pos (by norm_num)
  have l : (10:ℝ)^a<((x:ℝ)/y)^k := by
    rw [div_pow,lt_div_iff₀ (pow_pos yp k)]; exact_mod_cast lower
  have u : ((x:ℝ)/y)^k<(10:ℝ)^c := by
    rw [div_pow,div_lt_iff₀ (pow_pos yp k)]; exact_mod_cast upper
  have L := log_lt_log (by positivity) l
  have U := log_lt_log (by positivity) u
  rw [log_pow,log_pow] at L U
  constructor
  · rw [div_lt_div_iff₀ kp ten];linarith only [L]
  · rw [div_lt_div_iff₀ ten kp];linarith only [U]

/-- Exact rational-power comparisons certify the two-decimal log gaps and
the 2.22 and 6.78 order reductions from the displayed sufficient widths. -/
theorem log_gaps :
    let logRatio (x y : ℕ) := log ((x:ℝ)/y)/log 10
    (24.885 < logRatio (4*10^27) 512 ∧ logRatio (4*10^27) 512 < 24.895) ∧
    (22.675 < logRatio (243*10^23) 512 ∧ logRatio (243*10^23) 512 < 22.685) ∧
    (15.895 < logRatio (407*10^16) 512 ∧ logRatio (407*10^16) 512 < 15.905) ∧
    (2.215 < logRatio (4*10^27) (243*10^23) ∧ logRatio (4*10^27) (243*10^23) < 2.225) ∧
    (6.775 < logRatio (243*10^23) (407*10^16) ∧ logRatio (243*10^23) (407*10^16) < 6.785) := by
  intro logRatio
  have p0 := log_bracket (x:=4*10^27) (y:=512) (k:=200) (a:=4977) (c:=4979)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  have p1 := log_bracket (x:=243*10^23) (y:=512) (k:=200) (a:=4535) (c:=4537)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  have p2 := log_bracket (x:=407*10^16) (y:=512) (k:=200) (a:=3179) (c:=3181)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  have p3 := log_bracket (x:=4*10^27) (y:=243*10^23) (k:=200) (a:=443) (c:=445)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  have p4 := log_bracket (x:=243*10^23) (y:=407*10^16) (k:=200) (a:=1355) (c:=1357)
    (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (by decide +kernel)
  dsimp only [logRatio]
  exact ⟨by norm_num at p0 ⊢;exact p0,by norm_num at p1 ⊢;exact p1,by norm_num at p2 ⊢;exact p2,by norm_num at p3 ⊢;exact p3,by norm_num at p4 ⊢;exact p4⟩
end CircleSevenTraining
