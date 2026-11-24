/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.ShellReg
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Leg invoices differentiated at fixed shell. Keep angular weight fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Row Function Filter Set YM.Analysis MeasureTheory
open YM.Maxwell (grad)
open YM.Maxwell.Free (collar gradient_part gradient_smooth shell_cost)
open scoped Topology BigOperators ContDiff
variable {x : E4} {χ : E4→ℝ} {B : Dollars}

/-- freedom of choosing point tests all x in a neighborhood. -/
structure Chassis (x y : E4) (χ : E4 → ℝ) extends Cost χ : Prop where
  here : χ =ᶠ[𝓝 x] fun _=>1
  there : y ∉ tsupport χ
lemma Chassis.distinct {y} (c : Chassis x y χ) : x≠y := fun e=> c.there (e ▸ YM.Maxwell.Free.enclosed _ c.here)
lemma Chassis.route {y} (c : Chassis x y χ) : ∀ᶠ x' in 𝓝 x, Chassis x' y χ := by
  filter_upwards [c.here.eventuallyEq_nhds] with z h; exact ⟨c.toCost,h,c.there⟩

abbrev Shore (χ : E4→ℝ) := tsupport (fderiv ℝ χ)
lemma Chassis.gate {y} (c : Chassis x y χ) {z} (h : z∈ Shore χ) : x ≠ z ∧ y≠z :=
  ⟨fun p=> collar c.here (p.symm ▸ h), fun p=> c.there (p.symm ▸ tsupport_fderiv_subset ℝ h)⟩

-- constant speed

def road (x : E4) (v : Axis) (t : ℝ) := x+t • basis v
lemma p0 (x v) : road x v 0=x:= by simp [road]
lemma speed (x v) (t : ℝ) : HasDerivAt (road x v) (basis v) t := by
  refine (((hasDerivAt_id' t).smul_const (basis v)).const_add x).congr_deriv ?_; simp
lemma ridge (x v) : Continuous (road x v) := continuous_const.add (continuous_id'.smul continuous_const)
lemma speedy {F : FunC} {y v t} (h : ContDiffAt ℝ ∞ F (road y v t)) :
    HasDerivAt (fun t=> F (road y v t)) (grad v F (road y v t)) t := (h.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt _ (speed y v t)
lemma fast {F : FunC} {x v} (h : ContDiffAt ℝ ∞ F x) :
    HasDerivAt (fun t=>F (road x v t)) (grad v F x) 0 := by
  have he:= speedy (v:=v) (y:=x) (t:=0) (F:=F) (by rw [p0]; exact h); rwa [p0] at he

-- parametrized Flux numerator
lemma spends {y : E4} (c : Chassis x y χ) (j L : E4→Jobs) (v : Axis)
    (p : ∀ z : E4 × E4, z.1≠ y → z.2 ≠ y → z.2 ≠ z.1 → ∀ i,ContinuousAt (fun z : E4 × E4=> j z.1 i z.2) z)
    (q : ∀ z : E4×E4, z.1≠y→z.2≠ y→z.2≠z.1→∀ i,ContinuousAt (fun z : E4×E4=> L z.1 i z.2) z)
    (h : ∀ z:E4,z≠y→ ∀ t : ℝ,road x v t≠y → z≠ road x v t→ ∀ i : Axis,
      HasDerivAt (fun t : ℝ=> j (road x v t) i z) (L (road x v t) i z) t) :
    HasDerivAt (fun t:ℝ=> Flux χ (j (road x v t))) (Flux χ (L x)) 0 := by
  classical
  simp_rw [flux_sum]; apply HasDerivAt.fun_sum; intro i _
  let U := Shore χ
  have P := ridge x v
  have H : ∀ᶠ t in 𝓝 (0:ℝ), Chassis (road x v t) y χ := (show Tendsto (road x v) (𝓝 0) (𝓝 x) from by simpa only [p0] using P.continuousAt (x:= (0:ℝ)) |>.tendsto) c.route
  obtain ⟨r,hr,hR⟩:= Metric.nhds_basis_closedBall.mem_iff.mp H
  let A:=Metric.closedBall (0:ℝ) r
  have ha : A∈𝓝 0:= Metric.closedBall_mem_nhds _ hr
  let F (t : ℝ) z:= grad i χ z • j (road x v t) i z
  let G (t : ℝ) z:=grad i χ z • L (road x v t) i z
  have hU : IsCompact U := c.compact.fderiv _
  have he {z : ℝ×E4} (hx:z∈A×ˢ U):z.2≠road x v z.1 ∧ z.2≠y := ⟨((hR hx.1).gate hx.2).1.symm,((hR hx.1).gate hx.2).2.symm⟩
  have hk : ContinuousOn (fun z : ℝ× E4=> G z.1 z.2) (A×ˢ U) := fun z hz=> ContinuousAt.continuousWithinAt (((gradient_smooth c.health i).continuous.comp continuous_snd).continuousAt.smul ((q (road x v z.1,z.2) ((hR hz.1).distinct) (he hz).2 (he hz).1 i).comp (x:=z) (f:=fun w : ℝ×E4=> (road x v w.1,w.2)) ((P.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd)))
  obtain ⟨s,hs⟩:= ((isCompact_closedBall (0:ℝ) r).prod hU).exists_bound_of_continuousOn hk
  have ep {t} (u:t∈A) :Integrable (F t) := shell_cost c.health c.compact (fun z a=> (p (road x v t,z) ((hR u).distinct) (he (z:=(t,z)) ⟨u,a⟩).2 (he (z:=(t,z)) ⟨u,a⟩).1 i).comp (x:=z) (f:=fun y:E4=>(road x v t,y)) (continuousAt_const.prodMk continuousAt_id)) i
  have eq {t} (u:t∈A) :Integrable (G t) := shell_cost c.health c.compact (fun z a=> (q (road x v t,z) ((hR u).distinct) (he (z:=(t,z)) ⟨u,a⟩).2 (he (z:=(t,z)) ⟨u,a⟩).1 i).comp (x:=z) (f:=fun y:E4=>(road x v t,y)) (continuousAt_const.prodMk continuousAt_id)) i
  have E: HasDerivAt (fun t:ℝ=>∫ z:E4,F t z) (∫ z:E4,G 0 z) 0 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F':=G) (bound:=U.indicator fun _=> s) ha (Eventually.mono ha fun _ h=> (ep h).1) (ep (mem_of_mem_nhds ha)) (eq (mem_of_mem_nhds ha)).1 ?_ ((continuousOn_const.integrableOn_compact hU).integrable_indicator hU.measurableSet) ?_).2
  · simp only [F,G,p0] at E; exact E
  · refine Eventually.of_forall fun z t ht=> ?_
    by_cases hy : z∈U
    · rw [indicator_of_mem hy _]; exact hs (t,z) ⟨ht,hy⟩
    have g: grad i χ z=0 := image_eq_zero_of_notMem_tsupport fun a=> hy (gradient_part χ i a)
    simp [G,g,indicator_of_notMem hy]
  refine Eventually.of_forall fun z t ht=> ?_
  by_cases hy : z∈U
  · exact (h z (he (z:=(t,z)) ⟨ht,hy⟩).2 t ((hR ht).distinct) (he (z:=(t,z)) ⟨ht,hy⟩).1 i).const_smul (grad i χ z)
  have g : grad i χ z=0:= image_eq_zero_of_notMem_tsupport fun a=> hy (gradient_part χ i a)
  simpa only [F,G,g,zero_smul] using! hasDerivAt_const t (0:ℂ)

lemma pulse {y} (c : Chassis x y χ) {J J' : Jobs} (p :∀ i z,z∈Shore χ→ContinuousAt (J i) z) (g :∀ i z,z∈ Shore χ→ContinuousAt (J' i) z):
    Flux χ (J+J')=Flux χ J+Flux χ J' := by
  simp only [flux_sum,Pi.add_apply,smul_add]
  simp_rw [integral_add (shell_cost c.health c.compact (p _) _) (shell_cost c.health c.compact (g _) _),Finset.sum_add_distrib]
lemma atlas (χ : E4→ℝ) (J:Jobs) (r : ℂ) : Flux χ (r • J)=r*Flux χ J := by
  simp only [flux_sum,Pi.smul_apply]
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
  simp_rw [Complex.real_smul,smul_eq_mul,mul_left_comm (↑(grad i χ _) : ℂ) r,integral_const_mul]
end YM.GaugeFieldConstruction.Flux.One
