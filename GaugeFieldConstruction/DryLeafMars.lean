import GaugeFieldConstruction.CodaMars
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
/-!
# cuffs. quantified cubic cost for M1-through infin contours.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Set Filter MeasureTheory Measure Complex Analysis Points Bulb
open scoped ContDiff Topology BigOperators
variable {n:ℕ}
-- choose template on E4; aperture shift
noncomputable def ΔLeafMars:ContDiffBump (0:E4):= ⟨1/8,1/4,by norm_num,by norm_num⟩
noncomputable def leafMars(x:E4)(r:ℝ)(h:0<r):Bulb where
 f y:= ΔLeafMars (r⁻¹ • (y-x))
 d:= ΔLeafMars.contDiff.comp (by fun_prop)
 c:= by
    let e:= (Homeomorph.subRight x).trans (Homeomorph.smul (Units.mk0 (r⁻¹:ℝ) (inv_pos.mpr h).ne')) -- tune
    exact (ΔLeafMars.hasCompactSupport.comp_homeomorph e)
abbrev phiM := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis=>ℝ)).symm
noncomputable def RodMars:= ‖phiM.toContinuousLinearMap‖+1
lemma RodCostMars :1≤RodMars:=by unfold RodMars; exact le_add_of_nonneg_left (norm_nonneg _)
lemma taxMars (x y:E4): cubedist x y ≤ dist x y :=by
 rw[dist_eq_norm]; unfold cubedist; rw[dist_eq_norm]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun i=>PiLp.norm_apply_le (x-y) i)
lemma peakMars(x y:E4): dist x y ≤ RodMars*cubedist x y := (phiM.toContinuousLinearMap.le_of_opNorm_le (show _≤RodMars from le_add_of_nonneg_right (zero_le_one)) _) -- tune sub
lemma leaf_support (x y:E4)(r:ℝ)(h:0<r)(t:y∈ (leafMars x r h).run): cubedist y x ≤ r/4:=by
 let g(z:E4):= r⁻¹ • (z-x)
 have he:Continuous g:=by unfold g; fun_prop
 have hz:closure (g ⁻¹' Function.support (ΔLeafMars:E4→ℝ))⊆ g ⁻¹' tsupport (ΔLeafMars:E4→ℝ):= closure_minimal (preimage_mono subset_closure) ((isClosed_tsupport _).preimage he)
 have hv: g y∈tsupport (ΔLeafMars:E4→ℝ):=hz t
 rw[ΔLeafMars.tsupport_eq] at hv; have hp:= Metric.mem_closedBall.mp hv; unfold g at hp; rw[dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr h), inv_mul_le_iff₀ h] at hp; refine (taxMars y x).trans ?_; rw [dist_eq_norm]; exact hp.trans (Eq.le (by unfold ΔLeafMars; dsimp; ring))
lemma LeafHomeMars (x y:E4)(r:ℝ)(h:0<r)(p:dist y x < r/8): lit (leafMars x r h) y:=by
 have he:Continuous (fun y:E4=> dist y x):= continuous_id.dist continuous_const
 filter_upwards [(he.tendsto y).eventually (gt_mem_nhds p)] with z hz
 change ΔLeafMars (r⁻¹ • (z-x))=1; refine ΔLeafMars.one_of_mem_closedBall (Metric.mem_closedBall.mpr ?_); rw[dist_zero_right,norm_smul,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h), inv_mul_le_iff₀ h]; change dist z x < r/8 at hz; rw [dist_eq_norm] at hz; refine hz.le.trans (Eq.le ?_); change _= r*(1/8); ring
noncomputable def ThinMars := ((8*RodMars):ℝ)⁻¹
lemma thinMars_pos:0<ThinMars:= by unfold ThinMars; exact inv_pos.mpr (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one RodCostMars))
lemma ThinMars_limit: ThinMars≤1/8:=by unfold ThinMars; rw [inv_le_iff_one_le_mul₀ (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one RodCostMars))]; nlinarith [RodCostMars]
lemma LowerMars(x y:E4)(r:ℝ)(h:0<r)(p:y ∈ (leafMars x r h).shore): ThinMars*r ≤ cubedist y x:=by
 by_contra! v; have e0 : 0 < RodMars:=lt_of_lt_of_le zero_lt_one RodCostMars
 have he:= (peakMars y x).trans_lt (mul_lt_mul_of_pos_left v e0); rw [show RodMars*(ThinMars*r)=r/8 from ?_] at he; · exact centre (LeafHomeMars x y r h he) p
 unfold ThinMars; field_simp
lemma ThemeMars (r:ℝ)(h:0<r)(x:Points n)(p:spaced r x)(k:Fin n):BreatherMars (leafMars (x k) r h) k x:=by
 refine ⟨spaced_conf h p,LeafHomeMars _ _ r h ?_,fun i y v=>?_⟩
 · simp [h]
 have t:= (p _ _ y).trans (leaf_support _ _ _ h v); linarith
lemma theme_addMars (r:ℝ)(h:0<r)(x:Points n)(p:spaced r x)(k:Fin n)(y:E4)(e:y∈ (leafMars (x k) r h).shore) : spaced (ThinMars*r) (Points.cons y x):=by
 have ht: ThinMars*r≤r/8:= (mul_le_mul_of_nonneg_right ThinMars_limit h.le).trans (Eq.le (by ring))
 have hu:=leaf_support _ _ _ h (strands e)
 have hv (i:Fin n): ThinMars*r ≤ cubedist y (x i):=by
    by_cases hi:i=k
    · subst i; exact LowerMars _ _ r h e
    have hx:=p _ _ hi
    have hp:cubedist (x i) (x k) ≤ cubedist y (x i)+cubedist y (x k):=by unfold cubedist; rw[dist_comm (y.ofLp) (x i).ofLp]; exact dist_triangle .. -- parsing
    linarith
 intro i j; refine Fin.cases ?_ ?_ i
 · refine Fin.cases (by simp) (fun j h=>hv j) j
 intro i; refine Fin.cases ?_ (fun j e=> ?_) j
 · intro l; change _≤cubedist (x i) y; unfold cubedist; rw[dist_comm]; exact hv i
 exact ht.trans (le_trans (by linarith) (p i j (fun h=> e (by rw[h])))) -- tune
lemma DleafMars (r:ℝ)(h:0<r)(x y:E4)(a:Axis): (LED (leafMars x r h) a).f y=r⁻¹ * D (basis a) (ΔLeafMars) (r⁻¹ • (y-x)):=by
 let U:E4→L[ℝ] E4:= r⁻¹ • ContinuousLinearMap.id ℝ E4
 let g:=fun y=> r⁻¹ • (y-x)
 have he:HasFDerivAt g U y:=by
    rw[show g=(fun y=>r⁻¹ • y - r⁻¹ • x) from funext fun y=> smul_sub _ _ _]; exact U.hasFDerivAt.sub_const _
 change fderiv ℝ ((ΔLeafMars) ∘ g) y (basis a)= _; rw [fderiv_comp y (ΔLeafMars.contDiff.differentiable (by exact one_ne_zero) _) he.differentiableAt,he.fderiv,ContinuousLinearMap.comp_apply]; exact map_smul (fderiv ℝ ΔLeafMars (g y)) (r⁻¹) (basis a) -- tune
noncomputable def LeafC (a:Axis):ℝ:=∫ y:E4, ‖D (basis a) ΔLeafMars y‖
lemma Leaf_posMars (a:Axis):0≤LeafC a:= integral_nonneg fun i=>norm_nonneg _
lemma LeafMintMars (r:ℝ)(h:0<r)(v:r≤1)(x:E4)(a:Axis): (∫ y:E4, ‖(LED (leafMars x r h) a).f y‖) ≤ r⁻¹*LeafC a:=by
 simp_rw [DleafMars _ h,norm_mul,Real.norm_of_nonneg (r:=r⁻¹) (inv_pos.mpr h).le] -- tune syntax
 rw[integral_const_mul]
 let F:=fun y:E4=> ‖D (basis a) ΔLeafMars y‖
 have he:(∫ y:E4,F (r⁻¹ • (y-x)))= r^(Module.finrank ℝ E4) • ∫ y:E4,F y:=by
    have hs:=(integral_add_right_eq_self (μ:=volume) (fun y:E4=> F (r⁻¹ • y)) (-x)) -- tune
    simp_rw[sub_eq_add_neg]; exact hs.trans (Measure.integral_comp_inv_smul_of_nonneg volume F h.le)
 apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr h).le; change (∫ y:E4,F (r⁻¹ • (y-x))) ≤ LeafC a; rw [he]; exact mul_le_of_le_one_left (Leaf_posMars a) (pow_le_one₀ h.le v)
#print axioms LeafMintMars
end YM.GaugeFieldConstruction.Fathom
