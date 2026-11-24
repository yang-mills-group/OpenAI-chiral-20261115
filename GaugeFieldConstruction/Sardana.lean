import GaugeFieldConstruction.CobaltF
import GaugeFieldConstruction.Zapt
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators HopeC Finset CF.Crest CF.Vale.Veins
open Maxwell Analysis Lattice
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
open GaugeFieldConstruction GaugeFieldConstruction.Cauchy CF.Fock.Flux
abbrev localeΨ (x:Cover):=addQ (point (off x)) SpecW
lemma frost(p:E4): star (CF.Crest.Shore.weave p.ofLp)=CF.Crest.Shore.weave p.ofLp:=by unfold CF.Crest.Shore.weave; rw [star_prod]; exact prod_congr rfl fun _ _=> Complex.conj_ofReal _
lemma off_sub (x y:Cover): off (x-y)=off x-off y:=by ext i; simp [off]
variable (x y:Cover)(i j:Cauchy.Spin)
abbrev menagerie := Ferry (localeΨ x) (localeΨ y)
abbrev crΩ (v:Axis):ℂ:= -2*star (Hij v i j)
lemma Gray_Z (z:ℝ)(p:E4): (veil z p:ℂ)*RomanG (y-x) i j p.ofLp=∑ a:Axis, crΩ i j a*(ξH (menagerie x y) p * kip [a] z p):=by
 unfold RomanG  -- remove
 unfold tenderD; simp_rw [Finset.mul_sum]; apply sum_congr rfl; intro a _
 rw [adds (rev (localeΨ x)) (localeΨ y),revs,adds (point _) SpecW, adds (point (off y)), xi_point, xi_point,specie,star_mul,star_pow,frost]
 rw [←off_r,off_sub,sub_eq_add_neg, sum_r,opp_r]; unfold kip dotbill lightsU crΩ; simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]; rw [gamut]; unfold Hη; push_cast; ring -- tune
lemma bondF (z:E4)(h:z≠0): Gap.eye ((2:ℝ) • z) (Wick.blend i j)=∑ a:Axis, crΩ i j a*(↑(regD [a] Green z):ℂ):=by
 let p:ℝ:=2; have hv:0<p:=two_pos; have he:(p • z)≠0:=smul_ne_zero hv.ne' h
 unfold Wick.blend; rw [map_sum]; refine sum_congr rfl fun a _=>?_ ; rw [map_smul,Wick.flashStone _ he]; simp only [smul_eq_mul]; change _= crΩ i j a* ↑(grad a Green z); rw [first_Green h,first_Green he]; unfold crΩ; rw [norm_smul,Real.norm_of_nonneg hv.le]; change (-16:ℂ)*_ * ↑((-2:ℝ)*normal*(p*z a) *((p*‖z‖)^2)⁻¹^2)=_; unfold p; push_cast; ring
lemma Marne (h: 0∉(menagerie x y).site): RomT (y-x) i j=∫ z, (Wick.blend i j).val ((2:ℝ) • z) ∂(menagerie x y).μ:=by
 rw [(Aqueduct (y-x) i j).2]; let P:=menagerie x y; let F(p:E4):= RomanG (y-x) i j p.ofLp
 have W:= stranger F (Aqueduct ..).1; let T (a:Axis)(z:E4):ℂ:= ↑(regD [a] Green z)
 have ht(a:Axis): Integrable (T a) P.μ:= span_v P _ fun x e=> ((Complex.continuous_ofReal.continuousAt.comp ((quietC _ _ x (freeSmooth (fun u=>h (u ▸ e)))).continuousAt)).continuousWithinAt)
 have hp: (∫ z, (Wick.blend i j).val ((2:ℝ) • z) ∂P.μ)=∑ a:Axis, crΩ i j a*(∫ z, T a z∂P.μ):=by
    change (∫ z, Gap.eye ((2:ℝ) • z) (Wick.blend i j)∂P.μ)=_
    rw [integral_congr_ae (g:=fun z=> ∑ a:Axis, crΩ i j a*T a z) (P.onA.mono fun z v=> bondF i j z (fun p=>h (p▸v))),integral_finsetSum _ (fun i _=> (ht i).const_mul _)]; simp_rw [integral_const_mul]
 rw [hp]; refine tendsto_nhds_unique W (((tendsto_finsetSum univ (fun a _=> (approach P [a] (by simp) h).const_mul (crΩ i j a)))).congr' ?_)
 filter_upwards [eventually_gt_atTop (0:ℝ)] with z h; let L (a:Axis)(p:E4):= ξH P p* kip [a] z⁻¹ p; have hm(i:Axis): Integrable (L i) volume:= (Hanse P _ (by simp) _ (inv_pos.mpr h)).1
 simp_rw [show ∀ p:E4,(veil z⁻¹ p:ℂ) * F p= ∑ a: Axis, crΩ i j a*L a p from fun p=>Gray_Z x y i j _ p]; rw [integral_finsetSum _ (fun a _=> (hm a).const_mul (crΩ ..)),Finset.mul_sum]; exact sum_congr rfl fun a _=>by rw [integral_const_mul]; apply mul_left_comm -- tune
lemma greenCar (u v:Cover × PlaqAxes)(h: 0∉ (brackC u v).site): (∑ r:Exterior.TypeFace 1,gridQ u v r)=∫ x,(Wick.curl u.2.val.1 u.2.val.2 v.2.val.1 v.2.val.2).val x∂(brackC u v).μ:=by
 rw [spellCurl u v h]; exact integral_congr_ae ((brackC u v).onA.mono fun x v=> (Gap.lap _ _ (show x≠0 from fun z=> h (z ▸ v))).symm)
#print axioms Marne
end YM.StressFHeat
end
