import GaugeFieldConstruction.Zaba
import GaugeFieldConstruction.Trump
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell Analysis
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
open HopeC Finset Lattice Exterior CF.Crest CF.Vale.Veins
-- purchase limit on packet compacts by veil
lemma stranger (F:E4→ℂ)(h:Integrable F volume): Tendsto (fun z:ℝ=> (πnorm:ℂ)*(∫ p:E4,(veil z⁻¹ p:ℂ)*F p)) atTop (𝓝 ((πnorm:ℂ)*(∫ p,F p))):=by
 refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence (fun p:E4=> ‖F p‖) (Eventually.of_forall (fun z=> AEStronglyMeasurable.mul (by unfold veil; fun_prop) h.1)) ?_ h.norm ?_)
 · filter_upwards [eventually_ge_atTop (0:ℝ)] with i t; refine Eventually.of_forall fun z=>?_ ; rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply mul_le_of_le_one_left (norm_nonneg _); apply Real.exp_le_one_iff.mpr; nlinarith [inv_nonneg.mpr t,sq_nonneg ‖z‖,mul_nonneg (inv_nonneg.mpr t) (sq_nonneg ‖z‖)]
 refine Eventually.of_forall fun i=>?_ ; let f (t:ℝ):= (veil t i:ℂ)*F i; have he: Continuous f:=by unfold f veil; fun_prop
 have h0: F i=f 0:=by simp [f,veil]
 change Tendsto (fun i=> f i⁻¹) _ _; rw [h0]; exact ((he.tendsto 0).comp tendsto_inv_atTop_zero)
lemma gamut (p:E4): CF.Crest.Shore.radius p.ofLp=‖p‖^2:=Stationary.geode_sum p
abbrev Ferry(X Y:HopeC E4):= HopeC.addQ (rev X) Y
variable (i j: Cover× PlaqAxes) (r: TypeFace 1)
abbrev brackC := Ferry (FlatR i) (FlatR j)
abbrev Frames (i j:PlaqAxes)(r:TypeFace 1)(a b:Axis):ℝ:= -spikeT i r a* spikeT j r b
lemma phat (z:ℝ)(p:E4): (veil z p:ℂ)* WritW i j r p.ofLp =∑ a:Axis,∑ b:Axis,(Frames i.2 j.2 r a b:ℂ)*(ξH (brackC i j) p*kip [a,b] z p):=by
 unfold WritW; simp_rw [gamut,Bart_r]; simp_rw [show ξH (brackC i j) p=star (ξH (FlatR i) p)*ξH (FlatR j) p from ((adds (rev (FlatR i)) _ _).trans (by rw [revs]))]
 have hh(a:Axis):star (dotbill p [a]) = -dotbill p [a]:=by simp [dotbill,Complex.star_def,mul_comm]
 unfold standU; rw [star_mul, star_sum]; simp_rw [Finset.mul_sum, Finset.sum_mul,star_mul
 ]; rw [Finset.sum_comm] -- tune
 simp_rw [Finset.mul_sum,hh,show ∀ r:ℝ,star (r:ℂ)=r from fun r=>Complex.conj_ofReal _]
 refine sum_congr rfl (fun a _=>?_); refine sum_congr rfl (fun b _=>?_)
 simp only [hh,Frames,Complex.ofReal_neg,Complex.ofReal_mul,kip,dotbill,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; unfold Hη; push_cast; ring
abbrev cashGrad (a b:PlaqAxes)(v:TypeFace 1)(p:E4):ℂ:= ∑ i:Axis,∑ j:Axis,(Frames a b v i j:ℂ)* (↑(regD [i,j] Green p):ℂ)
lemma pepperH (h:0∉ (brackC i j).site): gridQ i j r= ∫ x, cashGrad i.2 j.2 r x∂(brackC i j).μ:=by
 rw [(Seaport i j r).2]; let P:=brackC i j; let W(p:E4):=WritW i j r p.ofLp; let X(a b:Axis)(p t:E4):=W p -- remove
 let B(a b:Axis)(z:ℝ)(p:E4):= ξH P p * kip [a,b] z⁻¹ p; let E(a b:Axis)(p:E4):ℂ:= (↑(regD [a,b] Green p):ℂ); let c(a b:Axis):ℂ:= Frames i.2 j.2 r a b
 have hz(a b): Integrable (E a b) P.μ:= span_v P _ fun x e=> Complex.continuous_ofReal.continuousWithinAt.comp ((quietC _ _ x (freeSmooth (fun u=>h (u ▸ e)))).continuousAt.continuousWithinAt) (Set.mapsTo_univ _ _) -- tune
 have ht(a b:Axis):Tendsto (fun z:ℝ=> (πnorm:ℂ)*(∫ p, B a b z p)) atTop (𝓝 (∫ x, E a b x∂P.μ)):= approach P [a,b] (by simp) h
 suffices Y: Tendsto (fun z:ℝ=> (πnorm:ℂ)*(∫ p:E4,(veil z⁻¹ p:ℂ)*W p)) atTop (𝓝 (∫ x,cashGrad i.2 j.2 r x∂P.μ)) by apply tendsto_nhds_unique _ Y; exact stranger W (Seaport ..).1
 have he: (∫ x,cashGrad i.2 j.2 r x∂P.μ)=∑ a:Axis, ∑ b:Axis,c a b*(∫ x,E a b x∂P.μ):=by
    change (∫ x,∑ a:Axis,∑ b:Axis, c a b * E a b x ∂P.μ)=_; simp_rw [integral_finsetSum _ (fun i _=> integrable_finsetSum _ (fun j _=> (hz i j).const_mul _)), integral_finsetSum _ (fun b _=>(hz _ b).const_mul (c _ b)), integral_const_mul] -- tune
 rw [he]; apply ((tendsto_finsetSum univ (fun a _=> tendsto_finsetSum univ (fun b _=> (ht a b).const_mul (c a b))))).congr'
 filter_upwards [eventually_gt_atTop (0:ℝ)] with z h; have he(a b): Integrable (B a b z) volume:= (Hanse P _ (by simp only [List.length_cons,List.length_nil,zero_add]; omega) z⁻¹ (inv_pos.mpr h)).1
 simp_rw [show ∀ p:E4, (veil z⁻¹ p:ℂ)*W p=∑ a:Axis,∑ b:Axis,c a b*B a b z p from (fun i'=> phat ..)]
 rw [integral_finsetSum, Finset.mul_sum]; swap; · intro i _; exact integrable_finsetSum _ (fun j _=> (he i j).const_mul _)
 refine sum_congr rfl (fun i _=>?_); rw [integral_finsetSum _ (fun j _=>(he i j).const_mul _),Finset.mul_sum]; exact sum_congr rfl fun j _=>by rw [integral_const_mul]; ring
lemma turn_sp (i:PlaqAxes)(f:Axis→ TypeFace 1→ℝ): ∑ v:TypeFace 1,∑ a:Axis, spikeT i v a*f a v=f i.val.1 (coord i.val.2)-f i.val.2 (coord i.val.1):=by
 unfold spikeT; simp_rw [sub_mul,sum_sub_distrib,ite_mul] -- `simp` control
 congr 1 <;> simp [ite_and,ite_mul]
lemma meetC (u v:PlaqAxes)(p:E4)(h:p≠0): (∑ r:TypeFace 1,cashGrad u v r p)= ↑(bareCurl u.val.1 u.val.2 v.val.1 v.val.2 p):=by
 unfold cashGrad; simp_rw [← Complex.ofReal_mul,← Complex.ofReal_sum]; apply congrArg; let A:=u.val.1; let B:=u.val.2; let C:=v.val.1; let D:=v.val.2
 let G(i j:Axis) := regD [i,j] Green p; let T:=fun a r=> ∑ b:Axis, -spikeT v r b*G a b; have hf:(∑ r:TypeFace 1,∑ a:Axis,∑ b:Axis,Frames u v r a b*regD [a,b] Green p)=∑ r:TypeFace 1,∑ a:Axis,spikeT u r a*T a r:=by unfold T G Frames; simp_rw [Finset.mul_sum]; ring_nf -- tune B vars
 rw [hf,turn_sp u T]; change T A (coord B)-T B (coord A)= grad A (curlOpp B C D) p-grad B (curlOpp A C D) p; rw [Bare.opp_grad h,Bare.opp_grad h]
 have ht(k l:Axis): T k (coord l)= (if C=l then grad k (grad D Green) p else 0) - if D=l then grad k (grad C Green) p else 0:=by
    unfold T spikeT; simp_rw [←coord_map,Equiv.apply_eq_iff_eq]; unfold C D; by_cases h1:v.val.1=l <;> by_cases h2:v.val.2=l <;> simp_rw [neg_mul,sub_mul,sum_neg_distrib,sum_sub_distrib] <;> simp only [h1,h2,and_true,and_false,if_false,ite_mul,one_mul,zero_mul] -- tune simp rewrite equality values -> replace rfl changing gradient axes v. may simp.
    all_goals simp [G,regD] <;> ring
 rw [ht,ht]
lemma spellCurl (h:0∉ (brackC i j).site): (∑ r:TypeFace 1,gridQ i j r)= (∫ x, (↑(bareCurl i.2.val.1 i.2.val.2 j.2.val.1 j.2.val.2 x):ℂ) ∂(brackC i j).μ):=by
 let P:=brackC i j
 have he(a b:Axis):ContinuousOn (fun x=> (↑(regD [a,b] Green x):ℂ)) P.site:=fun x e=> ((Complex.continuous_ofReal.continuousAt.comp (quietC _ _ _ (freeSmooth (fun p=>h (p ▸ e)))).continuousAt).continuousWithinAt) -- tune
 simp_rw [pepperH _ _ _ h]; rw [← integral_finsetSum]; swap; · intro r _; apply span_v; unfold cashGrad; exact continuousOn_finsetSum univ fun _ _=> continuousOn_finsetSum univ fun a _=> continuousOn_const.mul (he _ _)
 exact integral_congr_ae (P.onA.mono fun x e=> meetC _ _ _ (fun p=> h (p ▸ e)))
#print axioms spellCurl
end YM.StressFHeat
end
