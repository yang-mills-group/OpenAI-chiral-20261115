import YM.CF.Char.Casier
import YM.CF.Char.Jars
set_option autoImplicit false
noncomputable section
namespace YM.CF.Neige
open Char Summit
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
variable {α E:Type} [Fintype α][DecidableEq α] [NormedAddCommGroup E][NormedSpace ℝ E] {p:α→Site c}{a:ℕ} {K v d s t:ℝ} {n:ℕ}
open Finset Filter
lemma cap_pi {f : E→ Matrix α α ℝ}{x:E} (h:∀ i j, Allows n (fun y=>f y i j) x K)(hK:0  ≤  K): ContDiffAt ℝ n f x:=FreeResolvent.TestD.rectangle_smooth (fun i j=> (h i j).smooth)
lemma liftM {f : E→ Matrix α α ℝ}{x:E}{v:α→α→ℝ}(h:∀ i j, Allows n (fun y=> f y i j) x (v i j : ℝ))(hp:∀ i,∑ j,v i j  ≤ K)(hK:0  ≤  K): Allows n (fun y=>paintO (f y)) x K:=by -- v func explicit
 let P:Matrix α α ℝ→L[ℝ] Fish α →L[ℝ] Fish α:= paintO; let H(y):=P (f y)
 have hf:ContDiffAt ℝ n f x:= FreeResolvent.TestD.rectangle_smooth (fun i j=>(h i j).smooth); refine ⟨(P.contDiff.contDiffAt.comp x hf),fun i hi=>Planned.AtomRegular.op_le_of_unit hK fun b hb=>?_⟩
 change ‖iteratedFDeriv ℝ i (P ∘ f) x b‖ ≤ K
 erw [P.iteratedFDeriv_comp_left hf (i:=i) (by exact_mod_cast hi)]
 let T:=iteratedFDeriv ℝ i f x b
 change ‖P T‖  ≤  K; apply ContinuousLinearMap.opNorm_le_bound _ hK; intro w; apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg _))).mpr; intro j
 change |∑ k,T j k*w k|  ≤  _
 apply (Finset.abs_sum_le_sum_abs ..).trans; apply (sum_le_sum (g:=fun k=>v j k*‖w‖) fun k _=>?_).trans ((Finset.sum_mul ..).symm.le.trans (mul_le_mul_of_nonneg_right (hp j) (norm_nonneg _))) -- orientation
 rw [abs_mul]; apply mul_le_mul _ (norm_le_pi_norm w k) (abs_nonneg _) (h j k).nonneg
 let X:= FreeResolvent.TestD.evaluate j k; change ‖X (iteratedFDeriv ℝ i f x b)‖ ≤ _; rw [show X (iteratedFDeriv ℝ i f x b)=iteratedFDeriv ℝ i (X ∘ f) x b by erw [X.iteratedFDeriv_comp_left hf (i:=i) (by exact_mod_cast hi)]; rfl]; have ht:= ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le ((h j k).norm_le _ hi) hb -- tune
 simp only [prod_const,card_univ,Fintype.card_fin,one_pow,mul_one] at ht; exact ht
open LocalJet
lemma panel_w(i: Rows.In x A F (G:=G)) : (∑ j:Rows.In x A F (G:=G), if j∈panels A F i then (1:ℝ) else 0)  ≤  chips S (radiusB x)*Fintype.card G.ColorIndex:=by
 let L:= PatchReads.lift (G:=G) (x:=x) (A:=A) (F:=F); let g(i:PatchReads.Full S G):=i
 let I:= Finset.univ.filter (fun j=> j∈panels A F i); let X:= (members S (front A F i) (radiusB x)) ×ˢ (Finset.univ : Finset G.ColorIndex)
 have hv : ∀ j∈I,L j∈ X:=fun j hj=> mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,(ball_member (show j∈panels A F i from (mem_filter.mp hj).2)).trans (Nat.div_le_self ..)⟩,mem_univ _⟩
 calc
    _ = (I.card:ℝ):=by rw [← sum_filter]; simp [I]
    _  ≤  (X.card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card_of_injOn L hv ((PatchReads.lifting_injective (G:=G) A x F).injOn)) -- tune
    _  ≤  _:= by unfold X; rw [card_product,Nat.cast_mul,card_univ]; exact mul_le_mul_of_nonneg_right (saves ..) (Nat.cast_nonneg _)
variable {K':Teller G}{q:Chi}{B:ℝ}
lemma paintD {u:ℝ}(hx:1000 ≤ radiusB x)(he:shirt G K' P x K u n l)(hr:Cert P K' S T x)(hc:sizedP G P K' S T F)(hp:A.flags=RG.flags (temp x) V): Allows n (fun y=>paintO (driftN T x (Vmove x V y) k A F q B Y l)) 0 ((chips S (radiusB x)*Fintype.card G.ColorIndex)*(K*u)):=by
 obtain ⟨hu,hv,hK,h⟩:=he; obtain ⟨hr,hμ,hH⟩:=h S T A F hr hc V hp k q B Y
 have ht:0 ≤ chips S (radiusB x):=by unfold chips grain; positivity
 apply liftM (v:=fun i j=> (if j∈panels A F i then 1 else 0)*(K*u)) ?_ ?_ (by positivity)
 · intro i j; by_cases hl:j∈panels A F i
   · rw [if_pos hl,one_mul]; exact hH i j
   rw [if_neg hl,zero_mul]; simp_rw [driftN, Matrix.sub_apply,hessN_off hr hl hx, gram_off hr hl hx,sub_self]; exact allows_const _ (by simp)
 intro i; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (panel_w i) (by positivity)
lemma warp_h {g:Config G c→Matrix α α ℝ}(p:α→Site c)(h:Polar 0 p p (g∘(AnalyticBridge.SectorAffine.field V)) n d C)(hd:0<d)(hC:0 ≤ C)(hg:temp x  ≤ 1):
 Allows n (fun y=> paintO (g (Vmove x V y))) 0 (composeCost n (activation G n 0 d*C) 1):=by -- constraints G? α
 have ht :=polar_cash (0:Directions G c) (g ∘ AnalyticBridge.SectorAffine.field V) (by rw [map_zero]; exact h) hC hd
 let L := temp x • ContinuousLinearMap.id ℝ (Directions G c); have hv:=Work.E04.temp_nonneg x; have hL:Allows n L (0:Directions G c) 1:=allows_linear ((pole0 (temp x) _ ℝ hv).trans hg) (by simp only [map_zero,norm_zero]; simp)
 apply ((show Allows n _ (L 0) _ from (map_zero L).symm ▸ ht).comp (f:=L) hL).germ; exact Eventually.of_forall fun y=> congrArg paintO (congrArg g (reader_field ..)) -- tune
end YM.CF.Neige
