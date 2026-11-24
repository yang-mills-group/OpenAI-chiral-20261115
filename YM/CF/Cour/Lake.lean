import YM.CF.Souk.Hill
import YM.CF.Cour.Foil
import YM.CF.Hors.Galet
import YM.CF.Esti.Jet
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Cour
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink Hors
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {ι τ:Type} [Fintype ι] [Fintype τ]{f g:Fish (ι⊕τ)→ℂ}{A d s t r x:ℝ}{n:ℕ}
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
open Souk
variable {G:Gauge}{c f:Side}{S:StepData c f}{F:Forest S.ratio}{m z:Mast G c→ Fish (Key F G)}{u t p C A D:ℝ}{ι:Type}[Fintype ι]{E: Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:ℕ}
lemma lin_p (Y:Fish ι→ E)(j:Fin n→ι)(h:ContDiffAt ℝ (↑n) Y 0)(L:E→L[ℝ] ℝ): Uniform.entry (L ∘ Y) 0 j=L (Uniform.entry Y 0 j):=by unfold Uniform.entry; rw [L.iteratedFDeriv_comp_left h le_rfl]; rfl
structure Funds (Y:Fish ι→ E)(Q:ℝ):Prop where
 stiff:ContDiffAt ℝ 2 Y 0
 offer(i:Fin 1→ι): ‖Uniform.entry Y 0 i‖ ≤ Q
 charge (i: Fin 2→ι):‖Uniform.entry Y 0 i‖ ≤ Q
lemma Funds.peeks{Y:Fish ι →E}(h: Funds Y C)(L:E→L[ℝ] ℝ)(v:‖L‖≤1): FloorZ (L ∘ Y) C:=by
 have he(y:E):‖L y‖ ≤ ‖y‖:= (L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) v)
 refine ⟨L.contDiff.contDiffAt.comp _ h.stiff,fun i=> ?_,fun v=>?_⟩ <;> rw [lin_p _ _ (h.stiff.of_le (by norm_num))] -- tunes
 · exact (he _).trans (h.offer _)
 exact (he _).trans (h.charge _)
variable {Y H:Positions (Uniform.Joint F G) →ℂ}
lemma bring {q q':Fish ι→E}(j:Fin n→ι)(h:ContDiffAt ℝ n q 0)(h':ContDiffAt ℝ n q' 0): Uniform.entry (q-q') 0 j=Uniform.entry q 0 j-Uniform.entry q' 0 j:=by unfold Uniform.entry; rw [iteratedFDeriv_sub_apply h h']; rfl
def pierce(F:Fish ι→E)(C:ℝ):Prop:= ContDiffAt ℝ 2 F 0∧∀ j:Fin 2→ι,‖Uniform.entry F 0 j‖≤ C
lemma pick(h:GoodsR F m z t C D)(hx:Funds H A)(hz:Funds (Y-H) u)(hd:D≤1)(ht:0 ≤ A)(hp:0 ≤ u)(he:0≤ C)(hb:0≤ D): let X:=flute F m t; let W:= flute F z t
 let N:= D*A+2*D*((C+1)*A) +(C*u+C*(C*u)); pierce (H ∘ X-Y ∘ W) (2*N):=by
 intro M V W; obtain ⟨h,hH,hL,hY,hZ⟩:=h; change M 0=0 at h; change V 0=0 at hH; let H':=H ∘ M; let K:= H ∘ V; let Y':=(Y-H) ∘ V; have hl := (show ContDiffAt ℝ 2 H (M 0) by rw [h]; exact hx.stiff).comp 0 hL; have hc:= (show ContDiffAt ℝ 2 H (V 0) by rw [hH]; exact hx.stiff).comp 0 hY; have he':= (show ContDiffAt ℝ 2 (Y-H) (V 0) by rw [hH]; exact hz.stiff).comp 0 hY
 let N:=H'-K; let D':=Y∘V; rw [show H∘M-Y∘V=N-Y' from ?_]; swap; · ext1 i; unfold N H' K Y'; simp only [Pi.sub_apply,Function.comp_apply]; abel
 refine ⟨(hl.sub hc).sub he',fun k=>?_⟩
 have hu(i:Uniform.Primary c G) : costU (Uniform.entry M 0 (fun _ :Fin 1=>i)) ≤ C+1 ∧ costU (Uniform.entry V 0 (fun _:Fin 1=>i)) ≤ C+1:=by
    let q:Fin 1→Uniform.Primary c G:=fun _=>i; obtain ⟨p,v⟩:=hZ 0 (by decide) q; let a:= Uniform.entry (M-V) 0 q; let b:= Uniform.entry V 0 q; refine ⟨?_,p.trans (le_add_of_nonneg_right zero_le_one)⟩; rw [show Uniform.entry M 0 (fun _:Fin 1=>i)=b+a from ?_]; swap; · unfold a b; rw [bring _ (hL.of_le (by norm_num)) (hY.of_le (by norm_num))]; abel
    apply le_trans ?_ (add_le_add p (v.trans hd)); change costU (_+_) ≤ costU _+_; unfold costU; rw [←Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; exact abs_add_le ..
 let Z:=Uniform.entry (N-Y') 0 k; have hh (L: ℂ→L[ℝ] ℝ) (hy:‖L‖ ≤1): |L Z| ≤ W:=by
    have hW:=rise (hz.peeks L hy) hH (z:=V) hY hp he (fun i u j=> (hZ i u j).1) k; have hT:= roll_E (hx.peeks L hy) h hH hL hY ht hu (fun i u j=>(hZ i u j).2) k
    change |Uniform.entry (L ∘ Y') 0 k| ≤ _ at hW; change |Uniform.entry (L ∘ H') 0 k -Uniform.entry (L ∘ K) 0 k| ≤ _ at hT
    have hJ:ContDiffAt ℝ (2:ℕ) N 0:=(hl.sub hc).of_le (by norm_num)
    rw [show L Z= Uniform.entry (L ∘ H') 0 k -Uniform.entry (L ∘ K) 0 k- Uniform.entry (L ∘ Y') 0 k from ?_]; exact (abs_sub ..).trans (add_le_add hT hW)
    unfold Z N; rw [bring _ hJ (he'.of_le (by norm_num)), bring _ (hl.of_le (by norm_num)) (hc.of_le (by norm_num)), lin_p _ _ (hl.of_le (by norm_num)),lin_p _ _ (hc.of_le (by norm_num)), lin_p _ _ (he'.of_le (by norm_num)),map_sub,map_sub]
 apply (Complex.norm_le_abs_re_add_abs_im Z).trans; rw [two_mul]; exact add_le_add (hh Complex.reCLM (by simp)) (hh Complex.imCLM (by simp))
end YM.CF.Cour
