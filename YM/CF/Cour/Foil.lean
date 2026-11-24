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
lemma dash(f:Fish (ι⊕τ)→ℂ)(m:Fish ι→Fish τ)(s:ℝ)(x:Fish ι)(k:ι)(hm:DifferentiableAt ℝ m x)(hp:DifferentiableAt ℝ f (meetVar (s • x) (m x))):
 glance (fun y=> f (meetVar (s•y) (m y))) k x=s • glance f (.inl k) (meetVar (s•x) (m x))+∑ i, glance m k x i • glance f (.inr i) (meetVar (s•x) (m x)):=by
 let V:=s • ContinuousLinearMap.id ℝ (Fish ι); let U:=fderiv ℝ m x; let A:=Uniform.bolt k; let M:=meetVar (s•x) (m x); let H:=fderiv ℝ f M
 have hz := hp.hasFDerivAt.comp x ((Uniform.partSpace ι τ).symm.hasFDerivAt.comp x (V.hasFDerivAt.prodMk hm.hasFDerivAt)); unfold glance arrow; erw [hz.fderiv]; change H (meetVar (s•A) (U A))= s•H (bolt _) + ∑ i,(U A i) • H (bolt _) -- tune
 have he : meetVar (s•A) (U A)= s•bolt (.inl k)+ lowerCol (U A):=by ext e; cases e <;> simp [meetVar,Uniform.partSpace, A,lowerCol,Uniform.bolt,Pi.single_apply]
 rw [he,map_add,map_smul]; congr 1
 have hv(i:τ):lowerCol (ι:=ι) (bolt i)=bolt (.inr i):=by ext e; cases e<;> simp [lowerCol,Uniform.partSpace,Uniform.bolt,Pi.single_apply]
 nth_rw 1 [← Uniform.combine (U A)]
 rw [map_sum,map_sum]; simp_rw [map_smul,hv]
def straw(n:ℕ):ℝ:=1+(2:ℝ)^n*‖ContinuousLinearMap.mul ℝ ℂ‖
lemma straw_p :0 < straw n:=add_pos_of_pos_of_nonneg zero_lt_one (by positivity)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
lemma yarn{x:E}{f:E→ℝ}{g:E→ℂ}(h:Allows n f x A)(v:Allows n g x s):Allows n (fun i=> f i • g i) x (straw n*A*s):=by
 let L:=Complex.ofRealCLM; have he:= h.linear L (show ‖L‖ ≤ 1 by simp [L])
 rw [one_mul] at he
 exact (he.bilinear (ContinuousLinearMap.mul ℝ ℂ) v le_rfl).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) h.nonneg) v.nonneg)
section
lemma voyage {m z:Fish ι→Fish τ}{x:Fish ι}{a:ℝ}(i:ι)(L:Finset τ)
 (h:∀ y:Fish ι, ‖y‖<1→ Allows (n+1) m y (A*s)  ∧ Allows (n+1) z y (A*s))
 (he:∀ y:Fish (ι⊕τ), ‖y‖<r→ DifferentiableAt ℝ f y∧DifferentiableAt ℝ g y∧∀ i, Allows (n+1) (glance f i) y a∧ Allows n (glance (g-f) i) y d) (hs:0 ≤ s)(ha:1 ≤ A)(hv:3*A*s<r)(hr: 3*A*s ≤ 1)
 (ht:‖x‖<1)(hb: Allows n (fun y=>m y-z y) x t)(hl:∀ y:Fish ι, ‖y‖<1→∀ j, j ∉ L → glance m i y j=0) (Q:τ→ℝ)(hQ:∀ k, Allows n (fun y=>glance m i y k-glance z i y k) x (Q k)):
 let B:=composeCost n d 1 +2^n*composeCost n a 1*t
 Allows n (glance ((firmX g m s)-(firmX f z s)) i) x (s*B+ L.card*(straw n*(A*s)*B)+straw n*(∑ j,Q j)*composeCost n a 1):=by
 intro B; let hV(v:Fish ι→Fish τ)(y:Fish ι):= meetVar (s•y) (v y); let U:=hV m; let Z:=hV z
 have hu y(hy:‖y‖<1)(f:Fish ι→Fish τ)(h:Allows (n+1) f y (A*s)):Allows (n+1) (hV f) y (3*A*s):=by
    apply (turn_safe h h hs ha hy 0 (left_mem_Icc.mpr zero_le_one)).germ; filter_upwards with i; simp; rfl
 have hx y (hy:‖y‖<1):= he (U y) ((hu y hy _ (h _ hy).1).value.trans_lt hv); have hz y (hy:‖y‖<1) := he (Z y) ((hu _ hy _ (h _ hy).2).value.trans_lt hv)
 let D(i:ι⊕τ)(v:Fish ι):= glance g i (U v) - glance f i (Z v)
 have H(i:ι⊕τ): Allows n (D i) x B:=by
    have hm:= varying (n:=n) (f:=glance f i) (m:=m) (z:=z) (fun v hy=>(he v hy).2.2 _|>.1) ht (fun y hy=> ⟨((h y hy).1).order (by omega),(h y hy).2.order (by omega)⟩) hs ha hv hr hb
    apply ((((hx _ ht).2.2 _|>.2).comp (f:=U) (((hu _ ht _ (h _ ht).1).order (show n ≤ n+1 by omega)).mono hr)).add hm).germ
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with y (hy: y∈ball _ _)
    have hh:= hx _ (mem_ball_zero_iff.mp hy); change glance (g-f) i _ + _ = D _ _; unfold D; rw [show glance (g-f) i (U y)=glance g i (U y)-glance f i (U y) from glance_sub hh.2.1 hh.1 (bolt i)]
    change _-(glance f i (U y))+(glance f i (U y)-_) = _ ; abel
 let X(j:τ)(y:Fish ι):= glance m i y j • D (.inr j) y; let P(j:τ)(y:Fish ι):= (glance m i y j-glance z i y j) • glance f (.inr j) (Z y)
 have hh(j:τ) : Allows n (X j) x (straw n*(A*s)*B):= yarn (Char.readZ (seenY (h _ ht).1 i) j) (H _)
 have hT(j:τ) : Allows n (P j) x (straw n*(Q j)*composeCost n a 1):= yarn (hQ _) ((((hz _ ht).2.2 _|>.1).order (show n≤n+1 by omega)).comp (f:=Z) (((hu _ ht _ (h _ ht).2).mono hr).order (by omega))) -- costs compose mismatch n+1
 let W:ℝ:= composeCost n a 1; have hr := (((H (.inl i)).smul s).add (allows_sum (s:=L) (f:=X) (fun i _=> hh i))).add (allows_sum (s:=Finset.univ) (f:=P) (fun j _=>hT j)); rw [abs_of_nonneg hs] at hr; simp only [Finset.sum_const,nsmul_eq_mul] at hr; rw [Finset.mul_sum, Finset.sum_mul] -- check
 apply hr.germ; filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with y (hy:y∈ball _ _)
 have hb': ‖y‖<1:=mem_ball_zero_iff.mp hy
 rw [show glance ((firmX g m s)-(firmX f z s)) i y=glance (firmX g m s) i y-glance (firmX f z s) i y from glance_sub (f:= _ ∘ U) (g:= _ ∘ Z) ((hx _ hb').2.1.comp _ ((hu y hb' _ (h _ hb').1).smooth.differentiableAt (by norm_cast))) ((hz _ hb').1.comp _ ((hu _ hb' _ (h _ hb').2).smooth.differentiableAt (by norm_cast))) _,show glance (firmX g m s) i y=_ from dash g m s y _ ((h _ hb').1.smooth.differentiableAt (by norm_cast)) (hx _ hb').2.1,show glance (firmX f z s) i y=_ from dash f z s y _ ((h _ hb').2.smooth.differentiableAt (by norm_cast)) (hz _ hb').1]
 change s • D _ y+(∑ u∈L,X u y) + (∑ j,P j y)=_; rw [Finset.sum_subset (Finset.subset_univ L) (fun j _ hv=> (by unfold X; rw [hl _ hb' j hv,zero_smul] : X j y=0))]; unfold X P D; simp_rw [sub_smul, smul_sub,Finset.sum_sub_distrib]; unfold U Z hV; abel
end
end YM.CF.Cour
