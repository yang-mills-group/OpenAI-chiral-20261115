import YM.CF.Hors.Card
import YM.CF.Neige.Wit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
section norm
variable {ι τ:Type} [Fintype ι] [Fintype τ]{f g:Fish (ι⊕τ)→ℝ}{p:ι⊕τ→Site c}
private lemma gambit(f:Fish (ι⊕τ)→ℝ)(m:Fish ι→Fish τ)(s:ℝ)(x:Fish ι)(k:ι)(L:Finset τ)(hm:DifferentiableAt ℝ m x)(hp:DifferentiableAt ℝ f (meetVar (s • x) (m x)))(hw:∀ i, i∉ L→ glance m k x i=0):
 glance (fun y=> f (meetVar (s•y) (m y))) k x=s*glance f (.inl k) (meetVar (s•x) (m x))+∑ i∈L, glance f (.inr i) (meetVar (s•x) (m x)) *glance m k x i:=by
 let V:=s • ContinuousLinearMap.id ℝ (Fish ι); let U:=fderiv ℝ m x; let A:=Uniform.bolt k; let M:=meetVar (s•x) (m x); let H:=fderiv ℝ f M
 have hz := hp.hasFDerivAt.comp x ((Uniform.partSpace ι τ).symm.hasFDerivAt.comp x (V.hasFDerivAt.prodMk hm.hasFDerivAt)); unfold glance arrow; erw [hz.fderiv]; change H (meetVar (s•A) (U A))= s*H (bolt _) + ∑ i∈L,H (bolt _) *U A i -- tune
 have he : meetVar (s•A) (U A)= s•bolt (.inl k)+ lowerCol (U A):=by ext e; cases e <;> simp [meetVar,Uniform.partSpace, A,lowerCol,Uniform.bolt,Pi.single_apply] -- tune
 rw [he,map_add,map_smul]; congr 1
 have hv(i:τ):lowerCol (ι:=ι) (bolt i)=bolt (.inr i):=by ext e; cases e<;> simp [lowerCol,Uniform.partSpace,Uniform.bolt,Pi.single_apply] -- tune
 nth_rw 1 [← Uniform.combine (U A)]
 rw [map_sum,map_sum]; simp_rw [map_smul,hv,smul_eq_mul]; rw [Finset.sum_subset (s₁:=L) (s₂:=Finset.univ) (Finset.subset_univ L) (f:=fun i=> _) ?_] -- orientation
 · simp_rw [mul_comm (U A _)]
 · intro i hi hy; rw [show U A i=0 from hw i hy]; ring
lemma glance_sub {x:E}{f g:E→ B}(hf:DifferentiableAt ℝ f x)(hg:DifferentiableAt ℝ g x)(e:E):arrow (fun y=> f y -g y) e x=arrow f e x-arrow g e x:=by unfold arrow; rw [fderiv_fun_sub hf hg]; rfl
lemma seenY {f:Fish ι→E}{x:Fish ι}(h:Allows (n+1) f x C)(i:ι):Allows n (glance f i) x C:=by
 let L:=ContinuousLinearMap.apply ℝ E (bolt i); refine ((h.slide.linear L ?_).mono (one_mul _).le)
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro g; rw [one_mul]; change ‖g (bolt i)‖ ≤ _; simpa using g.le_opNorm (bolt i)
def firmX(f:Fish (ι⊕τ)→E)(z:Fish ι→Fish τ)(s:ℝ)(y:Fish ι):=f (meetVar (s • y) (z y))
set_option maxHeartbeats 600000 in
lemma valve {ι τ:Type}[Fintype ι] [Fintype τ]{f g:Fish (ι⊕τ)→ℝ}{m z:Fish ι→Fish τ}{x:Fish ι}{a d t:ℝ}(i:ι)(L:Finset τ)
 (h:∀ y:Fish ι, ‖y‖<1→ Allows (n+1) m y (A*s)  ∧ Allows (n+1) z y (A*s) ∧ Slope f (meetVar (s•y) (z y))=0)
 (he:∀ y:Fish (ι⊕τ), ‖y‖<r→ DifferentiableAt ℝ f y∧DifferentiableAt ℝ g y∧∀ i, Allows (n+1) (glance f i) y a∧ Allows n (glance (g-f) i) y d) (hs:0 ≤ s)(ha:1 ≤ A)(hv:3*A*s<r)(hr: 3*A*s ≤ 1)
 (ht:‖x‖<1)(hb: Allows n (fun y=>m y-z y) x t)(hl:∀ y:Fish ι, ‖y‖<1→∀ j, j ∉ L → glance m i y j=0):
 let B:=composeCost n d 1+2^n*composeCost n a 1*t
 Allows n (glance ((firmX g m s)-(firmX f z s)) i) x (s*B+ L.card*(2^n* B*(A*s))):=by
 intro B; let hV(v:Fish ι→Fish τ)(y:Fish ι):= meetVar (s•y) (v y); let U:=hV m; let Z:=hV z
 have hu y(hy:‖y‖<1)(f:Fish ι→Fish τ)(h:Allows (n+1) f y (A*s)):Allows (n+1) (hV f) y (3*A*s):=by
    apply (turn_safe h h hs ha hy 0 (left_mem_Icc.mpr zero_le_one)).germ; filter_upwards with i; simp; rfl -- tune
 have hx y (hy:‖y‖<1):= he (U y) ((hu y hy _ (h _ hy).1).value.trans_lt hv); have hz y (hy:‖y‖<1) := he (Z y) ((hu _ hy _ (h _ hy).2.1).value.trans_lt hv)
 let D(i:ι⊕τ)(v:Fish ι):= glance g i (U v) - glance f i (Z v)
 have H(i:ι⊕τ): Allows n (D i) x B:=by
    have hm:= varying (n:=n) (f:=glance f i) (m:=m) (z:=z) (fun v hy=>(he v hy).2.2 _|>.1) ht (fun y hy=> ⟨((h y hy).1).order (by omega),(h y hy).2.1.order (by omega)⟩) hs ha hv hr hb
    apply ((((hx _ ht).2.2 _|>.2).comp (f:=U) (((hu _ ht _ (h _ ht).1).order (show n ≤ n+1 by omega)).mono hr)).add hm).germ
    filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with y (hy: y∈ball _ _)
    have hh:= hx _ (mem_ball_zero_iff.mp hy); change glance (g-f) i _ + _ = D _ _; unfold D; rw [show glance (g-f) i (U y)=glance g i (U y)-glance f i (U y) from glance_sub hh.2.1 hh.1 (bolt i)]
    change _-(glance f i (U y))+(glance f i (U y)-_) = _ ; abel
 let X(j:τ)(y:Fish ι):=D (.inr j) y * glance m i y j
 have hh(j:τ) : Allows n (X j) x (2^n*B*(A*s)):=by
    let Y:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : τ=>ℝ) j
    have hp': ‖Y‖ ≤ 1:=by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro t; rw [one_mul]; exact norm_le_pi_norm t j
    exact Neige.oneCost_r (H _) (((seenY (h _ ht).1 i).linear Y hp').mono (one_mul _).le)
 have hr := ((H (.inl i)).smul s).add (allows_sum (s:=L) (f:=X) (fun i _=> hh i)); rw [abs_of_nonneg hs] at hr; simp only [Finset.sum_const,nsmul_eq_mul] at hr
 apply hr.germ; filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with y (hy:y∈ball _ _)
 have hb': ‖y‖<1:=mem_ball_zero_iff.mp hy
 have hw:∀ j:τ,glance f (.inr j) (Z y)=0:=fun j=> by
    unfold glance arrow
    have H:= congrFun (h _ hb').2.2 j; simp only [Slope,Uniform.entry,iteratedFDeriv_one_apply] at H; exact H
 have hQ: glance (fun x=> f (Z x)) i y=s*glance f (.inl i) (Z y):=by
    rw [show (fun x=>f (Z x))=(fun x=>f (meetVar (s•x) (z x))) from rfl, gambit f _ _ _ _ Finset.univ ((h _ hb').2.1.smooth.differentiableAt (by norm_cast)) (hz _ hb').1 (by simp)]
    change _+∑ j, glance f (.inr j) (Z y) *_=_; simp_rw [hw]; simp only [zero_mul,Finset.sum_const_zero,add_zero]; rfl
 rw [show glance ((firmX g m s)-(firmX f z s)) i y=glance (firmX g m s) i y-glance (firmX f z s) i y from glance_sub (f:= _ ∘ U) (g:= _ ∘ Z) ((hx _ hb').2.1.comp _ ((hu y hb' _ (h _ hb').1).smooth.differentiableAt (by norm_cast))) ((hz _ hb').1.comp _ ((hu _ hb' _ (h _ hb').2.1).smooth.differentiableAt (by norm_cast))) _] -- tune
 rw [show glance (firmX g m s) i y =_ from gambit g _ s _ i L ((h _ hb').1.smooth.differentiableAt (by norm_cast)) (hx _ hb').2.1 (hl _ hb'), show glance (firmX f z s) i y= _ from hQ]
 unfold X D; simp_rw [hw,sub_zero]; change s*(glance g (.inl i) (U y)-_)+_=_; rw [mul_sub]; abel
end norm
end YM.CF.Hors
