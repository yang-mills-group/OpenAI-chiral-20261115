import GaugeFieldConstruction.Sculpt
import GaugeFieldConstruction.Moulin
/-! Jet geometry: chart pressure near arbitrary link and left derivative. -/
set_option autoImplicit false
set_option maxHeartbeats 160000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
variable {E F D:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup D][NormedSpace ℝ D] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
variable (U:Config G n){L:Config G n→F}{A B:Directions G n}
abbrev solo(u:ℝ)(A:Config G n) (i:Directions G n):= increment A (u • i)
def sliders (U V:Config G n): Directions G n := fun i=> G.plog (G.mat (V i*(U i)⁻¹))
lemma con_t (t:ℝ) : Continuous (solo t U):= continuous_pi fun i=> by unfold solo increment; fun_prop
lemma placeL : sliders U U =0:=by ext i; simp [sliders]
lemma carry_t : ContinuousAt (sliders U) U:=by
 refine continuousAt_pi.mpr fun i=>?_
 let F(V:Config G n):= V i*(U i)⁻¹; have he:F U=1:=mul_inv_cancel _
 exact (show ContinuousAt G.plog (G.mat (F U)) from (by rw [he,G.mat_one]; exact G.plog_diff.continuousAt)).comp (g:=_) (f:=fun x=> G.mat (F x)) ((G.continuous_mat.comp (show Continuous F from (continuous_apply i).mul continuous_const)).continuousAt)
lemma portQ : ∀ᶠ V in 𝓝 U,increment U (sliders U V)=V:=by
 suffices h: ∀ i, ∀ᶠ V in 𝓝 U, increment U (sliders U V) i=V i by
    filter_upwards [eventually_all.mpr h] with V p; exact funext p
 intro i; let F(V:Config G n):= V i*(U i)⁻¹; have he:F U=1:=mul_inv_cancel _
 filter_upwards [((show Tendsto F (𝓝 U) (𝓝 1) from he ▸ ((continuous_apply i).mul continuous_const|>.continuousAt.tendsto : Tendsto F (𝓝 U) (𝓝 (F U)))).eventually G.plog_right)] with V h
 change G.lieExp (G.plog (G.mat (F V)))*U i=_; rw [h]; exact inv_mul_cancel_right (V i) _ -- name
lemma lively (p:ContinuousAt (L ∘ increment U) 0): ContinuousAt L U:=by
 have hh:=p.tendsto; rw [show (L∘ increment U) 0=L U from (by simp)] at hh
 exact (hh.comp (placeL U ▸ (carry_t U).tendsto : Tendsto (sliders U) (𝓝 U) (𝓝 0))).congr' ((portQ U).mono (fun V v=> congrArg L v))
-- combinatorial residents
abbrev engageS (n:Side)(G:Gauge)(i:tandem G n):= sliders (1:Config G n) (increment (increment 1 i.1) i.2)
lemma engage_ten (i:tandem G n)(e:Edge (Site n)): engageS n G i e=G.plog (G.mat (G.lieExp (i.2 e)*G.lieExp (i.1 e))):=by simp [engageS,sliders,increment]
lemma engage1 : engageS n G 0=0:=by unfold engageS; simp [placeL]
lemma engage_w : ContDiffAt ℝ ω (engageS n G) 0:=by
 refine contDiffAt_pi.mpr fun i=>?_; simp_rw [engage_ten]; let J(x:tandem G n):=G.mat (G.lieExp (x.2 i)*G.lieExp (x.1 i)); have hh:J 0=1:=by simp [J]
 exact (show ContDiffAt ℝ ω _ (J 0) from hh.symm ▸ G.plog_diff).comp _ ((((G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_snd)).mul (G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp contDiff_fst))): ContDiff ℝ ω J).contDiffAt)
lemma engage_H : βten 1 U=ᶠ[𝓝 0] increment U ∘ engageS n G:=by
 suffices he: ∀ i,∀ᶠ x in 𝓝 0,βten 1 U x i=increment U (engageS n G x) i by
    filter_upwards [eventually_all.mpr he] with x hx; exact funext hx
 intro i; let P(x:tandem G n):= G.lieExp (x.2 i)*G.lieExp (x.1 i); have hh:P 0=1:=by simp [P]
 filter_upwards [(show Tendsto P (𝓝 0) (𝓝 1) from (by rw [←hh]; exact (show Continuous P from (by unfold P; fun_prop)).continuousAt.tendsto)).eventually G.plog_right] with x h
 unfold βten; simp only [increment, engage_ten,one_smul]; rw [show G.lieExp _=P x from h,mul_assoc]
lemma engage_I(i: Fin 2):let L:=![ContinuousLinearMap.inl ℝ (Directions G n) (Directions G n), ContinuousLinearMap.inr ℝ (Directions G n) (Directions G n)] i
 engageS n G ∘ L =ᶠ[𝓝 0] id:=by
 intro L; let v:=engageS n G ∘ L
 suffices h:∀ e,∀ᶠ x in 𝓝 0,v x e=x e by
    filter_upwards [eventually_all.mpr h] with x hx; exact funext hx
 intro e; filter_upwards [((continuous_apply e).continuousAt.tendsto|>.eventually (show ∀ᶠ a in 𝓝 ((0:Directions G n) e), G.plog (G.mat (G.lieExp a))=a from G.plog_left))] with x hx
 change engageS n G (L x) e=x e; rw [engage_ten]; fin_cases i <;> simpa [L] using hx
lemma engage_R (A B:Directions G n): fderiv ℝ (engageS n G) 0 (A,B)= A+B:=by
 have hp(i: Fin 2):= engage_I (n:=n) (G:=G) i; let Q:=engageS n G
 have hh(L:Directions G n→L[ℝ] tandem G n)(p:Q ∘ L =ᶠ[𝓝 0] id)(V: Directions G n): fderiv ℝ Q 0 (L V)= V:=by
     have hh:= p.fderiv_eq (𝕜:=ℝ); rw [fderiv_id,fderiv_comp _ (by rw [map_zero L]; exact engage_w.differentiableAt (by simp)) (L.differentiableAt),L.fderiv,L.map_zero] at hh
     exact DFunLike.congr_fun hh V
 let a:= ContinuousLinearMap.inl ℝ (Directions G n) (Directions G n); let b:=ContinuousLinearMap.inr ℝ (Directions G n) (Directions G n)
 rw [show (A,B)= a A + b B by simp [a,b],map_add,show fderiv ℝ _ _ (a A)= A from hh a (hp 0) _,show fderiv ℝ _ _ (b B)=B from hh b (hp 1) _]
lemma tariff_comp (f:E→F)(g:F→D)(z:E)(h:ContDiffAt ℝ ω f z)(u:ContDiffAt ℝ ω g (f z))(v:fderiv ℝ g (f z)=0)(i j:E): iteratedFDeriv ℝ 2 (g ∘ f) z ![i,j]= iteratedFDeriv ℝ 2 g (f z) ![fderiv ℝ f z i,fderiv ℝ f z j]:=by
 rw [iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; let H:=fderiv ℝ (g ∘ f); let G:=fderiv ℝ g; let J:=fderiv ℝ f; let Q(x):= G (f x) ∘L J x; have hp:H=ᶠ[𝓝 z] Q:=by
    filter_upwards [h.eventually (by simp),h.continuousAt.eventually (u.eventually (by simp))] with y hy uy; apply fderiv_comp _ (uy.differentiableAt (by simp)) (hy.differentiableAt (by simp)) -- ω.eventually? Ω ok
 have hs:= ((u.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)|>.hasFDerivAt.comp _ (h.differentiableAt (by simp)|>.hasFDerivAt)).clm_comp (((h.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)).hasFDerivAt)
 change fderiv ℝ H z i j=_; rw [hp.fderiv_eq (𝕜:=ℝ), show fderiv ℝ Q z=_ from hs.fderiv]; simp [v] -- tune
lemma engage_A(p:ContDiffAt ℝ ω (L ∘ increment U) 0) : ContDiffAt ℝ ω (L ∘ βten 1 U) 0:=((show ContDiffAt ℝ ω (L ∘ increment U) (engageS n G 0) from engage1.symm ▸ p).comp _ engage_w).congr_of_eventuallyEq ((engage_H U).fun_comp L)
lemma engage_D (p:ContDiffAt ℝ ω (L ∘ increment U) 0)(v:fderiv ℝ (L ∘ increment U) 0=0): iteratedFDeriv ℝ 2 (L ∘ βten 1 U) 0 ![(A,0),(0,B)]= iteratedFDeriv ℝ 2 (L ∘ increment U) 0 ![A,B]:=by
 rw [(((engage_H U).fun_comp L).iteratedFDeriv ℝ 2).eq_of_nhds]; change iteratedFDeriv ℝ 2 ((L ∘ increment U) ∘ engageS n G) 0 _=_; rw [tariff_comp _ _ _ engage_w (engage1.symm ▸ p) (engage1.symm ▸ v),engage_R,engage_R,engage1,add_zero,zero_add]
end Shield
end YM.CF.XGarden
end
