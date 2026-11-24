import YM.CF.Vol.March
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented
abbrev Pot(T:StepData c f)(G:Gauge):Type:= Mast G c × Directions G f
def horseA(T:StepData c f)(G:Gauge)(x:Pot T G):=facadeX G x.1
def hoop(T:StepData c f)(G:Gauge)(s:Signed)(x:Pot T G):= facade T s (horseA T G x) x.2
lemma postU(p:PaintSupply G n D) : ∃ M, 0<M∧∀ {c f:Side}(S:StepData c f),Uniform.Inputs (horseA S G) n M∧∀ s:Signed,Uniform.Inputs (hoop S G s) n M:=by
 let T:= shade G; let C:= Uniform.composeCost n D T; let M:= Uniform.composeCost n C 1
 let X := M+ ‖(1:G.Mat)‖; let Y:= 2^n*C*X; let A:=max 1 (max Y M); refine ⟨A,zero_lt_one.trans_le (le_max_left ..),fun {c f} S=>?_⟩
 have ht: 1 ≤ T:=shade_one G; have hc:0<C:=by unfold C Uniform.composeCost; have he:=p.1; positivity
 have hp:0≤ M:=by unfold M Uniform.composeCost; positivity
 let F:=facadeX (c:=c) G; have he:Uniform.Inputs F n C:=by
    refine ⟨by simp [F,facadeX],hc.le,fun i x hx => ?_⟩
    let U:= hull G c; let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Bond c=>G.Color) i; let B:=L.comp U
    have hL:‖B‖ ≤ T:= ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans ht) fun i=> (norm_le_pi_norm (U i) _).trans ((U.le_opNorm i).trans (mul_le_mul_of_nonneg_right hull_n (norm_nonneg _))) -- tune
    have hB: ‖B x‖ ≤ T:= (B.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hL)
    simp_rw [F,facadeX,increment,Pi.one_apply,mul_one]; exact (p.2 _ hB).comp (f:=B) (allows_linear hL hB)
 have hh:Uniform.Inputs (horseA S G) n M:= onC (ContinuousLinearMap.fst ℝ (Mast G c) (Directions G f)) (ContinuousLinearMap.norm_fst_le ..) he
 refine ⟨Inputs.raises hh ((le_max_right ..).trans (le_max_right ..)),fun s=>?_⟩
 let K(y:Pot S G):= increment (replica S.ratio (horseA S G y)) y.2; have hX: ‖(1:G.Mat)‖ ≤ X:=le_add_of_nonneg_left hp
 apply pose_s (W:=K) _ s; refine Inputs.raises (C:=Y) ?_ ((le_max_left ..).trans (le_max_right ..)); refine ⟨by simp only [K,hh.1,Prod.snd_zero,replica_one]; funext i; simp [increment],by unfold Y X; positivity,fun i x hx=>?_⟩ -- tune global
 let f(y:Pot S G):=replica S.ratio (horseA S G y) i; have hv:Allows n (fun y=> G.mat (f y)) x X:=by unfold f replica; split; exact allows_const _ hX; exact (hh.2.2 _ _ hx).mono (le_add_of_nonneg_right (norm_nonneg _)) -- tune
 let L: Pot S G →L[ℝ] G.Color:= (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (Mast G c) _)
 have hL:‖L‖≤ T:=ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans ht) fun j=> ((norm_le_pi_norm j.2 i).trans (norm_snd_le _)).trans (le_mul_of_one_le_left (norm_nonneg _) ht)
 have hY:‖L x‖≤ T:= (L.le_opNorm x).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans hL)
 exact (((p.2 _ hY).comp (f:=L) (allows_linear hL hY)).times hv)
-- generic bzoom derivatives at (x.1,0). return SPHER component Allows at x in both vars. derivative only increments U. eventually license globally. Hess noise.
def bzoom(g:E×B→X) [NormedAddCommGroup X][NormedSpace ℝ X](x:E×B):X:= arrow (fun y=>g (x.1,y)) x.2 0
variable [NormedAddCommGroup X][NormedSpace ℝ X]
lemma depart{g:E× B→ X}(x:E× B)(h:DifferentiableAt ℝ g (x.1,0)):bzoom g x = arrow g (0,x.2) (x.1,0):=by
 unfold bzoom arrow
 let f(y:B):E× B:= (x.1,y); have he: HasFDerivAt f (ContinuousLinearMap.inr ℝ E B) 0:= by exact (hasFDerivAt_const (x:= (0:B)) x.1).prodMk (hasFDerivAt_id _)
 change (fderiv ℝ (g ∘ f) 0) x.2= _; rw [(h.hasFDerivAt.comp (f:=f) 0 he).fderiv]; rfl
lemma clnk {g:E×B→ X}(x:E× B)(hx:‖x‖≤1)(h:Allows (n+1) g (x.1,0) C): Allows n (bzoom g) x (2^n*Uniform.composeCost n C 1):=by
 let L₁: E×B →L[ℝ] E×B:= (ContinuousLinearMap.inl ℝ E B).comp (ContinuousLinearMap.fst ℝ E B); let L₂: E× B →L[ℝ] E× B:= (ContinuousLinearMap.inr ℝ E B).comp (ContinuousLinearMap.snd ℝ E B)
 have hP:‖L₁‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; change max ‖v.1‖ ‖(0:B)‖≤ _; exact max_le (norm_fst_le _) (by simp)
 have hL:‖L₂‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v=> by rw [one_mul]; change max ‖(0:E)‖ ‖v.2‖ ≤ _; exact max_le (by simp) (norm_snd_le _)
 have ht(L: E × B →L[ℝ] E × B)(h:‖L‖≤1): Allows n L x 1:=allows_linear h ((L.le_opNorm x).trans (mul_le_one₀ h (norm_nonneg _) hx)); have he:Allows n (fderiv ℝ g) (x.1,0) C:= ⟨h.analytic.fderiv_right (by simp),fun j hj=>by rw [norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (by omega)⟩
 have hh := ((he.comp (f:=L₁) (ht _ hP)).bilinear (ContinuousLinearMap.apply ℝ X|>.flip) (ht _ hL) (cling (E×B) X)); rw [mul_one,mul_one] at hh
 let U(y:E×B):=g (L₁ y)
 have hr : bzoom g =ᶠ[𝓝 x] fun y=> fderiv ℝ g (L₁ y) (L₂ y):= by
    filter_upwards [(L₁.continuous.tendsto x).eventually (h.analytic.eventually (by simp))] with y hy; exact depart y (hy.differentiableAt (by simp))
 exact ⟨hh.analytic.congr_of_eventuallyEq hr, fun j hj=> by rw [(hr.iteratedFDeriv ℝ j).eq_of_nhds]; exact hh.norm_le j hj⟩
end YM.CF.Vol
