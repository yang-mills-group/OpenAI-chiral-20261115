import YM.CF.Vol.Vertical
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
lemma capZ(f':Config G f→ Config G c→ E) [FiniteDimensional ℝ E] (T:Tube G S)(k:S.Choices)(s:Signed) (F:Forest S.ratio):
 let g(v):= f' ((pull s 0 ∘ (UP G c f)) v) ((pull s 0 ∘ (VQ G c f)) v)
 let h(v:Ark T F):=f' (Jazz T k s v) (Jade T k s v)
 ContDiffAt ℝ n g 0 → cFoot n g → cFoot n h:=by
 intro g h hp hc; obtain ⟨hx,hH⟩:= plumbs (T:=T) (F:=F) k s; let L:=windowH T F; have hg:h =ᶠ[𝓝 0] g ∘ L:=hx.mono fun i hi=> congr_arg₂ f' hi (congr_fun hH i)
 apply fun i hi=> ((hg.iteratedFDeriv ℝ i).eq_of_nhds).trans ((ride_eps hp L ?_ (snap_Q) hc).1 i hi)
 let Y: Ark T F →L[ℝ] Work.F03.ChartVars F G:= ((tint G _).prodCongr (tint G _)).toContinuousLinearMap
 apply ContDiffAt.of_le (n:=ω) _ le_top
 apply (show ContDiffAt ℝ ω (Work.F03.inclusion F) (Y 0) by rw [map_zero]; exact inclusion_smooth F).comp (f:=Y) _ Y.contDiff.contDiffAt
lemma bore(U:ℝ→ G.El)(h:U 0=1){v:G.Color}(hp:HasDerivAt (fun t=>G.mat (U t)) (G.colorMat v) 0):Tendsto (fun t:ℝ=> (t^2)⁻¹ • sore G (U t)) (𝓝[≠] 0) (𝓝 0):=by
 have he:Tendsto (fun t:ℝ=> t⁻¹ • G.curvature (U t)) (𝓝[≠] 0) (𝓝 v):=by simpa only [zero_add,h,G.curvature_unit,sub_zero] using hasDerivAt_iff_tendsto_slope_zero.mp (curvature_of_hasDerivAt hp)
 have hz:= (price_limit h hp).sub ((he.norm.pow 2).div_const 2); rw [sub_self] at hz; apply hz.congr; intro t; unfold sore; rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,smul_eq_mul]; ring
lemma yore(f:E → G.El)(x:ℝ)(hp:∀ v:E,f 0=1 ∧ ∃ g:G.Color, HasDerivAt (fun t:ℝ=> G.mat (f (t • v))) (G.colorMat g) 0)(h:ContDiffAt ℝ ω (fun y=> x*sore G (f y)) 0): cFoot 3 (fun y=> x*sore G (f y)):=by
 apply nextF (m:=2) (h.of_le le_top); intro v; obtain ⟨h0,g,hV⟩:=hp v; have hL:= (bore _ (show f ((0:ℝ) • v)=1 from (congr_arg f (zero_smul ℝ v)).trans h0) hV).const_mul x; rw [mul_zero] at hL; exact hL.congr (fun t=>by simp only [smul_eq_mul]; ring)
lemma vehicles(T:Tube G S)(F:Forest S.ratio)(h:K.Funds S T)(k:S.Choices)(s:Signed)(r:ℕ):
 let U:=pull s 0 ∘ UP G c f; let V:= pull s 0 ∘ VQ G c f; let X: Ark T F → Config G f:= Jazz T k s; let Z: Ark T F → Config G c:=Jade T k s
 Marble n T U V k r 0 C → (∀ i,cFoot 3 (fun y=>KissP (X y) T i))∧(∀ i,cFoot 3 (fun y=>KissQ (Z y) T i))∧(∀ i,cFoot 3 (fun y=>KissI (X y) (Z y) k i)):=by
 intro U V X Z ht; have he(x:LogsP G c f)(t:ℝ) : U (t • x)=represent (t • Bid.pulled x.2 s) ∧ V (t • x)=represent (t • Bid.pulled x.1 s):= ⟨represent_pulled ..,represent_pulled ..⟩
 have hy : U 0=1 ∧ V 0=1:=by
    obtain ⟨hx,hy⟩:=he 0 0; simp only [zero_smul,link_one] at *; exact ⟨hx,hy⟩
 have hp:S.patch.Branches S.kernel G:= funds_branch h
 constructor
 · intro i; apply capZ (fun U _=> KissP U T i) T k s F ((ht.S i).analytic.of_le le_top); apply yore (f:=fun x=>faceValue (U x) i) _ _ (ht.S i).analytic; intro y; refine ⟨?_,faceCurl i (Bid.pulled y.2 s),?_⟩
   · change faceValue (U 0) i=1; rw [hy.1]; exact (by have he:=stroll_zero (G:=G) (square i.2.val.1 i.2.val.2) (i.1); rw [link_one] at he; exact he)
   simp_rw [(he y _).1]; exact face_deriv ..
 constructor
 · intro i; apply capZ (fun _ V=> KissQ V T i) T k s F ((ht.Q i).analytic.of_le le_top); apply yore (f:=fun x=>faceValue (V x) i) _ _ (ht.Q i).analytic; intro y; refine ⟨?_,faceCurl i (Bid.pulled y.1 s),?_⟩
   · rw [hy.2]; exact (by have he:=stroll_zero (G:=G) (square i.2.val.1 i.2.val.2) (i.1); rw [link_one] at he; exact he)
   simp_rw [(he y _).2]; exact face_deriv ..
 intro i; apply capZ (fun U V=>KissI U V k i) T k s F ((ht.I i).analytic.of_le le_top); apply yore (f:=fun x=> tideX S k (V x) (U x) i) _ _ (ht.I i).analytic; intro y; let a:= Bid.pulled y.1 s; let b:= Bid.pulled y.2 s; have hz : tideX S k (1:Config G c) 1 i=1:=by unfold tideX; simp [settled S hp i k]
 refine ⟨hy.1.symm ▸ hy.2.symm ▸ hz,a (i.1,coord i.2) - Bid.bills S b (i.1,coord i.2),?_⟩; simp_rw [(he y _).1,(he y _).2, tideX,G.mat_mul,G.mat_inv]
 have hm : HasDerivAt (fun v : ℝ=>G.mat (S.prediction (represent (v • b)) k i)) (G.colorMat (Bid.bills S b (i.1,coord i.2))) 0:= prices S hp i k b
 convert! (represent_rate a i).mul hm.star using 1; simp [Gauge.colorMat_skew,settled S hp i k,sub_eq_add_neg]
end YM.CF.Vol
