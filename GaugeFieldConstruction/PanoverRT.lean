import GaugeFieldConstruction.GatewoodRT
/-!
 # w=s(real) at partial Heights y. Express boundary simultaneously for arbitrary compact Test exterior as limit of spatial projection episodes. NO testing Heaviside. Monotone strip perturb extr.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface NSF.Work.C20 Metric
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)(g:Bool)
local notation "Nτ"=> τNearRT k
noncomputable abbrev PoleIogRt : Points (n+1)≃ₗᵢ[ℝ] Points (n+1):= if g then (Nτ).switch else (LinearIsometryEquiv.refl ℝ _)
noncomputable def αpayXRt (g:Bool)(ε:ℝ):ℝ:= if g then ε else -ε
noncomputable def DewierXRt (ε:ℝ): Points (n+1):= PoleIogRt k g (addMeterRT k (position 0 (αpayXRt g ε),dawn (αVertRT k y)))
noncomputable def LuaιXRt (ε s:ℝ)(x:Points n): ZSideRt n:=(⟨s,αpayXRt g ε⟩, ΘOculusRt k y x)
lemma dewTintRt (ε s:ℝ)(x:Points n)(u:Space3): QchIRt k g (LuaιXRt k y g ε s x) u=glow ((PoleIogRt k g) (κMoverRT k (position u s,x))) (DewierXRt k y g ε):=by
 cases g
 · rw[χBornRT]; simp only[LuaιXRt, ΘOculusRt,re_glow,im_glow,PoleIogRt,DewierXRt,Bool.false_eq_true,↓reduceIte]; rfl -- tune
 rw[χTiltBornRT]; simp only[LuaιXRt, ΘOculusRt,re_glow,im_glow,DewierXRt,PoleIogRt,↓reduceIte]
lemma dewierPRt (ε s:ℝ)(p:0<ε)(x:Points n): (LuaιXRt k y g ε s x).1∈ HalfRT g:=by cases g <;>simp [LuaιXRt,HalfRT,αpayXRt,p]
lemma ContLuaRt:Continuous (fun z:ℝ × (ℝ × Points n)=> LuaιXRt k y g z.1 z.2.1 z.2.2):=by
 have h:Continuous fun z:ℝ×(ℝ × Points n) => αpayXRt g z.1:=by cases g<;> simp [αpayXRt] <;>fun_prop
 refine Continuous.prodMk ?_ ((continuous_iff_continuousAt.2 (fun x=>(ΘArchARt k y x).continuousAt)).comp (continuous_snd.comp continuous_snd))
 exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_fst.comp continuous_snd).prodMk h) -- tune
include v
lemma dewVisitTRt: Tendsto (DewierXRt k y g) (𝓝[>] (0:ℝ)) (𝓝[fields (n+1)] ((PoleIogRt k g) (dawn y))):=by
 have h: DewierXRt k y g 0= (PoleIogRt k g) (dawn y):=by unfold DewierXRt; rw [show αpayXRt g 0=0 from by cases g<;>simp [αpayXRt]]; congr 1; exact κDawnRT k y v -- tune
 have he(ε:ℝ): DewierXRt k y g ε=shade (QchIRt k g (LuaιXRt k y g ε 0 0) 0):=by rw [dewTintRt,im_glow]
 have ht:Continuous fun ε:ℝ=> LuaιXRt k y g ε 0 0:= (ContLuaRt k y g).comp (continuous_id.prodMk (continuous_const (y:=((0:ℝ),(0:Points n)))))
 have hc:Continuous (DewierXRt k y g):=by rw[funext he]; exact (cont_sh _).comp ((χTintRt k g).comp (ht.prodMk continuous_const))
 refine tendsto_nhdsWithin_iff.2 ⟨?_,?_⟩
 · rw [← h]; exact (hc.tendsto _).mono_left nhdsWithin_le_nhds
 have hα:LuaιXRt k y g 0 0 0=(0,ΘOculusRt k y 0):=by cases g<;>simp [LuaιXRt,αpayXRt] <;>try rfl
 have he':= roomXRt k 0 y v g; change ∀ᶠ w:ℂ × Full n in 𝓝 (0,ΘOculusRt k y 0),_ at he'; rw [← hα] at he'
 filter_upwards [self_mem_nhdsWithin,((((ht.tendsto 0).mono_left (nhdsWithin_le_nhds (s:= Ioi 0))).eventually he'))] with ε h hz; rw [he]; exact hz (dewierPRt k y g _ _ h _) _ -- tune
omit v
abbrev PlateTRt (n:ℕ):= ℝ × Points n
noncomputable def ΧJoyTRt (q:Space3 × PlateTRt n): Points (n+1):= PoleIogRt k g (κMoverRT k (position q.1 q.2.1, q.2.2))
noncomputable def ΕmotionRt: Space3 × PlateTRt n ≃ₜ Points (n+1):= ((Homeomorph.prodAssoc Space3 ℝ (Points n)).symm.trans (divide.symm.toHomeomorph.prodCongr (Homeomorph.refl _))).trans ((κMoverRT k).toHomeomorph.trans (PoleIogRt k g).toHomeomorph)
lemma JoyStreamRt : ΧJoyTRt k g= ΕmotionRt k g:= rfl
lemma StreamPresRt:MeasurePreserving (ΕmotionRt k g) volume volume:=by
 have h:MeasurePreserving divide.symm.toHomeomorph:= (MeasurePreserving.symm (divide.toHomeomorph.toMeasurableEquiv) volume_divide)
 have he: MeasurePreserving (Homeomorph.prodAssoc Space3 ℝ (Points n)).symm volume volume:= by exact MeasurePreserving.symm _ (measurePreserving_prodAssoc ..)
 exact ((PoleIogRt k g).measurePreserving).comp ((measureIRt k).comp ((h.prod (@MeasurePreserving.id (Points n) _ volume)).comp he))
noncomputable def MoonTestRt (d:Joint (n+1)):= Probe.along (PoleIogRt k g).symm.toContinuousLinearEquiv d
lemma MoonJoyRt (q:Space3 ×PlateTRt n)(b:Test4)(f:Joint n): MoonTestRt k g (χTestRT k b f) (ΧJoyTRt k g q) = b (position q.1 q.2.1)* f q.2.2:=by simp only [MoonTestRt,along_at]; change χTestRT k b f ((PoleIogRt k g).symm ((PoleIogRt k g) _))=_; rw [LinearIsometryEquiv.symm_apply_apply,priceIRT]
variable {G:Gauge}{L:Register G}{S:Table L}{Y:Surface S}{D:∀ i, Blanket i}{F:Waves S}{N:Y.Aurora D}
variable (P:N.FullBody F)(m:(D (n+1)).Modified)
variable (T:Axis→Axis→ S.Union)(V:Fin n→S.Union)(a:Axis)
local notation "Ct"=> CabinTRt k (TxRT k T V a timeAxis) g
variable (B:ContDiffBump (0:ℝ))(f:ContDiffBump (0:Space3))(τ:Joint n)
noncomputable abbrev MoχRt (b:Axis):= MoonTestRt k g (χTestRT k (αWarmRt B f b) τ)
local notation "τM"=> MoχRt k g B f τ timeAxis
noncomputable abbrev PenCostRt (p:PlateTRt n):ℂ:= (shutterXRt B p.1:ℝ)*τ p.2
noncomputable abbrev ΡioPaymentRT (ε:ℝ)(z:PlateTRt n):= PenCostRt B τ z * PanProjRT (X:=N) k T V a (φInXRt f) timeAxis g (LuaιXRt k y g ε z.1 z.2)
lemma RioPayRt(q:Space3 × PlateTRt n)(ε:ℝ): N.emit (Ct) (glow (ΕmotionRt k g q) (DewierXRt k y g ε)) * (τM) (ΕmotionRt k g q)= PenCostRt B τ q.2*(φInXRt f q.1 * TapCoreRt (X:=N) k T V a g (LuaιXRt k y g ε q.2.1 q.2.2) timeAxis q.1):=by
 unfold TapCoreRt OriΛTRt; rw [Function.comp_apply,dewTintRt]; rw[show ΕmotionRt k g q=ΧJoyTRt k g q from rfl]; rw [MoonJoyRt]; unfold ΧJoyTRt; rw [αWarmRt,if_pos rfl]; change _*((((shutterXRt B (time _) * f (spatial _)):ℝ):ℂ)*_)=PenCostRt _ _ _*(((f q.1:ℝ):ℂ)*N.emit _ (glow _ _)); rw [time_position,spatial_position]; unfold PenCostRt; push_cast; ring
include P m v
lemma cashTRt: Tendsto (fun ε=>∫ z:PlateTRt n, ΡioPaymentRT (N:=N) k y g T V a B f τ ε z) (𝓝[>] (0:ℝ)) (𝓝 (partialXRT (B:=D) (Y:=Y) (CabinTRt k (TxRT k T V a timeAxis) g) ((PoleIogRt k g) (dawn y)) ((MoχRt k g B f τ) timeAxis))):=by
 have he := dewVisitTRt k y v g; have ht:(PoleIogRt k g (dawn y))∈ shores (n+1):=by rw [show PoleIogRt k g (dawn y)=dawn y from by cases g; rfl; exact heightTieRT k y v]; exact v.here
 refine ((N.sees P (Ct) _ ht m (τM)).comp he).congr' ?_
 filter_upwards [he.eventually self_mem_nhdsWithin] with ε hε
 let L(x:Points (n+1)):= N.emit (Ct) (glow x (DewierXRt k y g ε))*(τM) x; let E:= ΕmotionRt k g
 have h:Integrable (L ∘ E):= ((StreamPresRt k g).integrable_comp_emb E.measurableEmbedding).2 (P.leaned _ _ _ hε _)
 change (∫ x,L x)=_; rw[← (StreamPresRt k g).integral_comp E.measurableEmbedding L]; change (∫ x, (L ∘ E) x)=_
 refine (integral_prod_symm _ h).trans ?_; apply integral_congr_ae; filter_upwards with s; simp only [Function.comp_apply]; unfold ΡioPaymentRT PanProjRT; rw[← integral_const_mul]; apply integral_congr_ae; exact Eventually.of_forall fun u=> RioPayRt k y g T V a B f τ (u,s) ε
#print axioms cashTRt
end YM.NSF.Boundary
end
