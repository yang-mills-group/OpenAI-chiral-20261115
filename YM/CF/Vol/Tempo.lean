import YM.CF.Vol.Lithe
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations
abbrev LogsP(G:Gauge)(c f:Side):= Bid.Dir G c×Bid.Dir G f
abbrev UP(G:Gauge)(c f:Side)(x:LogsP G c f):= represent x.2
abbrev VQ(G:Gauge)(c f:Side)(x:LogsP G c f):= represent x.1
lemma repB(G:Gauge)(n:ℕ) : ∃ C:ℝ, ‖(1:G.Mat)‖ ≤ C ∧∀{c:Side}, Uniform.Inputs (@represent c G) n C:=by -- Args
 obtain ⟨Z,hZ,hH⟩:= Rel.storms G n
 exact ⟨max Z ‖(1:G.Mat)‖,le_max_right ..,fun {c} => ⟨link_one,(norm_nonneg _).trans (le_max_right ..),fun i x hx=>(hH _ hx i).mono (le_max_left ..)⟩⟩
lemma onC {W:E → Config G c}(L:B →L[ℝ] E)(h:‖L‖≤1)(p:Uniform.Inputs W n C): Uniform.Inputs (W ∘ L) n (Uniform.composeCost n C 1):=by
 obtain ⟨hL,hC,H⟩:=p; refine ⟨by rw [Function.comp_apply,map_zero,hL], by unfold Uniform.composeCost; positivity,fun i x hx=>?_⟩
 have hp:‖L x‖≤1:= (L.le_opNorm x).trans (mul_le_one₀ h (norm_nonneg _) hx); exact (H _ _ hp).comp (f:=L) (allows_linear h hp)
lemma pose_s {W:E → Config G c}(p:Uniform.Inputs W n C)(s:Signed): Uniform.Inputs (pull s 0 ∘ W) n C:=by
 obtain ⟨hv,hC,H⟩:=p; refine ⟨by rw [Function.comp_apply,hv]; funext i; cases i; simp [pull,Step.read],hC,fun e x hx=>?_⟩ -- tune
 let i:=(StepData.sendBonds s 0) e; have hh:= H i x hx; unfold Function.comp pull Step.read; split; next hv=> exact hh.inverse (f:=fun z=>W z i)
 exact hh
lemma Inputs.raises {U:E → Config G c}(p:Uniform.Inputs U n C)(h:C ≤ D):Uniform.Inputs U n D:=⟨p.1,p.2.1.trans h,fun i v hv=>(p.2.2 i v hv).mono h⟩
def Jazz(T:Tube G S)(k:S.Choices)(s:Signed)(x:Mast G c×Fish (Key F G)):= pull s 0 (Uniform.fine G F (meetVar x.1 x.2))
def Jade(T:Tube G S)(k:S.Choices)(s:Signed)(x:Mast G c×Fish (Key F G)):= pull s 0 (facadeX G x.1)
set_option maxHeartbeats 650000 in
lemma drawn (K:Teller G)(P:Patch)(n:ℕ)(hn:3 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind n)(p:P.Branches K.bind G): ∃ C ε:ℝ,0<C ∧0<ε∧∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), K.Funds S T → S.patch=P→∀ s:Signed,∀ k:S.Choices, ∀ r, (∀ x:LogsP G c f, ‖x‖<ε → Marble n T (pull s 0 ∘ UP G c f) (pull s 0 ∘ VQ G c f) k r x C) ∧ (∀ x:Mast G c× Fish (Key F G), ‖x‖< ε → Marble n T (Jazz T k s) (Jade T k s) k r x C):=by
 obtain ⟨Z,hZ,hT⟩:= repB G (n+1); obtain ⟨D,hD⟩:=paint_supply G (n+1)
 let U:=Uniform.composeCost (n+1) (fineCost G (n+1) D) 1; let Q:=Uniform.composeCost (n+1) (outerCost G (n+1) D) 1; let V:= Uniform.composeCost (n+1) Z 1; let H:=max (max Z V) (max U Q); have he: ‖(1:G.Mat)‖ ≤ H:=hZ.trans ((le_max_left ..).trans (le_max_left ..))
 obtain ⟨M,ε,hM,hε,h',hC⟩:= bags K P n hn W p H ((norm_nonneg _).trans he); have hW:=hD; obtain ⟨N,hN,hF⟩:=drops K P.L n H M (show PaintSupply G n D from ⟨hW.1,fun _ hx=> (hW.2 _ hx).order (by omega)⟩) he
 refine ⟨N,ε,hN,hε,fun {c f} S T F H' h t k r=>?_⟩
 have hx {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E](U:E → Config G f)(V:E → Config G c)(p:Uniform.Inputs U (n+1) H)(he:Uniform.Inputs V (n+1) H) x (hy:‖x‖<ε):= hF S T H' (by rw [h]) U V x k (hC S T H' h k U V p he x hy) r
 let C:= (Uniform.partSpace (Primary c G) (Key F G)).symm.toContinuousLinearMap -- tune
 constructor
 · intro x hy
   have hp : Uniform.Inputs (UP G c f) (n+1) H := Inputs.raises (onC (ContinuousLinearMap.snd ℝ (Bid.Dir G c) (Bid.Dir G f)) (ContinuousLinearMap.norm_snd_le ..) hT) ((le_max_right Z V).trans (le_max_left ..))
   have hu : Uniform.Inputs (VQ G c f) (n+1) H := Inputs.raises (onC (ContinuousLinearMap.fst ℝ (Bid.Dir G c) (Bid.Dir G f)) (ContinuousLinearMap.norm_fst_le ..) hT) ((le_max_right Z V).trans (le_max_left ..))
   exact hx _ _ (pose_s hp t) (pose_s hu t) x hy
 intro x hy; have he(x:Mast G c×Fish (Key F G)):Jade (F:=F) T k t x = pull t 0 (outer G F ((partSpace ..).symm x)):=by cases x; rfl
 rw [show Jade (F:=F) T k t=pull t 0 ∘ (outer G F ∘ C) from funext he]; exact hx _ _ (pose_s (Inputs.raises (onC C meets_n (fine_supply F hD)) ((le_max_left U Q).trans (le_max_right ..))) t) (pose_s (Inputs.raises (onC C meets_n (outer_supply F hD)) ((le_max_right U Q).trans (le_max_right ..))) t) x hy
end YM.CF.Vol
