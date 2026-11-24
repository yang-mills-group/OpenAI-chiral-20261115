import GaugeFieldConstruction.ToutK
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
namespace Lave
open Trackℓ Fables
variable (p: BudgetPoint)(h:ℝ)
abbrev VerdK(x:Cover)(V:Genre)(F:Paper n): Payν n:= (x,V,F)
def HomΓ (t:Genre)(q:Floor)(p: Waves): Prop:= t.Room p ∧ match q with
 | .three=> t=.pure ∧p.2=0
 | .four=> t≠.mixed∧ p.1=0∧ p.2.2=0
 | .five=> p.1=0∧p.2.1=0
def aptC : Floor→ℕ | .three => 3 | .four=> 4 | .five => 5
abbrev excess (q:Floor)(p:Genre):= aptC q-BaseD p
lemma aura (t:Genre)(q:Floor)(p:Waves)(e:HomΓ t q p): BaseD t+ excess q t=aptC q:=by
 have he:=e.2; cases q <;> cases t <;> try rfl
 all_goals simp at he
-- z authorization.C. univariate.W dress Sans S.Θ.
lemma spPure(x:Cover)(F:Paper n)(r i w:ℕ): sigΨ (VerdK x .pure F) (r,i,w) = if w=0 then κfΛ (PHale x (MastP x F) r i) else 0:=by
 let f:= MastP x F; have hp(p:ArcK x)(b t):eF x (Wry x p) b t= Rift x b t p:=rfl
 by_cases h:w=0
 · subst w; rw [if_pos rfl]; unfold sigΨ; rw [PHale,map_sum]; apply sum_congr rfl; intro t _; rw [map_smul]
   rcases t with ⟨a,b⟩; change (_:ℂ) • (_:Book)= _; change SipF n x F a b • αF (eF x (Wry x a) false r) (eF x (Wry x b) true i)= _; try rfl
 rw [if_neg h]; unfold sigΨ; apply sum_eq_zero; intro m _; change (_:ℂ) • (_:Book)=0; rw [show σU _ _ _=0 from ?_,smul_zero]; change (if w=0 then (αF _ _) else 0)=0; exact if_neg h -- tune
lemma sigG (x:Cover)(F:Paper n)(r i w:ℕ): sigΨ (VerdK x .gauge F) (r,i,w)=if w=0 then κgΛ (alignG x F r i) else 0:=by
 unfold sigΨ; by_cases h:w=0
 · subst w; rw [if_pos rfl,alignG,map_sum]; apply sum_congr rfl; intro i _; rw [map_smul]; try rfl
 rw [if_neg h]; apply sum_eq_zero; intro m _; change (_:ℂ) • (_:Book)=0; rw [show σU _ _ _=0 from ?_,smul_zero]; change (if w=0 then (αG _ _) else 0)=0; exact if_neg h -- tune
lemma sigH(x:Cover)(F:Paper n)(r i w:ℕ):sigΨ (VerdK x .mixed F) (r,i,w)=κmΛ (MesaP x F r i w):=by
 unfold sigΨ; -- Fin type.#
 let V:=VerdK x .mixed F
 change (∑ i':ArcK x×ArcK x × StampSet n x, _ • σU x (apices V i') (r,i,w))= _; rw [Fintype.sum_prod_type]; unfold MesaP; simp only [map_sum κmΛ, map_smul κmΛ]; apply sum_congr rfl; intro j _; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro z _; apply sum_congr rfl; intro a _; try rfl
private lemma Boot_0 : statW 6 0={(0,0,0)}:=by ext ⟨i,j,k⟩; simp [statW,LaneB,cN]; omega
private lemma Boot_1 : statW 6 1={(0,0,1),(0,1,0),(1,0,0)}:= by ext ⟨i,j,k⟩; simp [statW,LaneB,cN]; omega
private lemma Boot_2 : statW 6 2={(0,0,2),(0,1,1),(1,0,1),(1,1,0),(0,2,0),(2,0,0)}:= by ext ⟨i,j,k⟩; simp [statW,LaneB,cN]; omega
lemma Wick_0 (V:Payν n): CrestJ 6 V 0=sigΨ V (0,0,0):=by rw [CrestJ,Boot_0,sum_singleton]
lemma Wick_1 (V:Payν n) : CrestJ 6 V 1=sigΨ V (0,0,1)+(sigΨ V (0,1,0)+sigΨ V (1,0,0)):=by rw [CrestJ,Boot_1]; simp
lemma Wick_2 (V:Payν n): CrestJ 6 V 2=sigΨ V (0,0,2)+(sigΨ V (0,1,1)+(sigΨ V (1,0,1)+(sigΨ V (1,1,0)+(sigΨ V (0,2,0)+ sigΨ V (2,0,0))))):=by rw [CrestJ,Boot_2]; simp -- tune
abbrev Aurora (d:Floor)(P: Payν n)(p:Genre)(w:Waves):Prop:=CrestJ 6 P (excess d p)=dress (SpineM w) ∧∀ k< excess d p,CrestJ 6 P k=0
abbrev Bid (P: Paper n)(o:Cover)(t:Genre):Payν n:= VerdK o t (t.coinB p h • P)
private lemma ΦBiz (X:Waves):(Phys.dress (SpineM X)).2.2.1=lineup (offP X):=by rw [dressF]; exact level_y X
private lemma FBiz (X:Waves):(Phys.dress (SpineM X)).2.1=graph_g (μG (bF4 X)+μD (bF5 X)):=by rw [dressG,level_x]
private lemma xBiz (X:Waves):(Phys.dress (SpineM X)).2.2.2=graph_x (task_M (bm5 X)):=by rw [dressX, level_w]
private lemma pBiz (X:Waves): (Phys.dress (SpineM X)).1=0:=rfl
private lemma LΘ (p:Book)(s:ℂ)(g:Cauchy.J GaugePair)(u:Cauchy.J Spair)(v:Cauchy.J Trip)(z:p.1=s)(q:p.2.1=g)(c:p.2.2.1=u)(w:p.2.2.2=v):p=(s,g,u,v):= Prod.ext z (Prod.ext q (Prod.ext c w))
private lemma reel_m (X:Waves):
 dress (SpineM X)=(0,graph_g (μG (bF4 X)+μD (bF5 X)), lineup (offP X), graph_x (task_M (bm5 X))):=by
 exact LΘ _ _ _ _ _ (pBiz X) (FBiz X) (ΦBiz X) (xBiz X)

private lemma f_nP(X:Waves)(h:chartF X=(0,0,0)): lineup (offP X)=0:=by
 have he: offP X=0:= Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Prod.ext (Subtype.ext (congrArg (fun X:PalOne=> X.2.1) h)) (Subtype.ext (congrArg (fun X:PalOne=> X.2.2.val) h)))
 rw [he,map_zero]
private lemma g_nP (X:Waves)(h:(bF4 X).val=0)(u:bF5 X=0): graph_g (μG (bF4 X)+μD (bF5 X))=0:=by have hp:bF4 X=0:=Subtype.ext h; rw [hp,u,map_zero,map_zero,add_zero,map_zero]
private lemma x_nP(X:Waves)(h:(bm5 X).val=0): graph_x (task_M (bm5 X))=0:=by have he:bm5 X=0:=Subtype.ext h; rw [he,map_zero,map_zero]
lemma GrainG {X:Waves}(e:Genre.gauge.Room X): dress (SpineM X)= κgΛ (graph_g (μG (bF4 X)+μD (bF5 X))):=by rw [reel_m,x_nP X e.2,f_nP X e.1]; try rfl
lemma GrainF {X:Waves}(e:Genre.pure.Room X): dress (SpineM X)=κfΛ (lineup (offP X)):=by rw [reel_m,g_nP X e.1 e.2.1, x_nP X e.2.2]; try rfl
lemma GrainX {X:Waves}(e:Genre.mixed.Room X): dress (SpineM X)=κmΛ (graph_x (task_M (bm5 X))):=by rw [reel_m,g_nP X e.1 e.2.1, f_nP X e.2.2]; try rfl

end Lave
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
