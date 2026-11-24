import GaugeFieldConstruction.BenguelaJ
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
section
-- Proof orientation & kernel estimators rely on SAME data at all Mesh walls. All approximants as Mark Page.
variable (x:P.VMark)
abbrev SlabR:= PermWallJ P
abbrev OnSaleR (x:P.VMark)(A:ScreensJ P)(M':ℕ→P.Test):Prop:=∀ (j:Axis)(σ τ:PermWallJ P),∃ F:ℕ→P.Slabs j,
 Tendsto F atTop (𝓝 (A j σ τ)) ∧ ∀ᶠ v in atTop, CallBoxJ x σ τ j (M' v) (F v) v
local notation "M"=> timeMesh P.par
local notation "δ"=>StallJ P
variable {F F':ScreensJ P}{m m':ℕ→P.Test}
lemma OnusR (P:Spine)(x:P.VMark): OnSaleR x (CandΛJ P) (fun _=>1):=fun j σ τ=> ⟨_, tendsto_const_nhds (x:=CandΛJ P j σ τ), Eventually.of_forall (UnitWallJ x σ τ j)⟩
lemma OnSaleR.adds (h:OnSaleR x F m)(p:OnSaleR x F' m') : OnSaleR x (F+F') (fun i=>m i+m' i):=by
 intro j σ τ; obtain ⟨a,h,t⟩:=h j σ τ; obtain ⟨b,p,w⟩:=p j σ τ; refine ⟨_,h.add p,?_⟩; exact (t.and w).mono (fun s h=> h.1.plus h.2)
lemma OnSaleR.scales (h:OnSaleR x F m)(z:ℂ) : OnSaleR x (z • F) (fun i=> z • m i):=by
 intro j σ τ; obtain ⟨a,h,t⟩:=h j σ τ; refine ⟨_,(tendsto_const_nhds (x:=z)).smul h,?_⟩; exact t.mono (fun s h=>h.scale z)
abbrev AttainedR (x:P.VMark)(F:ScreensJ P) := ∃ m:ℕ→P.Test, OnSaleR x F m
variable {θ: BandS→ℕ}{G:ℝ}{f0 s:ℕ}
variable (p:RosterJ P θ G f0) (B:SωJ θ)(M':JωL θ)
variable (R:Signed× Bool)(u:BandS) (L:finsJ)
variable (pu:Adept_T θ B M' G) (A:CalendarJ p B M') (T:LampHouseJ (θ:=θ) u)(D:P.Heritor) (V:LampΤJ p B M' x R u A T D.path)
include p pu
variable (y:FrameK (Fin (θ u)))(g:f0 ≤ s)
lemma ApuestasR: OnSaleR x (MeshΦ p B M' x R u pu A T D V g y) (fun n=> if h:s≤n then LaunchLJ B x R u L T D s n h y else 0):=by
 intro i a b
 refine ⟨_,ΦGateJ p B M' x R u pu L A T D V g a b i y,?_⟩; obtain ⟨t,h,t'⟩:=((farWallJ a b).and (eventually_ge_atTop f0)).exists; filter_upwards[eventually_ge_atTop t,eventually_ge_atTop s] with r hr hp; rw[dif_pos hp]; exact (SeroxJ p B M' x R u pu L A T D V t' g a b i r y hp hr h).1
lemma PanAuraR (h:F∈ Panmart p B M' x R u pu A T D V s g):AttainedR x F:=by
 obtain ⟨⟨z,c⟩,rfl⟩:=h; rw [kickΔ]; exact ⟨_,OnSaleR.adds x (ApuestasR x p B M' R u 0 pu A T D V z g) (OnSaleR.scales x (OnusR P x) c)⟩
omit p pu
end
abbrev KoR:= Axis→ℝ
variable {I:Type}
variable (p:I→PermWallJ P)
abbrev Xφ (v:I) : P.meshPin:= (p v).val
abbrev Xτ (v:I) : P.meshPin:= Xφ p v+ Xφ p v
local notation "δ" i:max=> StallJ P (p i)
variable {cost:ℕ→P.Test→ℂ} {j:Axis}(C: Porch P cost j)
def StageR (A:I→P.Slabs j):= C.elementals (Xφ p) (Xτ p) (fun i=> show 0<(δ i)+(δ i) from add_pos (p i).2 (p i).2) A
-- common pads equal both sides. Suffice for lifts.
variable (A:I→P.Slabs j)
local notation "Xs"=> StageR p C A
abbrev RollBestR (R:I→I→Prop)(L:List I):Prop:= L.Pairwise R -- avoid name
lemma highAndR (L:List I)(x:I → (Axis → ℝ)):
 x∈ (Xs).highway L ↔ RollBestR (fun i k=> x i j+StallJ P (p i)< x k j-StallJ P (p k)) L:=by
 let B (i:I):= x i j+StallJ P (p i); let D (i:I):=x i j-StallJ P (p i); let R':=(fun i k=>B i < D k)
 have h(i:I):(Xs).frontend (x i) i=D i:=rfl; have t(i:I):(Xs).endline (x i) i=B i:=by unfold B; change D i+((δ i)+(δ i))=_; unfold D; ring
 have g(i:I): D i < B i:=by have hx:0< StallJ P (p i):= (p i).2; dsimp only [D,B]; linarith
 suffices hs: ∀ b:Option ℝ,(Xs).Correct L (Pages true) x b ↔ (∀ i∈ L,∀ d:ℝ,b=some d → d< D i) ∧ L.Pairwise R' by
    change (Xs).Correct L _ x none↔ _; rw [hs]; exact ⟨fun e=> e.2, fun e=>⟨fun i p' _ f=>(nomatch f),e⟩⟩ -- tune
 intro b; induction L generalizing b with
 | nil=> simp [Correct]
 | cons i w ih=>
    rw[Correct,t,ih,List.pairwise_cons]
    refine ⟨fun ⟨d,hu,hv⟩=> ⟨fun k p z e=>?_,fun k p'=>hu k p' _ rfl,hv⟩,?_⟩
    · have ht: z < D i:=d _ e; rcases List.mem_cons.mp p with rfl|hk; exact ht; exact lt_trans ht ((g _).trans (hu k hk _ rfl))
    rintro ⟨ha,hq,hv⟩; refine ⟨fun d e=>ha i (List.mem_cons_self ..) _ e, fun a₀ hx d m=> (Option.some.inj m) ▸ (hq a₀ hx),hv⟩ -- orientation
local notation "π"=> P.meshPin
variable (l:List I)(u:I→P.VMark)
abbrev OpenR (j:Axis)(p:I→PermWallJ P)(l:List I) := {x:I→Axis→ℝ | RollBestR (fun i k=>x i j+StallJ P (p i)<x k j-StallJ P (p k)) l}
lemma on_rR : (Xs).highway l= OpenR j p l:=Set.ext (fun x=> highAndR p C A l x)
private lemma stage_glR {w:List I}(b:Option ℝ) : Continuous (fun A:I→P.Slabs j=> (StageR p C A).stageList w u ([]:List (Trans j)) b):=by
 induction w generalizing b with
 | nil=> exact continuous_const (X:=I → P.Slabs j) -- tune
 | cons i w ih=>
   let x:=u i; let O:= C.Time.E ((StageR p C (fun _=>0)).sep b i (clearAbove u i)); let V':= some ((StageR p C (fun _=>0)).endline (clearAbove u i) i); let F:=C.porchMove x; let Z:=C.porchMove (-x)
   have hc:Continuous C.ρ:=(show LipschitzWith 1 C.ρ from LipschitzWith.of_dist_le_mul fun a b=> by rw [dist_eq_norm,dist_eq_norm,←map_sub,NNReal.coe_one,one_mul]; exact C.watch_le _).continuous
   change Continuous (fun A:I→P.Slabs j=>O (F (C.ρ (A i) (Z ((StageR p C A).stageList w u [] V')))))
   exact O.continuous.comp (F.continuous.comp ((hc.comp (show Continuous (fun A:I → P.Slabs j=> A i) from continuous_apply _)).clm_apply (Z.continuous.comp (ih V'))))
lemma price_conR : Continuous (fun A:I→P.Slabs j=> (StageR p C A).ranking l u []) := continuous_const.inner (stage_glR p C u none)
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
