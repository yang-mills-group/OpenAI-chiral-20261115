import GaugeFieldConstruction.LusterR
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
variable {I:Type}[Fintype I][DecidableEq I]{cost:ℕ→P.Test→ℂ}(C: ∀ j:Axis, Porch P cost j)
abbrev DiagramR (I:Type):= I→Axis→ℝ
abbrev PolesR (L:List I):Prop:= L.Nodup ∧ ∀ i:I,i∈ L
abbrev SpreadS_R (j:Axis)(x:I→Axis→ℝ)(L:List I):Prop:= PolesR L ∧ L.Pairwise (fun i k=> x i j < x k j)
abbrev VplaneR (I:Type)(j:Axis): Set (I→Axis→ℝ):={x | Injective fun i=>x i j}
abbrev MasksR (I:Type): Set (I→Axis→ℝ):={x | ∀ j:Axis,x∈ VplaneR I j}
abbrev CardsR (I:Type): Set (I→Axis→ℝ):=⋃ j:Axis,VplaneR I j
lemma char_R {x:I→Axis→ℝ}{L:List I}{j:Axis}(p:SpreadS_R j x L) : x∈ VplaneR I j:=by
 intro i k eq
 have h: (L.map (fun i=> x i j)).Nodup:= List.Pairwise.imp (fun x=>ne_of_lt x) (List.pairwise_map.mpr p.2)
 exact List.inj_on_of_nodup_map h (p.1.2 i) (p.1.2 k) eq -- tune
lemma vplane_w {x:I→Axis→ℝ}{j:Axis}(q:x∈ VplaneR I j):∃ L:List I,SpreadS_R j x L:=by
 let r:I→I→Prop:= fun i k=>x i j ≤ x k j
 letI : DecidableRel r:= Classical.decRel _
 haveI : Std.Total r:= ⟨fun i k=> le_total ..⟩
 haveI : IsTrans I r:= ⟨fun _ _ _ m=> le_trans m⟩
 haveI : Std.Antisymm r:=⟨fun _ _ h e=> q (h.antisymm e)⟩ -- tune
 let L:= univ.sort r
 have hx: PolesR L:=⟨sort_nodup _ _,fun i=> by simp [L]⟩
 refine ⟨L,hx,?_⟩; have hp: L.Pairwise r:= pairwise_sort _ r
 generalize hx0 : L=L' at hp hx ⊢; clear hx0; have v:= hx.1; clear hx; induction L' with
 | nil=> exact List.Pairwise.nil
 | cons i L ih=>
    rw [List.pairwise_cons] at hp ⊢
    obtain ⟨m,k⟩:= List.nodup_cons.mp v
    exact ⟨fun k g=> lt_of_le_of_ne (hp.1 k g) (fun h=>m ((q h).symm ▸ g)),ih (hp.2) k⟩
lemma poles_permR {l L:List I}(p:PolesR l)(q:PolesR L) : l.Perm L:= (List.perm_ext_iff_of_nodup p.1 q.1).2 (fun i =>iff_of_true (p.2 _) (q.2 _))
lemma OpenRollR {L:List I} {x:DiagramR I} {j:Axis}{σ:I→PermWallJ P}(p:x∈OpenR j σ L) : L.Pairwise (fun i k=>x i j<x k j):=by
 refine (show RollBestR _ _ from p).imp (fun {i k} h=> lt_trans ?_ (lt_trans h ?_)) -- tune implicit elements args
 · exact lt_add_of_pos_right _ (σ _).2
 exact sub_lt_self _ (σ _).2
abbrev AutoPadR (P:Spine)(t:ℕ):PermWallJ P:=⟨P.stampPin t (WorkWJ P t), PledgeJ P t⟩
lemma OpenPatR (L:List I)(x:I→ Axis→ℝ)(P:Spine)(j:Axis)(h:L.Pairwise (fun i k=>x i j< x k j)) : ∀ᶠ t:ℕ in atTop,x∈OpenR j (fun _:I=>AutoPadR P t) L:=by
 induction L with
 | nil=> exact Eventually.of_forall (fun i=> List.Pairwise.nil)
 | cons i L ih=>
   obtain ⟨g,u⟩:= List.pairwise_cons.mp h
   have hv(k:I) :∀ᶠ v in atTop,k∈L→x i j+StallJ P (AutoPadR P v)< x k j-StallJ P (AutoPadR P v):=by
     by_cases a:k∈L; swap; · exact Eventually.of_forall fun i e=>(a e).elim
     simp_rw [show k∈L from a,forall_true_left]; let h:  x i j+0 < x k j-0:=by simpa using g k a
     have hp : Tendsto (fun t=>StallJ P (AutoPadR P t)) atTop (𝓝 0):=SecondEraJ P
     have hv:= (tendsto_const_nhds (x:=x i j)).add hp; have hw:=(tendsto_const_nhds (x:=x k j)).sub hp
     filter_upwards [(hw.sub hv).eventually (lt_mem_nhds (sub_pos.mpr h))] with t e; exact sub_pos.mp e -- tune
   filter_upwards[eventually_all.mpr hv,ih u] with r h q; exact List.pairwise_cons.mpr ⟨h,q⟩
lemma OpenTollR (P:Spine){x:I→Axis→ℝ}{j:Axis}(e:x∈VplaneR I j) :∃ (L:List I)(σ:I→PermWallJ P), PolesR L∧x∈ OpenR j σ L:=by
 obtain ⟨L,h,p⟩:= vplane_w e; obtain ⟨t,v⟩:= (OpenPatR L x P j p).exists; exact ⟨L,_,h,v⟩
lemma Opens_R (j:Axis)(σ:I→PermWallJ P)(L:List I): IsOpen (OpenR j σ L):=by rw[←on_rR σ (P.publicH j) (fun _=>0)]; exact smooth_highway ..
lemma terrain_R (I:Type)[Finite I](j:Axis) : IsOpen (VplaneR I j):=by
 have hv : VplaneR I j= ⋂ (i:I)(k:I)(_ : i≠k), {x:I→Axis→ ℝ | x i j≠ x k j}:=by ext x; simp [VplaneR, injective_iff_pairwise_ne,Pairwise] -- tune
 rw [hv]; apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro k; apply isOpen_iInter_of_finite; intro p; exact isOpen_ne_fun (by fun_prop) (by fun_prop)
lemma prosc_R (I:Type)[Finite I] : IsOpen (CardsR I) := isOpen_iUnion (terrain_R I)
lemma ply_openR (I:Type)[Finite I] : IsOpen (MasksR I):=by rw[show MasksR I= ⋂ j,VplaneR I j from (by ext x; simp[MasksR])]; exact isOpen_iInter_of_finite (terrain_R I) -- tune
private abbrev PicketR (P:Spine){I:Type}(x:I→Axis→ℝ):Prop:=∃ (j:Axis)(L:List I)(σ:I→PermWallJ P), PolesR L∧ x∈ OpenR j σ L
def SπR (S:I→ScreensJ P) (x: I → Axis→ℝ): ℂ:=
 if g:PicketR P x then let j:=g.choose; let L:=g.choose_spec.choose; let σ:= g.choose_spec.choose_spec.choose; (StageR σ (C j) (BodyΘ P S j σ)).reading L x else 0
variable (L:List I)(S:I→ScreensJ P)(p:∀ i,AttainedR 0 (S i))
lemma perim_R {x:I→Axis→ℝ}(h:x∉ CardsR I) : SπR C S x=0:=by
 apply dif_neg; rintro ⟨j,t,σ,g,u⟩; exact h (Set.mem_iUnion.mpr ⟨j,char_R (And.intro g (OpenRollR u))⟩)
include p
lemma ηTenderR (j:Axis)(σ:I→PermWallJ P)(x:I→Axis→ℝ)(p':PolesR L)(u:x∈ OpenR j σ L): SπR C S x= (StageR σ (C j) (BodyΘ P S j σ)).reading L x:=by
 have e:PicketR P x:= ⟨j,L,σ,p',u⟩; unfold SπR; rw[dif_pos e]; obtain ⟨g,v⟩:=e.choose_spec.choose_spec.choose_spec
 exact Shore_R C S p _ _ _ _ _ _ (poles_permR g p') g.1 ⟨v,u⟩
lemma groundPlotR : ContinuousOn (SπR C S) (CardsR I):=by
 intro x h; obtain ⟨i,t⟩:= Set.mem_iUnion.mp h; obtain ⟨L,σ,p',u⟩:=OpenTollR P t
 let A:= StageR σ (C i) (BodyΘ P S i σ); apply ContinuousAt.continuousWithinAt
 refine (A.repertoire_cont L).continuousAt.congr ?_; exact Eventually.mono ((Opens_R i σ L).mem_nhds u) (fun i' m=> (ηTenderR C L S p i σ i' p' m).symm) -- tune
lemma PlotBillR (j:Axis)(σ:I→PermWallJ P)(x:I→P.VMark)(p': PolesR L)(u:AskR P x∈OpenR j σ L)(v:AskR P x∈ MasksR I): SπR C S (AskR P x)= (StageR σ (C j) (BodyΘ P S j σ)).ranking L x []:=by
 choose L' σ' s r using fun i:Axis=> OpenTollR P (v i)
 exact (ηTenderR C L S p j σ (AskR P x) p' u).trans ( Billing_R C S p j σ L x L' σ' (fun i=>poles_permR p' (s i)) p'.1 u r)
#print axioms PlotBillR
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
