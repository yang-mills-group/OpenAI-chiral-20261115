import GaugeFieldConstruction.LotTileJ
import YM.CF.Buffered.Duels
import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 72000
variable (i k:ℕ) {P' V: Side} {f r t v :ℕ}
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
local notation "X_" s:max=> RootBook Y i k s
local notation "µ" s:max=> city (Ω s)
variable {I J G:Type} [Fintype I] [Fintype J][LinearOrder I][LinearOrder J] [LinearOrder G]
variable (p:(Y.voyage i).kick≤ k)
local notation "ν"=> Y.uv k
local notation "θ"=> P.R.L
variable (w:I→G)(X: HousingJ Y i G)(K:G→Prop)(t:f ≤Y.uv k)(E: List I→Orbit (side Y i f)→ Phys (side Y i f))(A:I→Mark (side Y i (Y.uv k)))
variable {N:Side}
variable (σ:I→Seat (side Y i f))(R:I→I→ℂ)
variable (vP:κWork G (Seat (side Y i f)) w σ)
local notation "κ0"=> RevenueT Y i k
local notation "ƒ"=> convoy Y i k t
local notation "Gc"=> city (side Y i (Y.uv k))
variable (M:I→Mark (side Y i f))(F:List I)(qM:∀ j∈ F.toFinset,AtSupport false (X f (w j)) (M j))
variable (pU:Montana Y i k X f)(u:Entourage Y i k w X K t E A)
open Girt
local notation "Yτ"=> side Y i f
local notation "Ym"=> (Y.voyage i).CapeT f
abbrev slipListJ (F L:List I):=F.reverse.filter (·∈ (L.toFinset ∩ F.toFinset))
abbrev leaveListJ (F L:List I):=wingR L (L.toFinset ∩ F.toFinset)
def banquetJ (M:Mark (side Y i f))(H:Orbit (side Y i f)→ Phys (side Y i f))(x:Orbit (side Y i f)): Phys (side Y i f):= acts (M (drawn ((Y.voyage i).CapeT f) x)) (H x)
abbrev ΩBirthJ (L:List I):=banquetJ Y i (List.map M (slipListJ F L)).prod (E (leaveListJ F L)) -- binder macro 
set_option maxHeartbeats 190000 in
lemma oathJ (U:Mark (side Y i f))(H:Orbit (side Y i f)→Phys (side Y i f))(v:Envelope U)(r:Version (city _) H):Version (city _) (banquetJ Y i U H):=by
 let S:=(Y.voyage i).CapeT f; obtain ⟨F,u,v1⟩:=r
 refine ⟨banquetJ Y i U F,u.mono fun i e=> congrArg (acts (U (drawn S i))) e, kitE (fun i=>U (drawn S i)) F (fun Tt:FC (Single (side Y i f))=> (fun i=> acts Tt i)) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd) (Env.along v (drawn_m S ((Y.voyage i).ownership f).paid.bill)) v1⟩ -- q order
lemma merryP (W U:Mark (side Y i f))(H:Orbit (side Y i f)→Phys (side Y i f)) : markedRead W Ym (banquetJ Y i U H)= markedRead (W*U) Ym H:=by
 apply integral_congr_ae; filter_upwards with x; unfold banquetJ; rw [Pi.mul_apply,letterRead,letterRead]; simp only [ContinuousLinearMap.comp_apply,act_mul]; first| rfl| done
-- order
local notation "F0"=> F.toFinset
variable (vF:F.Nodup)
lemma slipEJ (L:List I): (slipListJ F L).toFinset=L.toFinset∩ F0:=by ext i; simp [slipListJ]
lemma slip_J (L:List I)(h:L.Nodup): F.Nodup → (slipListJ F L).Perm (Roots.wingX L F0):=by
 intro p; apply List.perm_of_nodup_nodup_toFinset_eq ((show F.reverse.Nodup from (by simpa using p)).filter _) ((wing_sub ..).nodup h); rw[slipEJ]; ext; simp only[List.mem_toFinset,Roots.wingX,List.mem_filter,decide_eq_true_eq,Finset.mem_inter,List.mem_toFinset]
lemma Leave_l (L:List I): leaveListJ F L=wingR L F0:= List.filter_congr fun i v=> by simp [v]
include qM u
private abbrev PackList(L:List I):=AtJO w (slipListJ F L)
lemma Herita (l:List I)(v:galaJ w l): Version (city _) (ΩBirthJ Y i E M F l) :=by -- w arg unused
 have h:(slipListJ F l).toFinset⊆F.toFinset:= by rw [slipEJ]; exact inter_subset_right
 have g:galaJ w (leaveListJ F l):= List.Pairwise.sublist ((wing_sub _ _).map w) v
 refine oathJ Y i _ _ (tileList Y i w X F.toFinset M qM (slipListJ F l) h (AtJO w (slipListJ F l)) (Finset.Subset.refl _)).env (u.lease _ g)
omit qM u
lemma rosterCut (L:List I)(h:galaJ w L): let l:= Roots.wingX L F0; let k:= Roots.wingR L F0; Disjoint (AtJO w l) (AtJO w k)∧ AtJO w l ⊆ AtJO w L∧ AtJO w k⊆ AtJO w L:=by
 intro S Q; have hp {G0:List I}(p:G0.Sublist L): AtJO w G0⊆ AtJO w L:= fun _ e=> List.mem_toFinset.mpr ((p.map w).subset (List.mem_toFinset.mp e))
 have ht:(L.map w).Nodup:=List.Pairwise.imp (fun x=>ne_of_lt x) h
 refine ⟨?_,hp (wing_sub ..),hp (wing_sub ..)⟩; apply Finset.disjoint_left.mpr; intro x p t
 obtain ⟨i,a,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp p); obtain ⟨j,b,w⟩:= List.mem_map.mp (List.mem_toFinset.mp t)
 obtain ⟨v,g⟩:=List.mem_filter.mp a; obtain ⟨v',e⟩:=List.mem_filter.mp b
 have he:=List.inj_on_of_nodup_map ht v' v w -- tune
 exact (Finset.mem_compl.mp (of_decide_eq_true e)) (he.symm ▸ of_decide_eq_true g)
include qM u p pU t
variable (aK:FarLedge K w)
local notation "Mχ"=> convoy Y i k t∘ M
abbrev BornMarkJ := pepperJ F.toFinset A (convoy Y i k t∘ M)
include aK vF
lemma Warm_J : Entourage Y i k w X K t (ΩBirthJ Y i E M F) (BornMarkJ Y i k t A M F) :=by -- w arg
 have q_B:=u.stamped
 refine ⟨⟨fun j=>?_,fun j v=>?_⟩, fun l v=>Herita Y i k w X K t E A M F qM u l v,?_⟩
 · by_cases h:j∈ F.toFinset
   · rw [BornMarkJ,pepperJ,if_pos h]; exact PostSupport.of ((plot_U Y i k p w X t F.toFinset M qM pU j h).mono (subset_univ _))
   rw[BornMarkJ,pepperJ,if_neg h]; exact q_B.owns _
 · by_cases h:j∈ F.toFinset
   · rw [BornMarkJ,pepperJ,if_pos h]; exact PostSupport.of (plot_U Y i k p w X t F.toFinset M qM pU j h)
   rw[BornMarkJ,pepperJ,if_neg h]; exact q_B.slit _ v
 intro l v C W h
 obtain ⟨pC,bC⟩:=h
 let L:= slipListJ F l; let t':= PackList w F l; let T: Finset G:= AtJO w L; let Y₀:= (List.map M L).prod; let U0:= convoy Y i k t (W*Y₀)
 obtain ⟨v₀,v₁,v₂⟩:= rosterCut w F l v
 have pB:(l.map w).Nodup:=List.Pairwise.imp (fun x=> ne_of_lt x) v
 have he:L.Perm (Roots.wingX l F0):=slip_J F l (List.Nodup.of_map w pB) vF
 have hu:T= AtJO w (Roots.wingX l F0):=by ext; simp only[T,AtJO,List.mem_toFinset,(he.map w).mem_iff]
 let lB:= Roots.wingR l F0; have hr:L.toFinset⊆ F0:=by unfold L; rw[slipEJ]; exact inter_subset_right
 have hL:= tileList Y i w X F0 M qM _ hr T (Finset.Subset.refl _); have pq: Disjoint C T:=Disjoint.mono_right (show T⊆AtJO w l from (hu.symm ▸ v₁)) pC -- tune orientation
 have hh:galaJ w lB:= List.Pairwise.sublist ((wing_sub _ _).map w) v
 have hv:(L.map w).Nodup:=(he.map w).nodup_iff.mpr (((wing_sub _ _).map w).nodup pB)
 have hW: nearJ Y i w X (C∪ T) f lB (W*Y₀):=by
    constructor
    · rw [disjoint_union_left,hu]; exact ⟨Disjoint.mono_right v₂ pC,v₀⟩ -- union of LinTS.
    exact (bC.mono (tile0J Y i X _ _ subset_union_left)).mulM (hL.mono (tile0J Y i X _ _ subset_union_right))
 unfold ΩBirthJ; rw[merryP,Leave_l]
 change markedRead (W*Y₀) Ym (E lB)= _; rw[u.fare _ hh _ (W*Y₀) hW,turnU Y i k p X C pU W bC t le_rfl T _ pq hL,show convoy Y i k t Y₀= (List.map Mχ L).prod from altarList Y i k p w X t F0 M qM pU L hr hv, stone_Z Y i k p w X t F0 M qM pU _ L hr he hv]; unfold BornMarkJ; rw [returnJ_list Y i k p w X K t A F0 M qM pU q_B aK l v,mul_assoc]
#print axioms Warm_J
#check ΩBirthJ
#check BornMarkJ
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
