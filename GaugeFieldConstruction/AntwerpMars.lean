import GaugeFieldConstruction.AmberPoleMars
import GaugeFieldConstruction.NorkPackMars
import GaugeFieldConstruction.StyriaRel.YM.Euclid.Pairing
import Mathlib.Analysis.Complex.Liouville
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
open SignetS
variable {cost:ℕ→P.Test→ℂ}(C:∀ j:Axis, Porch P cost j) {j:Axis}
variable {n m:ℕ}(L:List (Fin n))(W:List (Fin m))(σ:Fin n→ PermWallJ P)(τ:Fin m→PermWallJ P)
open NSF.Table.Pairing
variable (S: Fin n→ ScreensJ P)(F: Fin m→ ScreensJ P)(R: Fin n→ScreensJ P)
variable (x:Points n)(y: Points m)
local notation "xz"=> ΦplanR n x
local notation "yz"=> ΦplanR m y
abbrev terrasEMars (j:Axis) (x:Points n): DiagramR (Fin n):= ΦplanR n x -- tune
abbrev TripLMars (L:List (Fin n))(W:List (Fin m)):= L.reverse.map (Fin.castAdd m) ++ W.map (Fin.natAdd n)
lemma PolesLMars (l:PolesR L)(w:PolesR W): PolesR (TripLMars L W):=by
 unfold TripLMars; let i:=Fin.castAdd m (n:=n)
 have e(a:Fin n)(b:Fin m): Fin.castAdd m a ≠ Fin.natAdd n b:= ne_of_lt (show Fin.castAdd m a < Fin.natAdd n b from (show a.val < n+b.val from lt_of_lt_of_le a.2 (Nat.le_add_right ..))) -- tune
 refine ⟨List.nodup_append.mpr ⟨(List.nodup_reverse.mpr l.1).map ?_,w.1.map ?_,?_⟩,?_⟩
 · intro a b h; have q:= congrArg Fin.val h; exact Fin.ext q
 · intro a b h; apply Fin.ext; have q:= congrArg Fin.val h; exact Nat.add_left_cancel (show n+a.val=n+b.val from q)
 · intro i t x s v; obtain ⟨a,_,rfl⟩:=List.mem_map.mp t; obtain ⟨b,_,rfl⟩:=List.mem_map.mp s; exact e a b v
 intro i; refine Fin.addCases (fun i=>List.mem_append_left _ (List.mem_map_of_mem ?_)) (fun i=> List.mem_append_right _ (List.mem_map_of_mem ?_)) i <;> simp [l.2,w.2] -- tune
-- appointments
abbrev TimeShelfMars (x:Points n)(j:Axis):= x∈ {z | Function.Injective fun i=>z i j}∧ NSF.Points.allAbove j 0 x
structure StallLeadMars (j:Axis)(x:Points n)(P:Spine) where
 L : List (Fin n)
 σ : Fin n→PermWallJ P
 pol : PolesR L
 pays : ΦplanR n x∈ OpenR j σ L
 toll : ∀ i,0<x i j-StallJ P (σ i)
lemma AppointsMars (j:Axis)(x:Points n)(v: TimeShelfMars x j)(P:Spine): Nonempty (StallLeadMars j x P):=by
 obtain ⟨L,p,q⟩:=vplane_w (show ΦplanR n x∈ VplaneR (Fin n) j from v.1)
 let t:= AutoPadR P
 have he : ∀ᶠ r in atTop,∀ i,0<x i j-StallJ P (t r):=by
    apply eventually_all.mpr; intro i; have vt:Tendsto (fun r:ℕ=> StallJ P (t r)) atTop (𝓝 0):= SecondEraJ P; exact (vt.eventually (gt_mem_nhds (v.2 i))).mono fun r h=> sub_pos.mpr h
 obtain ⟨r,h,Q⟩:= (he.and (OpenPatR L (ΦplanR n x) P j q)).exists; exact ⟨L,_,p,Q,h⟩ -- Nonempty deconstruct tune
lemma enterRightMars (a:Axis)(i:Fin m): ΦplanR (n+m) (closedUp a x y) (Fin.natAdd n i)= ΦplanR m y i:=congrArg WithLp.ofLp (leave ..)
lemma enterLeftMars (a:Axis)(i:Fin n): ΦplanR (n+m) (closedUp a x y) (Fin.castAdd m i)= flipTactMars a (ΦplanR n x i):=by
 unfold ΦplanR; funext k; unfold flipTactMars; by_cases p:k=a
 · subst k; rw[Function.update_self]; change _=_; simp [NSF.Table.Pairing.ride] -- tune
 rw [Function.update_of_ne p]; simp [NSF.Table.Pairing.ride,p]
variable (A:StallLeadMars j x P)(B:StallLeadMars j y P)
abbrev queueActMars (b:Axis)(x:Points n)(s:StallLeadMars b x P)(S: Fin n→ ScreensJ P):= billActMars (C b) s.σ (BodyΘ P S b s.σ) (ΦplanR n x) s.L
lemma ForwardReadyMars : AheadActorMars (0:ℝ) (queueActMars C j x A S) :=by
 rintro i h; obtain ⟨k,g,rfl⟩:= List.mem_map.mp h; exact (A.toll k).le
lemma OrderedReadyMars: OrderActorMars (queueActMars C j x A S):=by
 apply List.pairwise_map.mpr; exact (show RollBestR _ _ from A.pays).imp (fun k=> k.le)
lemma WidthReadyMars (k:VignMars (C j).DegreeHab)(h:k∈queueActMars C j x A S): k.lo ≤ k.hi:=by
 obtain ⟨k,hk,rfl⟩:=List.mem_map.mp h; exact le_trans (sub_le_self _ (A.σ _).2.le) (le_add_of_nonneg_right (A.σ _).2.le)
lemma TerraceOpensMars : ΦplanR _ (closedUp j x y) ∈ OpenR j (Fin.append A.σ B.σ) (TripLMars A.L B.L):=by
 let M:=ΦplanR _ (closedUp j x y); let σ:=Fin.append A.σ B.σ; let p:=A.pays; let q:=B.pays
 apply List.pairwise_append.mpr; refine ⟨List.pairwise_map.mpr (List.pairwise_reverse.mpr ?_),List.pairwise_map.mpr ?_,?_⟩
 · apply (show RollBestR _ _ from p).imp; intro a b h; rw [enterLeftMars,enterLeftMars, Fin.append_left, Fin.append_left, flipTactMars,Function.update_self, flipTactMars, Function.update_self]; linarith
 · apply (show RollBestR _ _ from q).imp; intro a b h; rw[enterRightMars, enterRightMars,Fin.append_right,Fin.append_right]; exact h
 intro i h k g; obtain ⟨a,ha,rfl⟩:=List.mem_map.mp h; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp g
 rw[enterRightMars,enterLeftMars,Fin.append_right,Fin.append_left,flipTactMars,Function.update_self]; let H:= A.toll a; let V:= B.toll b
 change - x a j+_ < y b j- _; linarith
variable (hS: ∀ (i:Fin n)(σ: PermWallJ P), R i j σ σ=Star.star (S i j σ σ))
local notation "Dξ"=> TripLMars A.L B.L
include hS
lemma TerraceBookedMars (T:Fin (n+m)→ScreensJ P)(h:T=Fin.append R F): let U:= Fin.append A.σ B.σ; let v:=ΦplanR _ (closedUp j x y)
    billActMars (C j) U (BodyΘ P T j U) v (TripLMars A.L B.L)=(queueActMars C j x A S).reverse.map ReflectActorMars ++ queueActMars C j y B F :=by
 subst T; dsimp only; unfold TripLMars queueActMars billActMars BodyΘ; rw [List.map_append,List.map_map,List.map_map,←List.map_reverse,List.map_map] -- reverse tune
 congr 2
 · funext i; simp only [Function.comp_apply,Fin.append_left,enterLeftMars,hS, LoopActMars]
 · funext i; simp only [Function.comp_apply,Fin.append_right,enterRightMars]
omit hS
def ChargeEntryMars {j:Axis}(C: Porch P cost j){x:Points n}(A:StallLeadMars j x P)(S: Fin n→ ScreensJ P): C.DegreeHab:= ActorMars C.BrightHab C.groundHab (some 0) (billActMars C A.σ (BodyΘ P S j A.σ) (ΦplanR n x) A.L)
include hS
lemma BookingActMars (v:∀ i,AttainedR 0 (R i))(e:∀ i,AttainedR 0 (F i)) : inner ℂ (ChargeEntryMars (C j) A S) (ChargeEntryMars (C j) B F)=SπR C (Fin.append R F) (ΦplanR _ (closedUp j x y)):=by
 let U:=Fin.append R F; let u:= Fin.append A.σ B.σ; let t:=ΦplanR _ (closedUp j x y); let L:=TripLMars A.L B.L; have he(i:Fin (n+m)): AttainedR 0 (U i):=by
    refine Fin.addCases ?_ ?_ i
    · intro k; simpa [U] using v k
    intro k; simpa [U] using e k
 rw [ηTenderR C L U he j u t (PolesLMars A.L B.L A.pol B.pol) (TerraceOpensMars x y A B), EarningActorMars]
 rw [TerraceBookedMars C S F R x y A B hS U rfl, FoldActorMars (C j).BrightHab _ (SpireHTMars (C j)) _ _ 0 (ForwardReadyMars C S x A) (by rw [neg_zero]; exact ForwardReadyMars C F y B) (OrderedReadyMars C S x A) (WidthReadyMars C S x A), neg_zero]; rfl -- tune
#print axioms BookingActMars
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
