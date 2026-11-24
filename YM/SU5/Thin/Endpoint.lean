import SatinFixedContrastNovember4
import YM.SU5.Thin.Operators

set_option autoImplicit false
set_option maxHeartbeats 200000
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
open Sifter DoseBill PadThin VoucherOp Theatre
variable (P:Spine)(K:P.Register)(x:P.Spectrum0 3) (c r:ℕ→ℕ)(i:ℕ)(a:ℝ)(F G:SampleDose)(b:ℕ→ℕ) (Z W:Lead.Clan)
local notation "N"=> r i
variable (D:∀ Z:Lead.Clan, P.VoucherOp x Z (r i) b)
local notation "U"=>reviewEarlierBox
local notation "V"=>reviewLaterBox
local notation "H"=> P.ManyF 3 (P.otherSpectrum 3 3 x)
local notation "ℍ"=> P.ColorHil 3 (P.otherSpectrum 3 3 x)
local notation "ω"=> P.heaven 3 (P.otherSpectrum 3 3 x)
local notation "ν"=> P.seasons 3 (P.otherSpectrum 3 3 x)
namespace BoxBill
lemma orderSingle (t:Bool): Ordered [t] lEdge rEdge := ⟨List.pairwise_singleton ..,List.nodup_singleton _,fun _ _ u v h=> by replace h := congrArg List.length h; simp at h; omega⟩
lemma transOrdered : Ordered wedding lEdge rEdge:=by
  refine ⟨List.pairwise_pair.mpr (show _ from le_rfl),by decide,?_⟩; intro j i A D h
  have g:= congrArg List.length h; rcases A with _|⟨b,A⟩
  · change [false,true]=j::i::D at h
    obtain ⟨h,e⟩:= List.cons.inj h; simp only [← h, ←(List.cons.inj e).1, rEdge, lEdge,Bool.false_eq_true, ↓reduceIte]
  simp [wedding] at g <;> omega
lemma readyBefore (F:SampleDose)(z:tsupport F.val⊆ (U).invites): ReadyThin F stopEarly 0:=by
  refine ⟨1/2,by positivity,fun i e=>?_⟩
  obtain ⟨hp,ht⟩:=(show -2 < i 3∧ i 3 < -1 from z e 3 (Set.mem_univ _)); unfold stopEarly; constructor <;> linarith
lemma readyAfter (G:SampleDose)(z:tsupport G.val⊆ (V).invites): ReadyThin G 0 stopLate := by
  refine ⟨1/2,by positivity,fun i e=>?_⟩
  obtain ⟨hp,ht⟩:=(show 1 < i 3∧ i 3 < 2 from z e 3 (Set.mem_univ _)); unfold stopLate; constructor <;> linarith
lemma outside (F:SampleDose)(X:Doorway)(f:tsupport F.val ⊆ X.spare.invites) : tsupport F.val ⊆ X.invites:= f.trans (Set.Subset.trans subset_closure X.sparesDoor)
private lemma linkBill (X:Hilbert)(x:X)(A:Bool→X.Op) : markVoice X x (word A [false,true]) = inner ℂ x (A false (A true x)):=by change inner ℂ x (A false ( (A true*1 : X.Op) x))=_; rw [mul_one]
lemma jointBill : jointPrice P x r i F G b Z W D = inner ℂ ω ((D Z).thinOp false F stopEarly 0 ((D W).thinOp true G 0 stopLate ω)) := linkBill H ω (fun j=>(D (flagsFor Z W j)).thinOp j (smearsFor F G j) (lEdge j) (rEdge j))

-- instantiate receipts on the genuinely separated pair of compact boxes
variable (X : Weather P x latch downDue (r i) b) (m:P.calibration.ℓ<r i) (g:F.Normalized)(h:G.Normalized)(f:tsupport F.val ⊆ (U).spare.invites)(p:tsupport G.val⊆ (V).spare.invites)
include f p
lemma witnesses (q:Bool) : P.SeeStatic x r i F G b Z D q:=by
  intro ε o
  let T:= smearsFor F G q; let Y:= if q then V else U; let A:= D Z
  have hx:tsupport T.val⊆ Y.spare.invites:=by cases q; exact f; exact p
  have hg: (if q then reviewLaterBox.invites else reviewEarlierBox.invites)=Y.invites:=by cases q<;>rfl
  rw [hg]
  filter_upwards [A.shrink q ε o, A.dwellings q T Y hx] with i x y t p
  exact ⟨y.2 t p,fun x₀=>⟨(x _ p).2 _,(A.isObserved q T i t x₀).1⟩⟩
include X m g h
lemma insideReview (J:P.Ellis 3 x) : P.OrderedCost x r i F G b Z W D := by
  have hx:= outside F (U) f; have hp:= outside G (V) p
  have he(B:Bool) : ReadyThin (smearsFor F G B) (lEdge B) (rEdge B):= by cases B; exact readyBefore F hx; exact readyAfter G hp
  have hq(L:List Bool)(p:Ordered L lEdge rEdge) : weddingCost P x r i F G b Z W D L:= Theatre.pays x (flagsFor Z W) _ id (smearsFor F G) lEdge rEdge L J p (fun i _=>he i) m
  have a := (D Z).receives (D W) X g h hx hp
  exact ⟨hq _ (orderSingle _),hq _ (orderSingle _),hq _ transOrdered,jointBill P x r i F G b Z W D ▸ a.1, jointBill P x r i F G b Z W D ▸ a.2, half_pos (mul_pos (purePrice_p Z) (purePrice_p W))⟩
lemma boxesGet (z:StrictMono b)(J:P.Ellis 3 x)(a':P.ReturnsSix x (c i) (r i) a F G)(v:∀Z:Lead.Clan,P.spacePrice (P.RTest Z (c i) (r i)) F ⊆ (U).spare.invites)(w:∀Z:Lead.Clan,P.spacePrice (P.FTest Z (c i) (r i)) G⊆ (V).spare.invites): P.GetsThin K x c r i a F G b D:=
  let Q(z:Doorway):z.spare.invites⊆ z.invites:= Set.Subset.trans subset_closure z.sparesDoor
  ⟨⟨g,h,f.trans (Q _),p.trans (Q _)⟩,⟨a',P.reviewWardContrast K x (c i) (r i) a F G a'⟩,fun i=>⟨(v i).trans (Q _),(w i).trans (Q _)⟩,⟨m,z⟩,X,fun t=>P.thin_comparator t x,fun Z B=> witnesses P x r i F G b Z D f p B,fun Z W=> insideReview P x r i F G b Z W D X m g h f p J,fun Z=>(D Z).occupancy X⟩
omit X m g h f p
end BoxBill
open BoxBill
#print axioms BoxBill.orderSingle
#print axioms BoxBill.transOrdered
#print axioms BoxBill.witnesses
#print axioms BoxBill.insideReview
#print axioms BoxBill.boxesGet
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
