import GaugeFieldConstruction.StyriaRel.YM.Work.C03
import GaugeFieldConstruction.StyriaRel.YM.Work.C04
import GaugeFieldConstruction.StyriaRel.YM.Work.C05
import GaugeFieldConstruction.StyriaRel.YM.Work.C06
import GaugeFieldConstruction.StyriaRel.YM.Work.C07
import GaugeFieldConstruction.StyriaRel.YM.Work.C08
import GaugeFieldConstruction.StyriaRel.YM.Work.C09
import GaugeFieldConstruction.StyriaRel.YM.Work.C10
import GaugeFieldConstruction.StyriaRel.YM.Work.C11
import GaugeFieldConstruction.StyriaRel.YM.Work.C12
import GaugeFieldConstruction.StyriaRel.YM.Work.C13
import GaugeFieldConstruction.StyriaRel.YM.Work.C14
import GaugeFieldConstruction.StyriaRel.YM.Work.C15
import GaugeFieldConstruction.StyriaRel.YM.Work.C16
import GaugeFieldConstruction.StyriaRel.YM.Work.C17
import GaugeFieldConstruction.StyriaRel.YM.Work.C18
import GaugeFieldConstruction.StyriaRel.YM.Work.C19
import GaugeFieldConstruction.StyriaRel.YM.Work.C20
import GaugeFieldConstruction.StyriaRel.YM.Work.C21
import GaugeFieldConstruction.StyriaRel.YM.Work.C22
import GaugeFieldConstruction.StyriaRel.YM.Work.C23
import GaugeFieldConstruction.StyriaRel.YM.Work.C24
import GaugeFieldConstruction.StyriaRel.YM.Work.C25
import GaugeFieldConstruction.StyriaRel.YM.Work.C26
import GaugeFieldConstruction.StyriaRel.YM.Work.C27
import GaugeFieldConstruction.StyriaRel.YM.Work.C28
import GaugeFieldConstruction.StyriaRel.YM.Work.C29
/-!
# Wick stroke. Parametric version on this reconstruction.

* drain from the direct generated contour.
* supports kept in the actual absolute Points frequency coordinates; cone laws & suffix laws.
* T=S for the mean instance, T=chosen on (139) for the selected one, from the Ward M chronology.
* no impropriety on T or cap demands; smooth needed on Conf, to be earned actually.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.LD
open YM.Boundary Mink OS Function MeasureTheory Filter Set Metric Table Boundary Analysis Bid
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace
variable {G:Gauge}{L:Register G}{S T:Table L}{R:Rotation S}{s:S.RealSpin}{P:DiffPlan S}
variable {V:LRoom T timeAxis}{B:Small S V}{K:Spins S}{F:Waves S}{W:Surface S}
structure FitsL (S T:Table L)(R:Rotation S)(s:S.RealSpin)(P:DiffPlan S)(K:Spins S) :Prop where
  hS:S.Symmetric
  hs:T.Basic
  respect:T.respects S
  ready:P.Inclusions S
  hom:T.Homogeneous
  orient:R.OrientedL T
  ranks:R.Horizon P s
  signs:K.Descends R s
  sm:T.Smooth

-- literal F defined by This Small, **not** existential replacement of direct connection.
structure LoreL (F:Waves S)(K:Spins S)(W:Surface S)(T:Table L) :Prop where
 heat : F.Region T
 estimates : F.Breathes
 joints : F.NonTangentialFree W
 tilted : F.during W
 turns : Urs W K
 habitat : Bid.cones W

variable (A16:Bid.A16) (H:FitsL S T R s P K)
include A16 H in
lemma lightStrokeL (hr:F.Region T)(hh:F.Breathes):∃ W:Surface S,LoreL F K W T:=by
 obtain ⟨hv,hd,hu⟩:= Work.C04.answer S T F hr hh
 obtain ⟨W,hw⟩:= F.jointly hv hd hu hh
 have h:=Work.C07.answer S T R K s H.hS P H.ready H.sm H.respect H.orient H.ranks H.signs F hr hh hv hu hd
 have hx:=Work.C09.answer A16 Work.C08.answer S T R K s H.hS P H.ready H.hom H.respect H.orient H.ranks H.signs F W hr hh h hw
 have hs:=Work.C05.answer S T F W hr hh hu hd hw
 have hz:=Work.C06.answer S T F W hr hh hv hs
 exact ⟨W,hr,hh,hw,hs,hx,fun n=>tents W K hx (hz n)⟩
include A16 H in
lemma sprayL (book:Slice B):∃ (F:Waves S) (W:Surface S), Direct B F ∧ LoreL F K W T := by
 obtain ⟨F,p⟩:= Work.C03.answer S T _ B book
 obtain ⟨W,h⟩:= lightStrokeL A16 H p.reach p.birth
 exact ⟨F,W,p,h⟩
variable (h:LoreL F K W T)
noncomputable def drapeL (n:ℕ): Blanket n := Classical.choice (Work.C11.answer n)
lemma glazeL (D:∀ i,Blanket i) i : (D i).Modified := Work.C12.answer i (Work.C10.answer i) _
include h in
lemma FaceL (D:∀ i,Blanket i):∃ X: Surface.Aurora W D,X.FullBody F := by
 obtain ⟨X,P⟩ := Work.C13.answer W D Work.C10.answer (glazeL D)
 exact ⟨X, Work.C15.answer W D (glazeL D) h.habitat X P
     (Work.C14.answer W D (glazeL D) h.habitat Work.C10.answer X P) F h.heat h.estimates h.joints.int h.tilted⟩ -- legal name check
include H h in
lemma localityL {D:∀ i,Blanket i} (X:Surface.Aurora W D)(hv:X.FullBody F) : Actor W := by
 intro n v G
 apply G.actor X v (glazeL ..) (h.habitat n)
 obtain ⟨y,hy,p⟩:= Work.C17.answer n G; refine ⟨y,hy,fun m=>?_⟩
 obtain ⟨X'⟩:=Work.C19.answer K W D F X h.habitat hv R s H.signs P H.hS H.ready
     (Work.C18.answer _ _ _ H.signs) (Work.C16.answer W K D X F (glazeL D) h.habitat h.turns hv) n v G (y m) (p m).1 (p m).2
 exact ⟨X',Work.C20.answer P F W D X H.hS H.ready H.hs.toSymmetric H.sm H.respect h.heat hv n v _ G X',
    Work.C21.answer F W D X (glazeL D) hv n v _ G X'⟩
include H h in
lemma TerribleHoldL {J:StarOp S} (A:Direct B F)(Q:starRead J s)(v:Work.C22.OnImage B J F): B.Lamp W J K :=
 Work.C24.answer S T V P B F J K W A.reach h.joints (Work.C23.answer S T V P B K R s A.linked.stature H.signs)
   (Work.C22.StageAnswer P H.ready H.hS H.hs.toSymmetric h.heat H.respect v Q)

-- field space and embedded translation dynamics, actually identifies tests at boundary.
structure PredictionL (W:Surface S) (F:Waves S)(K:Spins S) (J:StarOp S)(B:Small S V) (R:Rotation S) (s:S.RealSpin) where
 system: Wightman S
 course: system.Realizes (W:=W) R s
 withStar: system.J=J
 labels: system.spin=K
 inlet: LoreL F K W T
 tap:Direct B F
 link: B.Lamp W J K
 mapSpace: (system.operators.H →L[ℂ] V.H)
 isometry: system.action.Intervenes (C:=V) mapSpace system.operators.vacuum
 assign (b: Sentence S): mapSpace (system.operators.vector b)= ((B.bowls link).out).toFun b
 propagates: Actor W

include H h in
lemma WallLightL {D:∀ i,Blanket i} (X:Surface.Aurora W D)(hv:X.FullBody F) {J:StarOp S} (Q:starRead J s) (A:Direct B F)
    (lamp:B.Lamp W J K) (u:V.jointLine)(n:∀ i,T.null i=S.null i)(p:P.Inclusions T) : Nonempty (PredictionL W F K J B R s) := by
 let atom:= (B.bowls lamp).out
 let Z : Soil W J := Classical.choice (Kernel.host atom.safe)
 have vr:= localityL H h X hv
 have ψ:= Work.C27.answer _ W vr
 obtain ⟨a,b⟩:= Work.C29.answer S W J
 have sn:=Work.C28.answer Work.C08.answer S W J K R P s H.hS H.ready H.signs Q h.turns
 have hm:= Work.C26.answer Work.C25.answer S T P D W F X n H.hs.toSymmetric H.sm H.hS H.ready p h.heat hv
 have hz := Boundary.invol H.hS H.ready Q
 obtain ⟨y,e⟩:= Soil.mobilize Z K H.signs sn.2 sn.1
 obtain ⟨U,-,hU,hu⟩:=Z.universal_embed (M:=V.H) atom.toFun atom.at_pair
 have hw:y.Intervenes (C:=V) U (Z.plant []) := by
    refine ⟨hu,fun p=> Z.by_bud ?_,(hU _).trans atom.vacuum⟩
    intro i; change U (y.V _ (Z.plant i))=V.flow.unit.translation p (U (Z.plant i)); rw[e,hU,hU, atom.volume]
 let M : Wightman S:=
    { operators:=Z.starter a,J:=J, action:=y, momentum:=y.orbit.P, spin:=K }
 refine ⟨{ system:=M
           withStar:=rfl
           labels:=rfl
           link:=lamp
           inlet:=h
           tap:=A
           mapSpace:=U
           isometry:=hw
           course:=⟨Q,H.signs,Soil.usable Z a b (atom.soak H.hs),Soil.sharp Z a,Soil.relishes Z a,Soil.regional Z a ψ,Soil.sees Z a hz hm,
                    Soil.cultivates Z K y e a,y.orbit.total,y.spectrum hw,y.only hw u⟩
           propagates:=vr
           assign:=fun b'=>?_ }⟩
 change U ((Soil.starter Z a).vector b')= _
 rw [Soil.bears] -- inspect
 exact hU b'
#print axioms lightStrokeL
#print axioms WallLightL
end YM.NSF.LD
