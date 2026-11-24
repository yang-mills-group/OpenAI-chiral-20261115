import SatinFixedContrastNovember4
import YM.SU5.Assay.Tickets
import YM.SU5.Assay.Authority
import YM.SU5.Assay.Issuing
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Six
variable (P:Spine)(j:Axis)(x:P.Spectrum0 3)
variable (t:ℕ)(M:Set Vantage)
local notation "K"=> P.calibration
/-! Eager invoices, including authentic loose caliper and component
 finances. `Pre` components are priced from their own raw input
 refinements -- not presuming multiplicativity of evolution across
 overlapping factors. `Post` components underpin the canonical test of
 the actual marginals *on the consultation host*, exactly as for the
 verified six-channel comparison. Either may issue height-dependent
 lists. Exact, null, even costed as operators framed in the same
 opening. No claim of consistency on coincident or relativistic tests.
-/

def Compartment (k:ℤ)(w:ℕ):Prop:= ∀ f∈P.Spent t M,
 P.BEntry j w (P.shifts j (-k) f) ∧
 (P.doorBox j t w (P.shifts j (-k) f)).1.1= P.meanBox j t w (P.shifts j (-k) f) ∧
 P.meanBox j t w (P.shifts j (-k) f)=0 ∧
 ∀y:P.Spectrum0 j,P.seenBox j y t w (P.shifts j (-k) f)=0∧P.singleState j t y f=0
section
variable {P j t M}{k:ℤ}{w:ℕ}{a b:ℝ}
lemma FrameFace.tears (h:P.FrameFace j t M a b k w)(R:P.Register) (x:P.Spectrum0 3):
 P.Compartment j t M k w:=by
 intro f u; let y:=P.advocate 3 x j
 have g:=h.rebate R u y
 exact ⟨g.1,g.2.1,g.2.2.1,fun z=>(h.rebate R u z).2.2.2⟩
lemma FrameFace.mount {y:P.Spectrum0 j}{L:(P.ColorHil j y).Op}{f:P.Test} (h:P.FrameFace j t M a b k w)
 (p:P.asked_at t f M)(q:P.Grips j y t a b f L): P.Sill j y t a b f L k w:=by
 let T:=P.physicalEnergy j y; let τ:=P.tock t
 let Y:=T.sand (P.costing j y t k w f) (τ k-a) (b-τ (k+w))
 have s:P.Sill j y t a b f Y k w:= ⟨h.left,h.right,⟨h.bank p,q.color⟩,rfl⟩
 exact s.grips.unique q ▸ s
end

local notation "μ"=>P.paperSplit t x
-- Post expenditure, inclusive of alternative prices even with a single Ward.
structure Payout (f:P.Test)(c:Bool):Prop where
 book :P.PostAsk t x f M c
 localFunds :P.asked_at t f M
 compare :μ f=0
 ward :∀T:P.Test→ₗ[ℂ]ℂ, Factors K T → MatterWard K T ∨ GaugeWard K T → T f=0
 loose: ∃D l,P.pinFoot t D ⊆M ∧ Presented K c D f l ∧ ∀i∈l,i.1∈P.Spent t M∧i.2∈P.Spent t M
section
variable {P x t M}{f:P.Test}{c:Bool}
lemma PostAsk.invoice (p:P.PostAsk t x f M c): P.Payout x t M f c:=by
 have q:=p
 -- explicit because x argument
 obtain ⟨D,l,h,w,_,_,z,e⟩:=q
 exact ⟨p,⟨_,w,h⟩,e,z,PostAsk.sheet p⟩
end

-- A posted orientation entering an eligible consultation.
variable (D:Doorway)(A:P.Apron)(c:Bool)(l:P.Folio)(F:SampleDose)
local notation "B"=>P.spacePrice A F
local notation "η"=>P.prepared t A F
local notation "τ"=>fun j=>(A.realWidth P j)
local notation "ξ" j:max=> P.advocate 3 x j
structure Notice :Prop where
 advance:A.s ≤ t
 admits:∀j,Walled j F (D.foyer.lower j) (D.foyer.upper j) (A.realWidth P j)
 posted : B⊆D.invites
 prices :P.Payout x t (B) (η) c
 wires :P.DressCall x A c l
 prior :P.PriorTithe x t A F l=0
 fired:∀r∈P.usedGrid t F, ∀i∈l,P.sParcel t A i.1 r∈P.Spent t (B) ∧ P.sParcel t A i.2 r∈P.Spent t (B)
 shelter : P.Tickets D t
 faces :∀j k w,P.Curtain D j t k w → P.FrameFace j t (B) (D.lower j) (D.upper j) k w
 stance:∀ j (a b:ℝ)(y:P.Spectrum0 j), Walled j F a b (A.realWidth P j)→ P.Grips j y t a b (η) (P.rawSlot j y t A a b F)
 pays:∀j a b k w (y:P.Spectrum0 j), Walled j F a b (A.realWidth P j)→ P.FrameFace j t (B) a b k w →
   P.Sill j y t a b (η) (P.rawSlot j y t A a b F) k w ∧ P.Compartment j t (B) k w

variable {P D A c l t F}
lemma FirstDress.sell (h:P.FirstDress A c l)(R:P.Register)(p:A.s≤t)(q:tsupport F.val⊆D.spare.invites)(s:D.Stash (A.realWidth P))(u:P.Tickets D t):
 P.Notice x t D A c l F:=by
 have z:=h.call R x
 have g:=z.finer t p F
 have e:=g.1.invoice
 refine ⟨p,s.installs q,?_,e,z,g.2.1, ?_,u,fun _ _ _ v=>v.on_price s q,?_,?_⟩
 · intro r y j v
   obtain ⟨a,b⟩:=(s.installs q j).aperture y
   exact ⟨lt_trans (lt_add_of_pos_right _ (D.change_pos ..)) a,b.trans (sub_lt_self _ (D.change_pos ..))⟩
 · intro r k; exact firstPose.smear h R p _ ((P.usedPose ..).mp k)
 · exact fun j _ _ z h=> P.prepared_grips j z t A p h
 exact fun j _ _ _ _ y g q=>⟨q.mount e.localFunds (P.prepared_grips j y t A p g),q.tears R x⟩
namespace Notice
variable {j x}(h:P.Notice x t D A c l F)
include h
variable {a b:ℝ}
lemma wall (p:a≤D.lower j)(q:D.upper j≤b): Walled j F a b (A.realWidth P j):=
 (h.admits j).outer (p.trans (le_add_of_nonneg_right (D.change_pos j).le)) ((sub_le_self _ (D.change_pos j).le).trans q)
lemma stance3 (p:Walled 3 F a b (A.realWidth P 3)):P.Grips 3 x t a b (η) (P.rawSlot 3 x t A a b F):= h.stance _ _ _ _ p
lemma offer (R:P.Register)(p:Walled j F a b (A.realWidth P j)):P.spiritOne R x t A F=
 inner ℂ (P.colorZero j (ξ j)) (P.rawSlot j (ξ j) t A a b F (P.colorZero j (ξ j))):=by
 rw [P.spirit_single,(h.stance _ _ _ (ξ j) p).price]; exact (P.single_agrees ..).symm
lemma rejects (T:P.Test→ₗ[ℂ]ℂ) (z:Factors K T)(b:MatterWard K T∨GaugeWard K T):
 T (P.paintMark A t F.val)=0:=by rw [←P.reviewWardPaint]; exact h.prices.ward T z b
end Notice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
