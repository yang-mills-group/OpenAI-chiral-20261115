import SatinFixedContrastNovember4
import YM.SU5.Assay.Notice
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
variable (P:Spine)(x:P.Spectrum0 3)(t:ℕ)
variable (D:Doorway)(A:P.Apron)(c:Bool)(l:P.Folio)(F:SampleDose)
variable (N:Doorway)(B:P.Apron)(d:Bool)(n:P.Folio)(G:SampleDose)
local notation "f"=>P.prepared t A F
local notation "g"=>P.prepared t B G
local notation "a"=>A.realWidth P
local notation "b"=>B.realWidth P
local notation "X"=>P.spacePrice A F
local notation "Y"=>P.spacePrice B G
local notation "μ"=>P.paperSplit t x
local notation "S" j:max y:max=>P.rawSlot j y t A
local notation "U" j:max y:max=>P.rawSlot j y t B
/-! Sale of two separately oriented notices on their consultations. Exact sealing
 of both competing predictions even without a time axis on which to join the
 operators. In presence of payment for chronological costs on a common host,
 earns everything in one frame, caliper as before, and for any wall choices
 satisfying intrinsic lags. `BothWays` applications for widths require just
 such orders (eventually) and the coming examples charge even the envelopes
 about whole posed stencils there. -/
structure DuoNotice :Prop where
 first:P.Notice x t D A c l F
 second:P.Notice x t N B d n G
 pair: Disjoint (X) (Y)
 prices:P.Payout x t ((X)∪(Y)) (f*g) c
 prior:P.PriorBoth x t A B F G l n=0
 stance:∀ j (L M T:ℝ) (y:P.Spectrum0 j), Walled j F L M ((a) j)→Walled j G M T ((b) j)→
   P.Grips j y t L T (f*g) ((S j y) L M F * (U j y) M T G)
 pays:∀ j L M T (y:P.Spectrum0 j) k w, Walled j F L M ((a) j)→Walled j G M T ((b) j)→P.FrameFace j t ((X)∪(Y)) L T k w→
  P.Sill j y t L T (f*g) ((S j y) L M F * (U j y) M T G) k w ∧ P.Compartment j t ((X)∪(Y)) k w
 loose: ∀f₁∈P.Spent t (X), ∀f₂∈P.Spent t (Y),f₁*f₂∈P.Spent t ((X)∪(Y))

variable {P x t D A c l F N B d n G}
local notation "σ"=>P.DuoNotice x t D A c l F N B d n G
lemma Notice.plus (R:P.Register)(u:P.Notice x t D A c l F)(v:P.Notice x t N B d n G)(p:Disjoint (X) (Y)):
 σ:=by
 obtain ⟨h,q,e⟩:=u.wires.joint F G u.advance v.advance p v.wires R
 have y:=h.invoice
 refine ⟨u,v,p,y,e,
   (fun j L M T y p q=>(u.stance j L M y p).join (v.stance j M T y q)), ?_,fun f₁ h f₂ k=> Spent.visitor h (Spent.in_y k) p⟩
 exact fun j L M T γ _ _ p q z=>⟨z.mount y.localFunds ((u.stance j L M γ p).join (v.stance j M T γ q)), z.tears R x⟩
lemma Notice.beside (R:P.Register)(u:P.Notice x t D A c l F)(v:P.Notice x t N B d n G){o:Orders}(p:D.Later N o 0):σ:=
 u.plus R v ((u.wall (j:=3) le_rfl p.split.1.le).apart (v.wall p.split.2.le le_rfl))
-- Joint curtain-made calipers. The sold outer claims may be fixed in
-- advance (here cuts between boxes, walls on other sides inclusive)
namespace DuoNotice
variable (h:P.DuoNotice x t D A c l F N B d n G){j:Axis}{M:ℝ}(g₁:D.upper j≤M)(g₂:M≤N.lower j)
variable (k r:ℤ)(w v:ℕ)
include h g₁ g₂
lemma safe : Walled j F (D.lower j) M ((a) j)∧ Walled j G M (N.upper j) ((b) j):=
 ⟨h.first.wall le_rfl g₁,h.second.wall g₂ le_rfl⟩
lemma frame (q:P.Curtain D j t k w)(p:P.Curtain N j t r v):
 ∃m,P.FrameFace j t ((X)∪(Y)) (D.lower j) (N.upper j) k m ∧ k+w≤r ∧ k+(m:ℤ)=r+v:=by
 have x:=h.first.faces j k w q
 have y:=h.second.faces j r v p
 have x':P.FrameFace j t (X) (D.lower j) M k w:=⟨x.width,x.left,x.right.trans g₁,x.buys⟩
 have y':P.FrameFace j t (Y) M (N.upper j) r v:=⟨y.width,g₂.trans y.left,y.right,y.buys⟩
 exact x'.connect y'
lemma calipers (q:P.Curtain D j t k w)(p:P.Curtain N j t r v) (y:P.Spectrum0 j):
 ∃m,P.Sill j y t (D.lower j) (N.upper j) (f*g) ((S j y) (D.lower j) M F * (U j y) M (N.upper j) G) k m ∧ P.Compartment j t ((X)∪(Y)) k m∧ k+(m:ℤ)=r+v:=by
 obtain ⟨m,u,_,i⟩:=h.frame g₁ g₂ k r w v q p
 obtain ⟨j,e⟩:=h.safe g₁ g₂
 obtain ⟨a',v⟩:=h.pays _ _ M _ y k m j e u
 exact ⟨_,a',v,i⟩
omit g₁ g₂
local notation "ξ"=> P.advocate 3 x j
local notation "Vac"=>P.colorZero j (ξ)
variable {L T:ℝ}
lemma offer (R:P.Register)(p:Walled j F L M ((a) j))(q:Walled j G M T ((b) j)):
 P.spiritBoth R x t A F B G= inner ℂ (Vac) (((S j (ξ)) L M F * (U j (ξ)) M T G) (Vac)):=by
 rw [P.spirit_pair,(h.stance _ _ _ _ (ξ) p q).price];exact (P.single_agrees ..).symm
lemma rejects (V:P.Test→ₗ[ℂ]ℂ)(v:Factors P.calibration V)(u:MatterWard P.calibration V∨GaugeWard P.calibration V):
 V (P.markPair A B t F.val G.val)=0:=by rw [P.spirit_both_mark]; exact h.prices.ward V v u
lemma canon : μ (f*g)=0∧μ (P.markPair A B t F.val G.val)=0:=by rw [P.spirit_both_mark];exact ⟨h.prices.compare,h.prices.compare⟩
end DuoNotice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
