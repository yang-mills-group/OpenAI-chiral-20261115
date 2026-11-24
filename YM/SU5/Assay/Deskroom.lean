import YM.SU5.Assay.SeenBox
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
variable (P j) in
/-- Time reflection between the calipers, including OS conjugation. -/
def riposte (w:ℕ)(f:P.Test): P.Test:=aureole K j (gaugeT K w) f
lemma riposte_keeps (p:f∈ S):P.riposte j w f∈S:= P.mirror_keeps _ _ p
lemma BEntry.riposte(p:P.BEntry j w f): P.BEntry j w (P.riposte j w f):=
  BEntry.ofCard (SlabMark.inverse Y H 0 j false w (p.card 0)) p.pos rfl
lemma BEntry.across(p:P.BEntry j w f)(d:Trans j)(a:ℤ):P.BEntry j w (P.shifts d a f):=
  BEntry.ofCard (SlabMark.alongS Y H 0 j false w (p.card 0) d a) p.pos rfl
variable(s)
lemma meanBox_star(p:P.BEntry j w f):star (μ j s w f)= μ j s w (P.riposte j w f):= by
 let g:=SlabMark.inverse Y H s j false w (p.card s)
 rw [meanBox_eq s p, meanBox_card s g p.pos (f:=P.riposte j w f) rfl]; exact respects ..
lemma meanBox_across (p:P.BEntry j w f)(d:Trans j)(a:ℤ):
   T j (s,a,d)* μ j s w f= μ j s w (P.shifts d a f)* T j (s,a,d):=by
 let g:= SlabMark.alongS Y H s j false w (p.card s) d a
 rw [meanBox_eq s p, meanBox_card s g p.pos (f:=P.shifts d a f) rfl]; exact shape_across ..
lemma meanBox_earns (p:P.BEntry j w f):inner ℂ (Ω j) (μ j s w f (Ω j))=P.E s f.val :=by
 rw [meanBox_eq s p];exact boxed_at Y H V s π Qt _ false C₀ _ _ p.pos
lemma meanBox_state (p:P.BEntry j w f): P.compressed j s f=(P.piZero j).comp ((μ j s w f).comp (P.inHil j)):=by
 rw [meanBox_eq s p]; exact P.compresses j s w p.pos (p.card s)

variable (P j)
lemma E_invariant (z:ℤ)(f:P.Test):P.E s ((σ z f).val)=P.E s f.val:=SWay Y H V s j (2*z) f.property
lemma floor_moves (G:Grid j): T j G (Ω j)=Ω j:= ((P.ground_ok j _).mp (P.groundZero j).property).2 G
lemma slide_up (z:ℤ)(t:ℕ)(p:s≤t)(d:Trans j): T j (s,z,d)= T j (t,castor (timeMesh Λ) s t z,d):=by
  exact congrArg (P.crew j d).play (notch_up _ s t p z).symm

/-- Images of forward fields via the full stamps contain all pieces. -/
lemma floor_range (x:P.Vox j s) : ∃ w f,P.BEntry j w f∧ μ j s w f (Ω j)=P.piece j s x:=by
 obtain ⟨a,p,u,rfl⟩:= P.fits j s x
 refine ⟨a,P.entryTest j s u,BEntry.ofCard u p rfl,?_⟩
 rw [meanBox_card s u p (f:=P.entryTest j s u) rfl]; exact SlabMark.lays ..
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
