import YM.SatinExist.GlassStamp
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Set
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "Ψ" => P.voyageF 3 (β)
local notation "yb@" i:max=> P.shard x Z (c (i:ℕ)) (r (i:ℕ))
local notation "ρ" i:max=> P.dew (c (i:ℕ)) (r (i:ℕ))
local notation "Γ" => marks (timeMesh P.par)
local notation "Nt" => notch (timeMesh P.par)
open Aria Casting Six
open FirstWindows FirstWindows.Chambers
local notation "H"=> P.ColorHil 3 (β)
local notation "B"=> P.par.block
local notation "l₀"=> P.width
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ρₛ" t:max=> Selected.gaugeMesh Λ t
local notation "θ" t:max => Selected.gaugePosition Λ t
local notation "ℓ"=> P.calibration.ℓ
-- representation as strict gauges on this very axis and house. Arena-based OS = ColorHil, no boost.
variable (j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "Hi" => P.GreatRoom x j
local notation "η" => P.orientHouse x j
local notation "F"=> FirstWindows.Domain P.run P.large P.projection
local notation "G"=>P.projection
local notation "d~"=> FirstWindows.insideAt Λ l₀ K
local notation "Os"=> FirstWindows.physicalKet P.run P.large P.law G j (P.room j) η
variable (O:Set Vantage)
local notation "Q₀"=> (flank j 0 ∩ O)
noncomputable def ticketParade : FirstWindows.Domain P.run P.large G true (flank j 0 ∩ O) →ₗ[ℂ] Hi:= (Os).comp (Submodule.inclusion (domain_mono P.run P.large G inter_subset_left))
def seeingBalcony : Submodule ℂ (P.GreatRoom x j).space := LinearMap.range (P.ticketParade x j O)
lemma available_singlet (s:ℕ) (f:P.Test)(p:f∈ insideAt P.par l₀ K true (flank j 0 ∩ O) s) (g:P.birthF j s f) : P.colorRoom x j (P.viewF j ξ s g)∈ P.seeingBalcony x j O :=by
 obtain ⟨a,d,w,e⟩:= P.birth_foyer x j s g
 let f':= FirstWindows.enclose P.run P.large G (Q₀) true s ⟨f,p⟩
 apply LinearMap.mem_range.mpr; refine ⟨f',?_⟩
 change Os _=_
 exact (congrArg (Os) (Subtype.ext w.symm)).trans e.symm
structure ColorTicket (O:Set Vantage)(p:(P.GreatRoom x j).space) : Prop where
 earn : ∃ (s:ℕ)(A:P.Test)(g:A∈ FirstWindows.insideAt P.par l₀ K true (flank j 0 ∩ O) s), ∃ h:P.birthF j s A, p=P.colorRoom x j (P.viewF j ξ s h)
lemma furnished_here (p:(P.GreatRoom x j).space) : p∈ P.seeingBalcony x j O ↔ P.ColorTicket x j O p:=by
 constructor
 · intro v; obtain ⟨f,rfl⟩:= LinearMap.mem_range.mp v; obtain ⟨s,A,rfl⟩:= (eventually_enclosed P.run P.large P.projection f).exists
   let A':=A.val; obtain ⟨w,h⟩:= (P.pinFoyer ..).1 (show A'∈d~ true (Q₀) s from A.property)
   have he:A'∈d~ true (flank j 0) s:= FirstWindows.insideAt_mono (Set.inter_subset_left) A.property
   -- positive_today gives Field b at true
   have u:= (FirstWindows.positive_today P.run P.large j s A').1 he
   let V₁:= (FirstWindows.asField P.run P.large j true s) ⟨A',he⟩
   let V':= Selected.admit P.run P.large s j V₁
   have p':P.birthF j s A':= ⟨⟨V',show _ from h⟩,rfl⟩
   obtain ⟨a,d,l,e⟩:= P.birth_foyer x j s p'
   refine ⟨s,A', (show A'∈ _ from A.property),p',?_⟩
   change Os _=_
   exact (congrArg (Os) (Subtype.ext l.symm)).trans e.symm
 rintro ⟨s,A,g,k,rfl⟩
 exact P.available_singlet x j O s A g k
local notation "T₀"=> (P.seeingBalcony x j O)
lemma held_in_escrow (p: Hi) : p∈ (T₀).topologicalClosure ↔
    ∀ ε:ℝ,0<ε →∃ (s:ℕ)(A:P.Test)(Y₀:Finset Cover), A ∈ bay P.calibration Y₀ true ∧ A∈ enclave P.calibration ∧
      PhaseChoice.SupportedPhysically P.par l₀ s Y₀ (flank j 0 ∩ O) ∧ ∃ h:P.birthF j s A, dist p (P.colorRoom x j (P.viewF j ξ s h)) < ε:=by
 change p∈ closure _ ↔ _; rw [Metric.mem_closure_iff]
 constructor <;> intro h ε e <;> specialize h ε e
 · obtain ⟨s,v,w⟩:=h; obtain ⟨m,A,g,k,rfl⟩:= (P.furnished_here x j O s).mp v
   obtain ⟨⟨Y,u,a⟩,p'⟩:= (FirstWindows.mem_insideAt ..).1 g
   exact ⟨m,A,Y,u,p' rfl,a,k,w⟩
 obtain ⟨m,A,Y,u,p',a,k,w⟩:= h
 exact ⟨_, P.available_singlet x j O _ _ ((mem_insideAt ..).2 ⟨⟨Y,u,a⟩,fun _=>p'⟩) k, w⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
