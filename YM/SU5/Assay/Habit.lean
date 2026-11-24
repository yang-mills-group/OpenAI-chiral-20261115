import SatinFixedContrastNovember4
import YM.SU5.Assay.Slip
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
open Aria Set Six Ballad
local notation "Zs"=> Ballad.Lead.Clan
variable (P:Spine)(x:P.Spectrum0 3) (D N:Doorway) (F G:SampleDose)
variable (C E:Ballad.Lead.Clan→P.Apron)(l m:Ballad.Lead.Clan→P.Folio)(t:ℕ)
local notation "Φ"=>D.canopy N
local notation "ν"=>P.singleState 3 t x
local notation "W"=>P.prepared t
local notation "α" z:max=> W (C z) F
local notation "β" z:max=> W (E z) G
local notation "μ"=> P.called F G C E t
/-!
 At a habit: all primary exposures, even with review regulator
 normalization & width-dependent normalization factors inside the
 marks, on a single canopy, against canonical actual pure-marginal
 comparison. A single service can serve MANY habits at the same
 tolerance. It pays on an eventual cone of genuine regulators
 (not one built using a different trajectory after seeing the marks).
-/
structure Habit (Gain:Set Slip)(ε:ℝ):Prop where
 bale : P.Bale x D N F G C E l m t
 paid : μ ν∈Gain
 embark : ∀V':P.Test→ℂ,P.Patina 3 t x Φ ε V' → μ V'∈Gain
variable {P x D N F G C E l m t}{Gain:Set Slip}{ε:ℝ}
lemma Bale.gets (b:P.Bale x D N F G C E l m t)(y:Gain∈𝓝 (μ ν)):
 ∃u>0,∀ε≤u,P.Habit x D N F G C E l m t Gain ε:=by
 obtain ⟨w,p,v⟩:=b.threshold y
 exact ⟨w,p,fun _ g=>⟨b,mem_of_mem_nhds y,fun _ h=>v _ (h.thicken g)⟩⟩
namespace Habit
variable (h:P.Habit x D N F G C E l m t Gain ε)
include h
lemma capital: μ ν-μ (P.paperSplit t x)∈Gain:=by rw [h.bale.paper,sub_zero];exact h.paid
variable {k:ℤ}{w n a:ℕ}{Z X Y':Finset Cover} {g:P.Test} {i j:ℕ} {d:ℝ}
variable (p:P.FloorService 3 t x (D.canopy N) k w Z n ε a g X Y' d)
variable (e:P.Flight 3 t x k w Z n ε a g X Y' i j)
local notation "Q"=>P.viewFrom 3 a n w k g
local notation "π₀"=>fun m'=>P.E t (Q m').val
local notation "π"=>fun m'=>P.sterling t i j (Q m')
include p
-- After choosing a viewer but before varying regulators
lemma bid (u:0<ε) : μ (π₀)∈Gain:=
 let v:P.Patina 3 t x Φ (ε/2) (π₀):=fun _ x' _ y=> p.witness.conserve _ (p.agency.auth.mp x') _ y
 h.embark _ (v.thicken (half_le_self u.le))
lemma prices : μ (π)∈Gain ∧ μ e.pressing∈Gain ∧ μ e.primer=0:=
 ⟨h.embark _ (p.film e).1,h.embark _ (p.film e).2,h.bale.primer p e⟩
lemma hits: μ e.pressing-μ e.primer∈Gain ∧ μ (π)-μ (P.paperSplit t x)∈Gain:=by
 obtain ⟨v,w,i⟩:=h.prices p e
 rw [i,h.bale.paper,sub_zero,sub_zero]
 exact ⟨w,v⟩
end Habit
#print axioms Habit.prices
#print axioms Habit.bid
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
