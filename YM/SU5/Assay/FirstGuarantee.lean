import SatinFixedContrastNovember4
import YM.SU5.Assay.FirstEstimate
import YM.SU5.Assay.Protect
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
open Aria Set OS.Semigroup Ballad Six
variable (P:Spine)(R:P.Register)(x:P.Spectrum0 3)
local notation "Zs"=>Ballad.Lead.Clan
local notation "κ"=>P.coffee 3 x
local notation "σ"=>P.rawSlot 3 x
local notation "β"=>P.base 3 x
local notation "Ω"=>P.heaven 3 x
local notation "O"=>(P.ManyF 3 x).Op
local notation "⟪" T "⟫"=> inner ℂ Ω ((T:O) Ω)
local notation "L"=>P.LagOp 3 x
variable (A : Lead.Clan → ℕ→P.Apron)(l:Lead.Clan→ℕ→P.Folio)(T:Lead.Clan→P.LagOp 3 x)
variable (B : Lead.Clan → ℕ→P.Apron)(m:Lead.Clan→ℕ→P.Folio)(U:Lead.Clan→P.LagOp 3 x)
-- PRE argument order for future
open DoseTravel TopologicalSpace
variable {P R x A B l m T U}{D N:Doorway}{s n:ℕ}{o:Orders}
variable {F G:SampleDose}{f g:ℕ→SampleDose}{i j t:ℕ→ℕ}
variable (p:P.Assay R x s n D N o F G A B l m T U)
local notation "a"=> D.lower 3
local notation "b"=> D.turnCut N
local notation "c"=> N.upper 3
local notation "R1"=>litRow 3 a b 0
local notation "R2"=>litRow 3 b c 0
/-!
 Also perturbative; **not** invoking LightRig as a new hypothesis on
 the physical coupling. The verification of the old measurement holds
 uniformly as well. Not changing smears during any interaction estimate.
-/
lemma full_rig (h:∀Z,∃g d L₀,P.RawNormal 3 x (A Z) g d L₀):
 P.LightRig x A ∧ P.LightRig x (P.fore A):=by
 constructor
 · intro Z u v;obtain ⟨_,_,_,w⟩:=h Z;exact w.shelf u v
 intro Z u v;obtain ⟨_,_,_,w⟩:=h Z;exact w.kiss.shelf u v
namespace Dawn
variable {M:P.Menagerie}
variable (q:P.Dawn R x s n D N o F G M)
local notation "P1"=> P.refront n
local notation "P2"=> P.borne M
local notation "P3"=> P.replayBody n
local notation "C"=> P.togetherBook n
local notation "τ"=> P.visor x M
local notation "Ψ"=> P.fee M
local notation "Old"=> P.arrayReading x s n (b)
include q
lemma rigs : P.LightRig x P1 ∧ P.LightRig x (P.fore P1) ∧ P.LightRig x P2∧ P.LightRig x (P.fore P2):=by
 obtain ⟨u,v⟩:=full_rig (A:=P1) (fun Z=>⟨_,_,_,q.flock.coin_ms P x Z n⟩)
 exact ⟨u,v,full_rig (A:=P2) (x:=x) (fun Z=>⟨_,_,_,P.breath_clutch.inlay_pole M Z (Set.mem_univ _) (P.breath_raw 3 x)⟩)⟩
lemma protected_front (J:P.Ellis 3 x) {Cost Gain:Set CrossRead} (y:Cost∈𝓝 (Old F G))(z:Gain∈𝓝 Ψ):
 ∃ e>0,∃ k≥s,∀F' G',D.Suitable F'→N.Suitable G'→AltNear e F F'→AltNear e G G'→
   P.Bearings R x s n D N o F' G' P1 C τ ∧ Old F' G' ∈ Cost ∧ (∀ t≥k,P.arrayFine x s n t F' G' ∈ Cost)∧∀ i≥k,∀j≥k,
   P.Audit R x (P.fore P1) (P.foreword C) (P.starboard x τ) P1 C τ F' G' s n D N Gain i j:=by
 rw [←q.desk] at z;exact q.rise.1.protects J q.rigs.2.1 q.rigs.1 y z
lemma protects_loss (p:Tasting.Paid P.par) :P.LightRig x P3 ∧ P.LightRig x (P.fore P3):=
 full_rig (fun Z=>⟨_,_,_,P.experiment_wash x Z n p q.taps.extent⟩)
end Dawn
#print axioms Dawn.protected_front
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
