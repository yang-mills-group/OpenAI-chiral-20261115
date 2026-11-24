import SatinFixedContrastNovember4
import YM.SU5.Assay.Day
import YM.SU5.Assay.Harvest
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
/-!
 Read a pair on real walls. Adjacent chronological enrollment suffices;
 for width=0 this means just strict order and proper clearance of the
 sample supports (compact). Thus the same separation suffices, for all
 narrowings including different width schedules. **Operator brew** for
 the two encounter calls and their product; both ways on actual prices
 even when dressed according to old rules. No coincidence claim.
-/

/-- Final smeared pair seat. `T` already includes earlier orientation. -/
def seatPair (a b c:ℝ)(F G:SampleDose)
 (T U:Lead.Clan→P.LagOp 3 x):CrossRead:= Matrix.of fun Z W=> ⟪κ (T Z) a b F * κ (U W) b c G⟫
abbrev seatStage (a b c:ℝ)(F G:SampleDose)(A B:Zs→ℕ→P.Apron)(i j:ℕ) :=
 P.seatPair x a b c F G (fun Z=>β (A Z i)) (fun W=>β (B W j))
/-- Actual array on hosted consultation, **earlier Satin normalization**. -/
def seatGrid (P:Spine)(R:P.Register)(x:P.Spectrum0 3)(F G:SampleDose)(A B:Zs→ℕ→P.Apron)(i j t:ℕ):CrossRead:=
 Matrix.of fun Z W=> P.spiritBoth R x t (A Z i) F (B W j) G

namespace Irons
variable {P R x A l T B m U}
variable (p:P.Irons x A l T)(q:P.Irons x B m U)
variable {a b c:ℝ}{F G:SampleDose}(u:Walled 3 F a b 0)(v:Walled 3 G b c 0)
variable (f g:ℕ→ℕ)(Z W:Ballad.Lead.Clan)
variable (r:Tendsto f atTop atTop)(k:Tendsto g atTop atTop)
-- variable order f g Z W r k
local notation "μ"=>P.singleState 3
local notation "γ"=>P.prepared
local notation "δ" s:max=>A Z (f s)
local notation "ν" s:max=>B W (g s)
local notation "X" s:max=> κ (β (δ s)) a b F
local notation "Y" s:max=> κ (β (ν s)) b c G
local notation "T₀"=>κ (T Z) a b F
local notation "U₀"=>κ (U W) b c G

include p u r
lemma display : P.Porcelain 3 x f (fun s t=> γ t (δ s) F) a b
 (fun s t=> σ t (δ s) a b F) (fun s=>X s) T₀:=
 (((p.heat Z).visit r).porcelain u).raise (Eventually.of_forall fun _=> (p.native _ _).le)
-- Single-slot actual consultations as well
variable (R)
lemma scene : BothWays f (fun s t=>P.spiritOne R x t (δ s) F) (fun s=>⟪(X s)⟫) ⟪T₀⟫:=
 (p.display u f Z r).traces.congr' (Eventually.of_forall fun _=>⟨rfl,fun _ _=>(P.spirit_single ..).symm⟩)

include q v k
lemma tour : P.Porcelain 3 x (fun s=>max (f s) (g s)) (fun s t=> γ t (δ s) F*γ t (ν s) G) a c
 (fun s t=> σ t (δ s) a b F * σ t (ν s) b c G) (fun s=>X s*Y s) (T₀ * U₀):=
 (p.display u f Z r).compound (q.display v g W k)
omit k r in
lemma call : P.seatPair x a b c F G T U Z W = P.two_call 3 x (T Z) F b (U W) G:=
 (two_call_from (p.heat Z).normal.credits (q.heat W).normal.credits u v).symm
omit k r in
lemma audition : Duet (P.seatGrid R x F G A B) (P.seatStage x a b c F G A B) (P.seatPair x a b c F G T U):=by
 refine Duet.pi fun Z=>Duet.pi fun W=>fun f g r k=>(p.tour q u v f g Z W r k).traces.congr' ?_
 exact Eventually.of_forall fun _=>⟨rfl,fun _ _=>(P.spirit_pair ..).symm⟩
end Irons
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
