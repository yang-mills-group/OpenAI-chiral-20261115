import SatinFixedContrastNovember4
import YM.SU5.Assay.Motive
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
/-! Price movement with the hosts, sensors and final commitments. Vary both
 mold heights along independent schedules, and pose at *any* stage eligible
 for both. Coercions use the very same `x`.
-/
-- public assumption; discharged by RawNormal arms
abbrev LightRig (P:Spine)(x:P.Spectrum0 3)(A:Lead.Clan→ℕ→P.Apron):Prop:=
 ∀Z a' b', SeedBook (litRow 3 a' b' 0) (fun i:ℕ×ℕ=>P.rawSlot 3 x i.2 (A Z i.1) a' b')
namespace Assay
local notation "γ"=>P.seatGrid R x
local notation "V"=>P.seatStage x (a) (b) (c)
local notation "ξ"=>P.seatPair x (a) (b) (c)
local notation "τ"=>ξ F G T U
variable (u:D.Rival F f)(v:N.Rival G g)
include p u v
lemma roam : Tendsto (fun k=>ξ (f k) (g k) T U) atTop (𝓝 τ):=by
 refine tendsto_pi_nhds.mpr fun Z=>tendsto_pi_nhds.mpr fun W=>?_
 have y:Tendsto (fun k=>κ (T Z) (a) (b) (f k)) atTop (𝓝 (κ (T Z) (a) (b) F)):=
    tendsto_iff_norm_sub_tendsto_zero.mpr ((botanical (p.early.heat Z).normal.credits).rival
       (Doorway.plots p.old.taps.sep).1 u (fun _=>()))
 have z:Tendsto (fun k=>κ (U W) (b) (c) (g k)) atTop (𝓝 (κ (U W) (b) (c) G)):=
    tendsto_iff_norm_sub_tendsto_zero.mpr ((botanical (p.late.heat W).normal.credits).rival
       (Doorway.plots p.old.taps.sep).2 v (fun _=>()))
 exact tendsto_const_nhds.inner (𝕜:=ℂ) ((BSOT.fromNorm (y.mul z)).showAt _)
variable (hi:Tendsto i atTop atTop)(hj:Tendsto j atTop atTop)
include hi hj
lemma clasp : Tendsto (fun k=>V (f k) (g k) A B (i k) (j k)) atTop (𝓝 τ):=by
 refine tendsto_pi_nhds.mpr fun Z=>tendsto_pi_nhds.mpr fun W=>?_
 let y:=(p.early.heat Z).normal; let z:=(p.late.heat W).normal
 have α:=((y.pour p.walls.1).visit hi).squeeze' ((y.all_stage (a) (b)).rival (Doorway.plots p.old.taps.sep).1 u i)
   («b»:=fun k=>κ (β (A Z (i k))) (a) (b) (f k)) (Eventually.of_forall fun _=>le_rfl)
 have ψ:=((z.pour p.walls.2).visit hj).squeeze' ((z.all_stage (b) (c)).rival (Doorway.plots p.old.taps.sep).2 v j)
   («b»:=fun k=>κ (β (B W (j k))) (b) (c) (g k)) (Eventually.of_forall fun _=>le_rfl)
 exact tendsto_const_nhds.inner (𝕜:=ℂ) ((α.mul ψ).showAt _)
variable (J:P.Ellis 3 x)(Y:P.LightRig x A)(X:P.LightRig x B)
include J Y X
lemma gather (w:∀k,max (i k) (j k)≤t k): Tendsto (fun k=>γ (f k) (g k) A B (i k) (j k) (t k)) atTop (𝓝 τ):=by
 refine tendsto_pi_nhds.mpr fun Z=>tendsto_pi_nhds.mpr fun W=>?_
 have e:Tendsto t atTop atTop:= tendsto_atTop_mono (fun k=>le_of_max_le_left (w k)) hi
 have r:Tendsto (fun k=>(i k,t k)) atTop atTop:=by rw [←prod_atTop_atTop_eq]; exact hi.prodMk e
 have s':Tendsto (fun k=>(j k,t k)) atTop atTop:=by rw [←prod_atTop_atTop_eq]; exact hj.prodMk e
 have α:=(((p.early.heat Z).pressed _ _ _ p.walls.1).visit r).squeeze'
  ((Y Z (a) (b)).rival (Doorway.plots p.old.taps.sep).1 u (fun k=>(i k,t k)))
  («b»:=fun k=>σ (t k) (A Z (i k)) (a) (b) (f k)) (Eventually.of_forall fun _=>le_rfl)
 have ψ:=(((p.late.heat W).pressed _ _ _ p.walls.2).visit s').squeeze'
  ((X W (b) (c)).rival (Doorway.plots p.old.taps.sep).2 v (fun k=>(j k,t k)))
  («b»:=fun k=>σ (t k) (B W (j k)) (b) (c) (g k)) (Eventually.of_forall fun _=>le_rfl)
 refine (α.mul ψ).price.congr' ?_
 filter_upwards [p.alter J u v univ_mem,p.qualifies hi hj] with k h q
 exact (h.2.exposed q Z W _ (w k)).symm
end Assay
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
