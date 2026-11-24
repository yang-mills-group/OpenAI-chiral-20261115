import SatinPP.Parlor

set_option autoImplicit false
set_option maxHeartbeats 120000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 4500
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Aria
open Hierarchy.Celeritas Land Hierarchy.Seld.Leal
variable (P:Spine)(x:P.Spectrum0 3)
open Germ Alliance Selected FirstWindows

variable (j:Axis)
local notation "C" => P.room
local notation "χ"=>P.chateau x j
local notation "L"=>P.sitting x j
local notation "ξ"=>P.advocate 3 x j
local notation "H"=>P.ColorHil j (P.advocate 3 x j)
local notation "B" s:max f:max=> Selected.bud P.run P.large P.law s P.history P.projection.clipped j false (C j) (χ) f
local notation "ℱ"=>P.voxTest j

local notation "R"=>P.revolving x j
local notation "Θ"=>P.physicalEnergy j (P.advocate 3 x j)
local notation "δ"=>Selected.ride P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)
local notation "M"=>timeMesh P.par
local notation "ℛ"=>P.voyageF j ξ
local notation "ℛ'"=>turnstile P.run P.large P.law P.history P.projection.clipped j false (C j) (χ)


local notation "π'"=> P.province j ξ
lemma parlor_ext (A:(H).Op)(D:(L).Op)
 (h:∀ᶠ s:ℕ in atTop, ∀v:P.naturalVox j s,R (A (π' s v))=D (B s v.val)):
 ∀ u, R (A u) = D (R u):=by
 let a := (P.revolving x j).toLinearIsometry.toContinuousLinearMap
 have p : a.comp A = D.comp a:=by
    refine ContinuousLinearMap.ext_on (P.native_dense j ξ) ?_
    intro v z;obtain ⟨s,y,rfl⟩:=Set.mem_iUnion.mp z
    obtain ⟨u,s',p⟩:=( (eventually_ge_atTop s).and h).exists
    obtain ⟨f,e,_⟩:=P.parlor_rise x j s u s' y
    rw [←e]
    change R (A (_))=D (R _)
    rw [p,P.spins_bud]
 exact fun _=>DFunLike.congr_fun p _


lemma spins_tick(s n:ℕ):
 ∀u,R ((Θ).E (whenly M s n) u)=(δ).E (whenly M s n) (R u):=by
 apply P.parlor_ext
 filter_upwards [eventually_ge_atTop s] with t p v
 rw [← matchR M s t n p,ride_ticks]
 let b:=MeshClock.acts M s t n
 let w:=tick P.run P.large t j 0 false (2*b) v.val
 let v':P.naturalVox j t:= ⟨w,(P.wishing j t v b) ▸ P.shifts_keep j _ v.property⟩
 have g : π' t v'=(Θ).E (whenly M t b) (π' t v):=by
    apply (P.gnsIn j ξ).injective
    change _=P.gnsIn j ξ (P.warming j ξ (whenly M t b) (π' t v))
    rw [P.warmTransit,P.coincides,P.coincides]
    exact P.moves_p ..
 rw [←g,P.spins_bud]
lemma spins_heat(q:ℝ≥0)(u:H): R ((Θ).E q u)=(δ).E q (R u):=
 tendsto_nhds_unique_of_eventuallyEq
  (((R).continuous.tendsto _).comp (((Θ).continuousE u).tendsto q |>.comp (MeshClock.shade M q)))
  (((δ).continuousE (R u)).tendsto q|>.comp (MeshClock.shade M q))
  (Eventually.of_forall fun _=>P.spins_tick ..)


lemma spins_crew(k:Trans j)(m:MeshClock.marks (timeMesh P.par)):
 ∀u,R (((ℛ).crew k).play m u) = ((ℛ').crew k).play m (R u):=by
 obtain ⟨s,i,rfl⟩:=notch_exists _ m
 apply P.parlor_ext
 filter_upwards [eventually_ge_atTop s] with t p v
 rw [←notch_up M s t p i,turnstile_in]
 let b:=castor M s t i
 let w:=sail P.run P.large t j 0 false k.val k.property (2*b) v.val
 let v':P.naturalVox j t:= ⟨w,P.sailNatur j t k.property b v⟩
 have g : π' t v'= ((ℛ).crew k).play (notch M t b) (π' t v):=by
    change _=(P.flutter j ξ k).ship _ _
    rw [Lunation.navZ]
    apply (P.gnsIn j ξ).injective
    change _=P.gnsIn j ξ (P.colorSpace j ξ (P.walksColor j (t,b,k)) _)
    rw [P.moveTransit,P.coincides,P.coincides]
    exact (P.move_use j ξ t k b _).symm
 rw [←g,P.spins_bud]
#print axioms spins_crew


lemma spins_raw (i:List (Trans j))(m:Trans j→ MeshClock.marks (timeMesh P.par)):
 ∀u, R ((ℛ).raw i m u)=(ℛ').raw i m (R u):=by
 induction i with
 |nil=>exact fun _=>rfl
 |cons k i ih=>intro; rw [raw_step,raw_step,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,P.spins_crew,ih]
#print axioms spins_heat
