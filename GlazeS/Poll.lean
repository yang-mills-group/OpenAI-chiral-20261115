import GlazeS.PrismL
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open Py.Rate.Pitching.Focus (Morn)
variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ i,F ≤ i → Accordance P M F i (C i) (D i))(q:RobeRoad P F C D x)(J:P.Ellis 3 x)(A B:SampleDose)(pA:hull A)(pB:hull B)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "W"=>P.ManyF 3 ξ
local notation "H"=>P.ColorHil 3 ξ
local notation "v" k:max y:max=> estimate P F C D x y k
local notation "aH" i:max k:max y:max=> athlete P F C D i k y
local notation "V" i:max k:max y:max=> arts P x i k (recoup P F C D (ξ) i i) (dealt y (central P F i))
-- actual arity: include joints. one projection for viewport.O.Use lamellar.GI.Center.
include q pA p
lemma cotton:Tendsto (fun i=> v i A) atTop (𝓝 (MiterT.cloud P F C D x A)):= (meteor P F C D (ξ) M p (rankBridge P F C D x q) A pA).1
omit q p
lemma eligibleH :∀ᶠ i:ℕ in atTop,∀ y∈tsupport A.val,tidal P F i ≤ y 3:=by obtain ⟨c,t,u⟩:=pA; exact ((recessVanish P F).eventually (ge_mem_nhds t)).mono fun i h y p=> h.trans (u y p).le
include q p J
lemma one_vault: ∀ᶠ s in atTop,
    Tendsto (fun t=>P.singleState 3 t x (aH s t A)) atTop (𝓝 (inner ℂ (P.colorZero 3 ξ) (P.enter 3 ξ (v s A)))):=by
 filter_upwards [eligibleH P F A pA,eventually_ge_atTop F] with s h g
 have H':Tendsto (fun t=> inner ℂ (P.colorZero 3 ξ) (V s t A)) atTop (𝓝 (inner ℂ (P.colorZero 3 ξ) (P.enter 3 ξ (v s A)))):= tendsto_const_nhds.inner (sharp_stone P F C D x s A g J)
 apply H'.congr'; filter_upwards [eventually_ge_atTop s] with t p
 let k:=gland P F C D x s t A p h
 exact k.choose_spec ▸ ((P.view_scalar 3 (ξ) t k.choose).trans (P.single_agrees 3 3 x ..)) -- rw style
include pB
lemma two_vault: ∀ᶠ s in atTop,
    Tendsto (fun t=>P.singleState 3 t x (P.reflectTest 3 (aH s t A)* aH s t B)) atTop (𝓝 (inner ℂ (v s A) (v s B))) :=by
 filter_upwards [eligibleH P F A pA,eligibleH P F B pB,eventually_ge_atTop F] with s h h' g
 rw [← (P.enter 3 ξ).inner_map_map]
 apply ((sharp_stone P F C D x s A g J).inner (sharp_stone P F C D x s B g J)).congr'
 filter_upwards [eventually_ge_atTop s] with t p using fingerGram P F C D x s t A B p h h' -- $λ
lemma answers : let l:=fun k:ℕ=> limUnder atTop (fun i=> P.singleState 3 i x (P.reflectTest 3 (athlete P F C D k i A)*athlete P F C D k i B)); Tendsto l atTop (𝓝 (inner ℂ (MiterT.cloud P F C D x A) (MiterT.cloud P F C D x B))) :=by
 intro l
 refine ((cotton P F C D x M p q A pA).inner (cotton P F C D x M p q B pB)).congr' ?_
 filter_upwards [two_vault P F C D x M p q J A B pA pB] with i h; exact h.limUnder_eq.symm
#check LinearIsometry.inner_map_map
#print axioms answers
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
