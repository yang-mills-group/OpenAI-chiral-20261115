import YM.SU5.Voyager.Apex
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
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
variable {a j:Axis}{P: Spine} (x:P.Spectrum0 a)
open Aria Set TopologicalSpace Metric Casting
local notation "χ[" k "]"=> P.advocate a x k
local notation "H[" k "]"=> P.ManyF k χ[k]
local notation "Ω[" k "]"=> P.heaven k χ[k]
local notation "Ψ[" k "]"=> P.seasons k χ[k]
local notation "ω[" k "]"=> P.colorZero k χ[k]
local notation "W[" k "]"=>P.cartage k χ[k]
local notation "E[" k "]"=>(Ψ[k]).E
local notation "V[" k "]"=>P.tableau k χ[k]
variable (j)(J:P.Ellis a x) (g:P.lodestarHere j (P.advocate a x j))
open MeasureTheory.Measure
local notation "τ"=> P.cartage j χ[j]
variable (F D:P.Apron)
include J
local notation "μ[" r "]"=> usher (0:Vantage) r
local notation "W"=> usher F D
local notation "β[" r "]"=> P.commonWell a x W μ[r]
lemma singleP {I:Type*}(A:I→P.Apron)(t:I→Vantage)(i:I): P.commonWell a x A t [i]= inner ℂ Ω[j] (flashY x (A i) j):=by
 rw [P.common_cult a x A t _ J (List.Perm.refl [i]) (show P.Turnstile j A [i] t from List.pairwise_singleton ..)]
 let u:=t i; unfold memorial; rw [←rector_view Ψ[j] Ω[j] _ _ _ (P.heaven_hot j χ[j]) 0]; change inner ℂ Ω[j] (E[j] _ (V[j] u _ Ω[j]))=_; rw [← OS.Semigroup.swing, P.heaven_hot,P.tableMaps]; exact (congrArg₂ (inner ℂ) (P.cart_empty j χ[j] u).symm rfl).trans (P.inner_pay j χ[j] u _ (flashY x (A i) j))
omit J
lemma lit_alone : inner ℂ (glareY x F j) Ω[j] = inner ℂ Ω[j] (flashY x F j):=by change inner ℂ ((V[j] 0 (F.engine P j χ[j])).adjoint Ω[j]) Ω[j] = _; rw [ContinuousLinearMap.adjoint_inner_left,P.tableMaps,P.cart_zero]; rfl
include J g
local notation "c"=> (F.realWidth P j+D.realWidth P j)
local notation "H₀[" r "]"=> Real.toNNReal (r j-c)
lemma pair_mix {I:Type*}{L:Filter I}(r:I→ Vantage)(h:Tendsto (fun i=> (r i) j) L atTop)(v:∀ k:Axis,k≠j→ Tendsto (fun i=> |(r i) k|) L atTop): Tendsto (fun i=>(β[r i]) [false,true]) L (𝓝 ((β[0]) [false]*(β[0]) [true])):=by
 let q(i:I):=Real.toNNReal (r i j-c); have ht:Tendsto q L atTop:= by apply Filter.tendsto_atTop.mpr; intro k; filter_upwards [h.eventually (eventually_ge_atTop (c+k))] with i y; change (k:ℝ)≤(q i:ℝ); unfold q; simp only [Real.coe_toNNReal']; apply le_max_of_le_left; linarith
 rw [singleP j x J,singleP j x J]; change Tendsto _ _ (𝓝 (inner ℂ Ω[j] (flashY x F j)*inner ℂ Ω[j] (flashY x D j))); rw [← lit_alone]; refine (joint_mix j x J _ _ q r ht v g).congr' ?_; filter_upwards [h.eventually (eventually_gt_atTop c)] with i t; exact (avail_cross x F D j (r i) J t).symm -- tune
lemma pairs_cluster {I:Type*}{L:Filter I}(r:I→ Vantage)(h:Tendsto (fun i=> (r i) j) L atTop)(v:∀ k:Axis,k≠j→ Tendsto (fun i=> |(r i) k|) L atTop): Tendsto (fun i=>(β[r i]) [false,true] - (β[r i]) [false]*(β[r i]) [true]) L (𝓝 0):=by
 have he(i:I)(k:Bool): (β[r i]) [k]= (β[0]) [k]:= (singleP j x J ..).trans (singleP j x J ..).symm -- syntax
 simp_rw [he]; simpa only [sub_self] using (pair_mix j x J g F D r h v).sub_const ((β[0]) [false]*(β[0]) [true])
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pairs_cluster
