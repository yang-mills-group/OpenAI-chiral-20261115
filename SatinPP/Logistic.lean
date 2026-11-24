import SatinPP.Lacuna
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
variable (P:Spine)(x:P.Spectrum0 3)

local notation "ξ"=>P.advocate 3 x 3
local notation "H"=>P.ColorHil 3 ξ
local notation "S"=>P.physicalEnergy 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "E"=>(S).E
local notation "Υ"=> P.shifts 3
variable (n:ℕ)
local notation "ϐ"=>bell (timeMesh P.par) n

local notation "τ"=>P.meshPose n 
local notation "Vv"=>P.vtile n
variable (A:P.Apron)(F:SampleDose)
local notation "w"=> A.realWidth P 3
local notation "G'"=>P.usedGrid n F
local notation "α"=>P.activation n F

local notation "T"=> P.truck 3 ξ
lemma jacket_reversal (B:(H).Op)(a b:ℝ): -- not valid reversal name
    star (jacket (S) a b B)= jacket (S) b a (star B):=by
 change star (E a.toNNReal * B * E b.toNNReal)= E _ * star B * E _
 have H'(r):star ((P.physicalEnergy 3 ξ).E r)=E r:=(S).sym r
 rw [star_mul,star_mul,H',H']; exact (mul_assoc ..).symm

variable {P x n F A}
variable {l u:ℝ} (e:P.birthF 3 A.s A.F)
lemma entryLater {k:Cover} (h:w ≤ τ k 3-l):
   P.panelOne x n A l u k (ω)= T (Vv k) (P.cradleH x A e (τ k 3-l)):=by
 unfold panelOne locket
 rw [charter_inside, jacket_ω]
 exact P.thin_charter_shift x n A e k _ h
lemma entryEarly {k:Cover} (h:w ≤ u-τ k 3):
   star (P.panelOne x n (A.kiss P 3) l u k) (ω)= T (Vv k) (P.cradleH x A e (u-τ k 3)):=by
 unfold panelOne locket
 rw [charter_inside,jacket_reversal, ContinuousLinearMap.star_eq_adjoint,
     P.charter_opposed,jacket_ω]
 exact P.thin_charter_shift x n A e k _ h
#print activation
#check star_sum
#check star_smul


lemma run_ask (h:P.SetPanel A F l u)
   {D:Vantage→ℝ}(r:∀y∈tsupport F.val,D y=y (3:Axis)-l):
 P.gridRun x n A F l u (ω) = P.askW x D F n (P.cradleH x A e):=by
  rw [gridRun, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k i=> ?_
  have a:=(P.usedPose n F k).mp i
  rw [ContinuousLinearMap.smul_apply, entryLater e (h _ a).1,← r _ a]
lemma run_asked (h:P.SetPanel (A.kiss P 3) F l u)
   {D:Vantage→ℝ}(r:∀y∈tsupport F.val,D y=u-y (3:Axis)):
 star (P.gridRun x n (A.kiss P 3) F l u) (ω) = P.askW x D F n (P.cradleH x A e):=by
  rw [gridRun, star_sum,ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k i=> ?_
  have a:=(P.usedPose n F k).mp i
  rw [star_smul,ContinuousLinearMap.smul_apply, entryEarly e (h _ a).2,←r _ a]
  congr 1
  simp [activation]


lemma strict_gap (h:Strict l u F)(lu:l<u):∃ μ:ℝ,0<μ ∧ l+μ≤u ∧
    ∀ p∈tsupport F.val, μ ≤ p (3:Axis)-l ∧ μ ≤ u-p 3:=by
 let N:=tsupport F.val
 let d(p:Vantage):=min (p (3:Axis)-l) (u-p 3)
 have f:Continuous d:= ((continuous_apply _).sub continuous_const).min (continuous_const.sub (continuous_apply _))
 have b(p)(v:p∈N):0<d p:=lt_min (sub_pos.mpr (h p v).1) (sub_pos.mpr (h p v).2)
 by_cases i:Set.Nonempty N
 · have r:IsCompact N:=F.budget
   obtain ⟨q,v,H'⟩:=r.exists_isMinOn i f.continuousOn
   refine ⟨min (u-l) (d q), lt_min (sub_pos.mpr lu) (b q v), by linarith only [min_le_left (u-l) (d q)],
      fun a x => le_min_iff.mp ((min_le_right ..).trans (H' x))⟩
 exact ⟨u-l,sub_pos.mpr lu,by linarith,fun p v=> (i ⟨p,v⟩).elim⟩

lemma strict_ready (h:Strict l u F)(lu:l<u)
 {C:ℕ→P.Apron}
 (g:Tendsto (fun i:ℕ=>(C i).realWidth P 3) atTop (𝓝 0)):
 ∀ᶠ i in atTop, P.SetReady (C i) F l u:=by
 obtain ⟨m,e,r,d⟩:=strict_gap h lu

 refine (g.eventually (eventually_lt_nhds (half_pos e))).mono fun i j=>⟨?_,fun p v=>?_⟩
 · linarith
 obtain ⟨b,c⟩:=d p v
 constructor <;> linarith
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
