import SatinPP.WakeWave
import SatinThinQuizSignal
import SatinPP.Pinch
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
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
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

local notation "H"=> P.ColorHil 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Δ"=> P.truck 3 ξ
local notation "ω"=> P.colorZero 3 ξ
variable (A:P.Apron)(eA : P.birthF 3 A.s A.F)(t:ℕ)

variable (F:SampleDose)
local notation "ϱ"=>P.thinGridRay x t A eA
local notation "ν"=> P.thinGridKet x t A eA
local notation "πₛ"=> P.meshPose t
local notation "ξₜ"=> P.usedGrid t
local notation "α"=> P.activation t
local notation "α!"=> P.macroStep t ^ 4
private lemma act_false (i:Cover)(h:i ∉ ξₜ F):α F i=0:=by
 have z: F.val (πₛ i)=0:= by by_contra g;exact h ((P.usedPose ..).2 (subset_closure g))
 unfold activation; rw [z,mul_zero,Complex.ofReal_zero]
lemma biggerGrid (D':Finset Cover)(h:ξₜ F ⊆D'):
 ν F=∑ i∈D',α F i • ϱ i:=
 Finset.sum_subset h (fun i _ e=>by rw [P.act_false t F i e,zero_smul])
def humidity :ℝ := ∑ i∈ξₜ F,‖α F i‖
lemma humidity_big (D':Finset Cover)(h:ξₜ F ⊆D'):
    P.humidity t F=∑ i∈D',‖α F i‖:=
 Finset.sum_subset h (fun i _ e=>by rw [P.act_false t F i e,norm_zero])

private lemma gridCap {q:ℝ}(h:0<q){i:Cover}(y:q≤πₛ i 3):‖ϱ i‖ ≤ ‖P.cradleH x A eA q‖:=by
 let r:=πₛ i 3; let E':=(S).E
 unfold thinGridRay cradleH
 rw [P.truck_norm,show r.toNNReal=(r-q).toNNReal+q.toNNReal from by rw [← Real.toNNReal_add (sub_nonneg.mpr y) h.le, sub_add_cancel],(S).time, ContinuousLinearMap.comp_apply]
 exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _))

lemma gridDiff (U F':SampleDose){q C:ℝ}(h:0<q)(g:0≤C)
 (h₁:forwardSite F q)(h₂:forwardSite F' q)
 (l:∀p,|F.val p-F'.val p|≤C*U.val p):
 dist (ν F) (ν F') ≤ P.humidity t U * (C * ‖P.cradleH x A eA q‖):=by
 let D':= ξₜ U ∪ (ξₜ F ∪ ξₜ F')
 rw [P.biggerGrid x _ _ t F D' ((Finset.subset_union_left).trans Finset.subset_union_right),
    P.biggerGrid x _ _ t F' D' ((Finset.subset_union_right).trans Finset.subset_union_right),
    P.humidity_big t U D' Finset.subset_union_left,dist_eq_norm,←sum_sub_distrib,sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
 rw [←sub_smul,norm_smul]


 by_cases d:q≤πₛ i 3
 · rw [← mul_assoc]
   apply mul_le_mul _ (P.gridCap x A eA t h d) (norm_nonneg _) (by positivity)
   unfold activation
   rw [←Complex.ofReal_sub,←mul_sub,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,mul_assoc, mul_comm |U.val (πₛ i)|]
   exact mul_le_mul_of_nonneg_left ((l _).trans (mul_le_mul_of_nonneg_left (le_abs_self _) g)) (abs_nonneg _)
 have p:(i ∉ ξₜ F)∧(i ∉ ξₜ F'):=⟨fun m=> d (h₁ _ ((P.usedPose ..).1 m)),fun m=>d (h₂ _ ((P.usedPose ..).1 m))⟩
 rw [P.act_false _ _ _ p.1,P.act_false _ _ _ p.2,sub_self,norm_zero,zero_mul]; positivity


lemma coast_equal {k:Cover}(u:k 3=0)(D':Finset Cover)(h: ∀ i∈ξₜ F,i+k∈D'):
 Δ (P.vtile t k) (ν F)=∑ i∈D', α F (i-k) • ϱ i:=by
 let D₁:=D'.image (fun i=>i-k)
 have e:ξₜ F⊆D₁:=fun i f=> Finset.mem_image.mpr ⟨i+k,h i f,add_sub_cancel_right .. ⟩
 rw [P.biggerGrid x A eA t F D₁ e, show D₁=D'.image (fun i=>i-k) from rfl,Finset.sum_image (by intro a _ b _ z;exact sub_left_inj.mp z),map_sum]
 refine sum_congr rfl fun i _=>?_
 have f:πₛ (i-k) 3=πₛ i 3:=by simp [P.pose_w,u]
 rw [map_smul];unfold thinGridRay;rw [f,←ContinuousLinearMap.comp_apply (Δ (P.vtile t k)), ←P.truck_paves,
    ←P.tile_add,add_comm,sub_add_cancel]
lemma coast_bike (k:Cover)(z:Vantage)(d:ℝ)(u:k 3=0)(p: d • z = πₛ k):
 ν (bike z F d)=d⁻¹ • (ν F - Δ (P.vtile t k) (ν F)):=by
 let D₁:=ξₜ F∪(ξₜ F).image (fun i=>i+k)
 let B:=bike z F d

 let L:=D₁∪ξₜ B
 rw [P.coast_equal x _ _ t F u L (fun i f=>Finset.subset_union_left (Finset.subset_union_right (Finset.mem_image.mpr ⟨i,f,rfl⟩))),
    P.biggerGrid x A eA t F L (Finset.subset_union_left.trans Finset.subset_union_left),
    P.biggerGrid x A eA t B L Finset.subset_union_right,
    ←sum_sub_distrib,smul_sum]
 refine sum_congr rfl fun i _=>?_
 rw [←sub_smul];unfold activation
 have r:πₛ (i-k)=πₛ i-πₛ k:=by ext j; rw [Pi.sub_apply,P.pose_w,P.pose_w,P.pose_w,Pi.sub_apply,Int.cast_sub];ring
 rw [r, show B.val (πₛ i)=(F.val (πₛ i)-F.val (πₛ i-d • z))/d from rfl, p,
    ←Complex.ofReal_sub,Complex.coe_smul,Complex.coe_smul,smul_smul,
    ←mul_sub,←div_eq_inv_mul,mul_div_assoc]
/-- signed step in matter/continuum unit -/
def gradeZ (t:ℕ)(n:ℤ):ℝ:=(n:ℝ)*P.macroStep t
def wheel(j:Axis)(n:ℤ):Cover:=Function.update 0 j n
lemma cycle_grid (j:Axis)(h:j≠3)(n:ℤ):
 ν (bike (footfall j) F (P.gradeZ t n))=
 (P.gradeZ t n)⁻¹ • (ν F - Δ (P.vtile t (wheel j n)) (ν F)):=by
 refine P.coast_bike x A eA t F _ _ _
    (show wheel j n 3=0 from by simp [wheel,h.symm]) ?_
 funext i
 simp [footfall,gradeZ,P.pose_w,aglow,wheel,Function.update_apply]
#print axioms cycle_grid
