import SatinFixedContrastNovember4
import SatinThinFusionApplied
/-!
# Milestone 15.I. Finite bounds and strong smeared convergence of general profiles

Actual price estimates. We are in `Spine.Ellis` on this character. No identification of raw
individual transverse-translated values with their projections. With weight zero over
remaining positions, projection enters by a **limit** (`macroRiemann`), strong
in the enclosing Hilbert. Proof extends that for scalars on the vacuum in `-Sweep`.
Taking at any wall qualification μ>0. The `max` is ONLY to evaluate outside
support of these tests. Same value at *every* point of support.
-/
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
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "Γ"=> P.truck 3 ξ
local notation "γ"=> P.cartage 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "λ'"=> P.enter 3 ξ
local notation "E"=> (S).E

section for_one
variable (A:P.Apron)(h:P.birthF 3 A.s A.F)(F:SampleDose)(μ:ℝ)(t:ℕ)
-- only μ-specific clamp off support -- positive all-T on x enables this
variable (V:ℝ→P.ColorHil 3 (P.advocate 3 x 3))(Z:ℝ→P.ManyF 3 (P.advocate 3 x 3))
local notation "p" => P.meshPose t
local notation "u" => P.vtile t
local notation "α"=> P.activation t F
local notation "ε"=> P.usedGrid t F

def queryGrid:H := ∑ i∈ε,α i • Γ (u i) (V (max μ (p i 3)))

def readProfile:G:= DoseTravel.beam (G) F (fun v=> γ v (Z (max μ (v 3)))) -- scope
local notation "T"=> P.queryGrid x F μ t V
private lemma sum_at_tick (X:Hilbert)(f:Vantage→X)(U:Cover → X.Op):
    poseApprox X (fun z:Vantage=>(F.val z:ℂ) • f z) U (P.macroStep t) =∑ i∈ ε, α i • U i (f (p i)):=by
  let g:=fun i:Cover=> U i ((F.val (p i):ℂ) • f (p i))
  have he(i:Cover)(x:i∉ε): g i=0:= by
    have hu : F.val (p i)=0 := by by_contra q; exact x ((P.usedPose t F i).2 (subset_closure q))
    unfold g; rw [hu,Complex.ofReal_zero,zero_smul,map_zero]
  refine (room_price (P.macroStep t) (P.macroStep_pos t) g (ε) he).2.trans ?_
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i h
  unfold g; rw [map_smul,
    show Fintype.card Axis=4 by rfl, ← Complex.coe_smul ((P.macroStep t)^4), smul_smul]
  push_cast [activation]; rfl

-- macro projection cost
lemma queries_cont (J:P.Ellis 3 x)(B:Positive (S) V) (u':0<μ)(z:∀ t:ℝ,0<t→ π' (V t)= Z t):
    Tendsto (fun t=> P.queryGrid x F μ t V) atTop (𝓝 (λ' (P.readProfile x F μ Z))):= by
 let A(qz:Vantage):= max μ (qz (3:Axis)); have hA(qz:Vantage):0<A qz:= u'.trans_le (le_max_left ..)
 let U:= V∘ A; let X(qz:Vantage):=(F.val qz:ℂ) • U qz; let q(qz:Vantage):= γ qz (π' (X qz))
 have he: HasCompactSupport X:= F.budget.mono (fun i w t=> w ((congrArg (fun b:ℝ=> (b:ℂ) • U i) (show F.val i=0 from t)).trans (zero_smul ℂ _)))
 have hu:Continuous U:= continuous_iff_continuousAt.mpr (fun i=> (Positive.cont (S) V B (hA i)).comp (f:=A) ((continuous_const.max (continuous_apply _)).continuousAt))
 have ht: Continuous X:= (Complex.continuous_ofReal.comp F.smooth.continuous).smul hu
 rw [show P.readProfile x F μ Z= ∫ qz:Vantage,q qz from integral_congr_ae (Eventually.of_forall fun i:Vantage=> by
    change (F.val i:ℂ) • γ i (Z (A i))= γ i (π' ((F.val i:ℂ) • V (A i)))
    rw [map_smul,map_smul,z _ (hA i)])]
 exact (P.macroRiemann x 3 J X he ht).congr fun i=> sum_at_tick P _ _ (H) U _

lemma query_tick_distance (B:Positive (S) V)(u':0<μ)(q:∀ x∈tsupport F.val,μ≤ x (3:Axis)):
   dist T (P.thinGridKet x t A h F) ≤ (∑ i∈ ε,‖α i‖)* ‖P.cradleH x A h μ - V μ‖ := by
 rw [dist_comm,dist_eq_norm, thinGridKet, queryGrid, ← Finset.sum_sub_distrib, Finset.sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i r=> ?_)
 have z:μ≤ p i 3:= q _ ((P.usedPose t F i).mp r); let U:= Γ (u i); let k:= E ((p i 3-μ).toNNReal)
 have hu (x): ‖U x‖=‖x‖:= P.truck_norm ..
 let v:= P.cradleH x A h; have ht:v (p i 3)=k (v μ):= cradlePositive (S) _ _ _ u' z
 change ‖α i • U (v (p i 3))-α i • U (V _)‖ ≤ ‖α i‖ * ‖v μ-V μ‖
 rw [←smul_sub, norm_smul, ht, max_eq_right z, B _ _ u' z, ←map_sub U, hu]
 rw [←map_sub k]; exact mul_le_mul_of_nonneg_left ((k.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((S).shrinks _))) (norm_nonneg _)

lemma query_cont_distance (J:P.Ellis 3 x)(B:Positive (S) V) (u':0<μ)(z:∀ t:ℝ,0<t→ π' (V t)= Z t)
    (q:∀ x∈tsupport F.val,μ≤ x (3:Axis)):
    dist (P.readProfile x F μ Z) (P.thinKet x A h F) ≤ (∫ x, ‖F.val x‖)* ‖P.cradleH x A h μ - V μ‖:= by
 rw [← (λ').dist_map]; exact le_of_tendsto_of_tendsto ((P.queries_cont x F μ V Z J B u' z).dist (P.thin_to_ket x A h F J)) ((P.thin_activation_abs F).mul_const _) (Eventually.of_forall fun i=> P.query_tick_distance x A h F μ i V B u' q)
end for_one
variable (A:ℕ→P.Apron)(h:∀ i,P.birthF 3 (A i).s (A i).F)(F:SampleDose)(μ:ℝ)
variable (V:ℝ→P.ColorHil 3 (P.advocate 3 x 3))(Z:ℝ→P.ManyF 3 (P.advocate 3 x 3))(J:P.Ellis 3 x)(B:Positive (P.physicalEnergy 3 (P.advocate 3 x 3)) V) (u':0<μ)(z:∀ t:ℝ,0<t→ P.wealth 3 (P.advocate 3 x 3) (V t)= Z t)
    (q:∀ x∈tsupport F.val,μ≤ x (3:Axis))(W:Tendsto (fun i=>P.cradleH x (A i) (h i) μ) atTop (𝓝 (V μ)))
include J B u' z q W
lemma dynamic_grid_ket (t:ℕ→ℕ)(g:Tendsto t atTop atTop):
    Tendsto (fun i=> P.thinGridKet x (t i) (A i) (h i) F) atTop (𝓝 (λ' (P.readProfile x F μ Z))):= by
 apply ((P.queries_cont x F μ V Z J B u' z).comp g).congr_dist; have hq:= ((P.thin_activation_abs F).comp g).mul (tendsto_iff_norm_sub_tendsto_zero.mp W); rw [mul_zero] at hq
 exact squeeze_zero (fun _=>dist_nonneg) (fun i=>P.query_tick_distance x _ _ _ _ _ _ B u' q) hq
lemma dynamic_cont_ket :
    Tendsto (fun i=> P.thinKet x (A i) (h i) F) atTop (𝓝 (P.readProfile x F μ Z)):= by
 apply (tendsto_const_nhds (x:=P.readProfile x F μ Z)).congr_dist; have hq:= (tendsto_iff_norm_sub_tendsto_zero.mp W).const_mul (∫ x, ‖F.val x‖); rw [mul_zero] at hq
 exact squeeze_zero (fun _=>dist_nonneg) (fun i=>P.query_cont_distance x _ _ _ _ _ _ J B u' z q) hq
omit J B u' z q W
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.query_tick_distance
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.query_cont_distance
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.dynamic_grid_ket
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.dynamic_cont_ket
