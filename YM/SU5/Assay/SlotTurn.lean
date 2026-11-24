import YM.SU5.Assay.RawSlot
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
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Turning, paying quadrature. Compression on **sum**, not product! -/
variable (t:ℕ)(F:SampleDose)(a b:ℝ)(D:P.Apron)
local notation "Q"=>P.usedGrid t
local notation "α"=>P.activation t
local notation "ν"=>P.vtile t
local notation "y"=>P.meshPose t
local notation "σ"=>P.rawSlot j x
local notation "θ'"=>P.reprise j x
local notation "g"=>opposeQ j
local notation "β"=>P.base j x
lemma flip_grid:
 Q (flipDose F j)=(Q F).image g:=by
 let S':=Q F;let G:=flipDose F j;let L:=Q G
 have hp(k:Cover): (g) k∈L ↔ k∈S':= by
   unfold L S'; rw [P.usedPose,P.usedPose,P.tile_reflect t k j, show tsupport G.val=_ from flipBudget F j]; change opposeR j (opposeR j (y k))∈ tsupport F.val ↔ _; rw [reflectPose_twice]
 exact Finset.ext (fun k=> by
   rw [Finset.mem_image]; constructor
   · intro h; exact ⟨(g) k,(hp ((g) k)).1 (Eq.mpr (congrArg (· ∈ L) (reflectInt_twice j k)) h), reflectInt_twice j k⟩
   rintro ⟨p,h,rfl⟩; exact (hp _).2 h)
lemma flip_activation (k:Cover): α (flipDose F j) ((g) k)=α F k:=by
 unfold activation; rw [P.tile_reflect,show (flipDose F j).val (opposeR j (y k))= F.val (y k) from congrArg F.val (reflectPose_twice j (y k))]
lemma flip_raze (k:Cover): star (P.raze j x D a b (ν k))= P.raze j x (D.kiss P j) (-b) (-a) (ν ((g) k)):=by
 let u:= (D.kiss P j).engine P j x
 have v:P.charter j x (ν k) u= P.charter j x (ν ((g) k)) u:= P.charter_same _ _ (by
    intro i z;apply Subtype.ext;change (y k) i=y _ i;rw [P.tile_reflect];exact (if_neg z).symm) _
 have q:P.laysM (ν ((g) k)) j = - P.laysM (ν k) j:=by
   change y _ j = - y k j; rw [P.tile_reflect]; exact if_pos rfl
 rw [P.raze_star,P.raze_base,v,q]
 simp only [sub_eq_add_neg,neg_neg]; -- order
 rw [add_comm b ,add_comm (-a)] <;> rfl
lemma rawSlot_flip : star (σ t D a b F)=σ t (D.kiss P j) (-b) (-a) (flipDose F j):=by
 rw [P.rawSlot_raze,P.rawSlot_raze,star_sum,P.flip_grid,Finset.sum_image ((reflectInt_twice j|>Function.Involutive.injective).injOn)]
 simp only [star_smul,P.flip_raze,P.activation_real,P.flip_activation]

lemma reprise_sum {ι:Type*}(s:Finset ι)(f:ι→X): θ' (∑i∈s,f i)= ∑i∈s, θ' (f i):=by
 ext1 u
 change R ((∑i∈s,f i) (E u))=_
 rw [_root_.sum_apply,_root_.sum_apply,map_sum];rfl
lemma reprise_slot : θ' (σ t D a b F)=
 ∑i∈Q F, α F i • P.slot j x (β D) a b (y i):=by
 simp_rw [P.rawSlot_raze,P.reprise_sum,P.reprise_smul,P.raze_slot]
 rfl
lemma sand_sum {ι:Type*}(s:Finset ι)(f:ι→X)(a b:ℝ):(U).sand (∑i∈s,f i) a b=∑i∈s,(U).sand (f i) a b:=by unfold sand;simp_rw [mul_sum,sum_mul]
variable {P j x a b F D}{l r:ℝ}
lemma rawSlot_outer (w:Walled j F a b (D.realWidth P j))(h:l≤a)(q:b≤r):σ t D l r F=(U).sand (σ t D a b F) (a-l) (r-b):=by
 rw [P.rawSlot_raze,P.rawSlot_raze,P.sand_sum];refine Finset.sum_congr rfl fun i v=>?_
 obtain ⟨u,z⟩:= Walled.used w P v
 rw [P.raze_step j x D (ν i) u.le z.le h q,sand_smul]
lemma rawSlot_paid (D:P.Apron)(a b:ℝ)(F:SampleDose): ‖σ t D a b F‖≤ P.gridMass F t*‖D.engine P j x‖:=
 P.sampler_cost j x t _ _ (P.laid_cost j x D a b F)
lemma rawSlot_charge (w:Walled j F a b (D.realWidth P j))(h:l≤a)(q:b≤r): ‖σ t D l r F‖ ≤ ‖σ t D a b F‖:= by
 rw [rawSlot_outer t w h q];exact (U).sand_pay ..
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
