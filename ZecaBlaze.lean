import ZecaGray
import YM.SU5.Six.PressSmear
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
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
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open scoped TensorProduct
open Six
local notation "κ"=> P.calibration
local notation "R"=> ruler P.par.block
local notation "H"=> P.large
local notation "Y"=> P.run
local notation "Φ"=> P.stateSpace j x
local notation "X"=> P.PortionHil j x
local notation "σ"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "R₀"=> P.history
local notation "J"=> P.Slabs j
local notation "T"=> P.Test


variable (s w:ℕ)


local notation "Λ"=> P.par
local notation "δ"=> precisionAt P.par s
local notation "μ"=> ((κ).ℓ:ℤ)

/-- Real bill width of pitch slab w ticks -/
abbrev pen(t:ℤ):= bell (timeMesh P.par) s t

lemma pin_fit (u:ℤ)(S:Finset Cover)
 (p:∀ y∈P.pinFoot s S,P.pen s u ≤ y j ∧ y j ≤ P.pen s ((w:ℤ)+u)):
 Between κ j 0 (R*w) (plow κ j (-u) S):=by
 have q:Between κ j (R*u) (R*((w:ℤ)+u)) S:=by
    intro x h
    let t (σ':ℤ):Vantage:= fun i=> markZ Λ s (x i+σ') / 2
    have m:0<δ:=positiveScale ..
    have hm(σ':ℤ):2*t σ' j=markZ Λ s (x j+σ'):=by unfold t; ring
    have g{σ':ℤ}(e:(|σ'|:ℤ) ≤ μ): t σ'∈P.pinFoot s S:=by
       refine ⟨x,h,fun i=>?_⟩
       change |δ * (2 * (markZ Λ s (x i+σ')/2)) - (x i:ℝ)| ≤ ((κ).ℓ:ℝ)
       rw [markZ,Int.cast_add, show ∀v:ℝ, δ*(2*(v/δ/2))=v from
          fun v=> by field_simp,
          add_sub_cancel_left]
       exact_mod_cast e

    let c(σ':ℤ):ℝ:=2* P.pen s σ'
    have d(σ':ℤ): c σ'=markZ Λ s (R*σ'):=Apron.distance_mark P s σ'
    have o: StrictMono (markZ Λ s) :=fun a b h=> div_lt_div_of_pos_right (by exact_mod_cast h) m
    have l:R*u ≤ x j + -μ:=by
       apply o.le_iff_le.mp
       rw [← d,← hm]; exact mul_le_mul_of_nonneg_left ((p _ (g (by simp))).1) (by norm_num)
    exact ⟨by omega, o.le_iff_le.mp ((hm μ).symm.trans_le 
      ((mul_le_mul_of_nonneg_left ((p _ (g (by simp : (|μ|:ℤ) ≤ μ))).2) (by norm_num: (0:ℝ)≤2))
       |>.trans_eq (d _)))⟩
 have h:=q.relocate κ j (-u)
 rw [show ruler (κ).B=R from rfl] at h
 convert h using 1
 · ring
 · ring

-- shift raw Sensors preserving sensing. implicit args
lemma sensing_trip (u:ℤ)(Q:Bool)(S:Finset Cover)(f:T)(h:f∈P.sensing S s Q):
 P.shifts j u f∈ P.sensing (plow κ j u S) s Q:=by
 let α:=P.sensing (plow κ j u S) s Q
 -- span induction
 refine Submodule.span_induction (p:=fun f _=> P.shifts j u f∈α) (fun f v=>?_)
    (by rw [map_zero]; exact α.zero_mem) (fun _ _ _ _ a b=>by rw [map_add]; exact α.add_mem a b)
    (fun c _ _ a=>by rw [map_smul]; exact α.smul_mem _ a) h
 obtain ⟨a,b,d,p,q,e,h,t⟩:=v

 exact Submodule.subset_span (show _∈_ from
    ⟨_,_,_,Finset.union_subset
       (Finset.image_subset_image (Finset.subset_union_left.trans p)) (Finset.image_subset_image (Finset.subset_union_right.trans p)),
       Finset.image_subset_image q,P.pin_relocate _ _ _ j u e,relocate_dressed κ Q a b d j u h,P.shifts_keep j u t⟩)

variable (hw:0<w)(u:ℤ)(D:P.Apron)(Q:Bool)(h:P.Sensor D Q)(b:D.s ≤ s)
local notation "C"=> P.pith j x s w hw
local notation "F"=>P.shifts j (-u)

def Lunette(p:Vantage):Prop:=
 P.pen s u + D.realWidth P j ≤ p j ∧ p j + D.realWidth P j ≤ P.pen s ((w:ℤ)+u)

include h b in
lemma shell_issued (k:Cover)(p:P.Lunette j s w u D (P.meshPose s k)):
 P.straight j s w (F (P.issuing s D k)) ∧ C (F (P.issuing s D k))=0:=by
 let U:= P.plotSet s D k
 have r:=P.pin_fit j s w u U (fun y a=>by
    have v:= P.inside_now s k D b a
    obtain ⟨d,e⟩:= abs_le.mp (v j)
    constructor
    · linarith only [p.1,d]
    · linarith only [p.2,e])
 have t:=P.sensing_trip j s (-u) Q U (P.issuing s D k) (P.issuance_senses _ _ _ D b h)
 exact ⟨(P.straight_ok ..).mpr ⟨_,r,P.shifts_support j (-u) _ (P.issuing_support s k D)⟩,
          P.shells j x s w hw Q _ r _ t⟩

private lemma help {W:Type}[AddCommGroup W][Module ℂ W](z:ℂ):z•(0:W)=0:=smul_zero _
include h b in
lemma shell_smear (L:SampleDose)(p:∀ y∈tsupport L.val,P.Lunette j s w u D y):
 P.straight j s w (F (P.prepared s D L)) ∧ C (F (P.prepared s D L))=0:=by
 have t(k:Cover)(v:k∈P.usedGrid s L):=P.shell_issued j x s w hw u D Q h b k (p _ ((P.usedPose s L k).1 v))
 unfold prepared; simp_rw [map_sum,map_smul]
 exact ⟨(P.Cellar ..).sum_mem (fun i v=> (P.Cellar ..).smul_mem _ (t i v).1),
        sum_eq_zero (fun k v=>by rw [(t k v).2]; exact help (W:=P.PomeOp j x) _)⟩
