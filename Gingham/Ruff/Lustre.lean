import Gingham.Ruff.TeaRoom
import YM.SU5.FiniteGaugeData.Tapestry.Neutral
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry

variable (S:Finset Cover)(K:Calibration)(U:Set PairsC)(C D:ℝ)(H:Bool)
def Flora (H:Bool)(F:Buffered.Family K)(C:ℝ):Prop :=
    (∀ m x, ‖F m x‖ ≤ C) ∧ Neutral K F ∧ SatinSkin K F ∧
       (H=true→∀m,pearl (F m))

open Nacre
lemma rotating {N:Side}(r:Seat N→E):
 Continuous (twist (quantU (tradew N r))) :=by
 apply Isometry.continuous; refine isometry_iff_dist_eq.mpr fun _ _=>?_
 rw [dist_eq_norm,dist_eq_norm,←map_sub,twist_norm]

lemma stilled {f:ℕ→Buffered.Family K}{g:Buffered.Family K}
 (h:∀i,Flora K H (f i) C)
 (t:∀ m x,Tendsto (fun i=>f i m x) atTop (𝓝 (g m x))): Flora K H g C:=by
 refine ⟨fun m x=>le_of_tendsto (t m x).norm
            (Eventually.of_forall fun i=>(h i).1 m x),
    ?_, ?_, ?_⟩
 · intro m r x
   have v:=t m (simultaneous r x)
   apply tendsto_nhds_unique_of_eventuallyEq v
     (?_ :Tendsto (fun i=>twist (quantU (tradew _ r)) (f i m x)) atTop _) (Eventually.of_forall
       fun i=>(h i).2.1 m r x)
   exact (rotating r).continuousAt.tendsto.comp (t ..)
   -- ?
 · intro m x y v
   exact tendsto_nhds_unique_of_eventuallyEq (t m x) (t m y)
       (Eventually.of_forall fun i=>(h i).2.2.1 m x y v)
 · intro a m x
   let J:=FC (Single (K.c m))
   let Z := (1:J)
   let p:=Submodule.span ℂ {Z}
   have he: g m x∈p :=
      p.closed_of_finiteDimensional.mem_of_tendsto (t m x)
        (Eventually.of_forall fun i=>Submodule.mem_span_singleton.mpr ((h i).2.2.2 a m x|>.elim
        fun c h=>⟨c,h.symm⟩))
   obtain ⟨z,r⟩:=Submodule.mem_span_singleton.mp he
   exact ⟨_,r.symm⟩

def Rose :Set (Swatch S):=
 {z| (∀ j,Steady S U C D (daub S (z j))) ∧ Flora K H (render S K z) C}
-- Lean include params
#print Rose

lemma ink_quill {q:ℕ→Swatch S}{x:Swatch S}(p:Tendsto q atTop (𝓝 x)) (m y):
 Tendsto (fun i=>render S K (q i) m y) atTop (𝓝 (render S K x m y)):=by
 let f: Swatch S →ₗ[ℂ] FC (Single (K.c m)) :=
    (LinearMap.proj y).comp (appear S K m)
 let c:=f.mkContinuous (spread S) (fun z=>appearLe S K m z y)
 exact c.continuous.continuousAt.tendsto.comp p

lemma shut : IsClosed (Rose S K U C D H):=by
 apply IsSeqClosed.isClosed;intro f g h l
 have he(i): (∀ j,Steady S U C D (daub S (f i j))) ∧ Flora K H (render S K (f i)) C:=h i
 refine ⟨fun j=>(isClosed_steady S U C D j).mem_of_tendsto l
             (Eventually.of_forall fun i=>(he i).1 j),
         stilled K C H (fun i=>(he i).2) (ink_quill S K l)⟩
lemma fenced(c:0≤C)(d:0≤D):IsCompact (Rose S K U C D H):=by
 apply TotallyBounded.isCompact_of_isComplete _ (shut S K U C D H).isComplete
 rw [←Subtype.range_val (s:=Rose S K U C D H)]
 exact lacelike S U _ c d (fun i j=>i.property.1 j)
lemma rose_origin(c:0≤C)(d:0≤D): (0:Swatch S)∈ Rose S K U C D H:=by
 refine ⟨fun i=>?_,?_⟩
 · have h:daub S ((0:Swatch S) i)=0:=rfl
   rw [h]
   exact ⟨fun x=>(show ‖(0:ℂ)‖ ≤ C from by simpa),fun _ _=>rfl,fun _ _ _ _=>by simp; positivity⟩
 rw [map_zero]
 exact ⟨by simpa, fun i t x=>(map_zero _).symm, fun _ _ _ _=>rfl, fun _ _ _=>⟨0,(zero_smul ..).symm⟩⟩
