import Gingham.Ruff.Lustre
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


variable {p:BudgetPoint}{c e C:ℝ}{S:Finset Cover}{H:Bool}
variable {N:Side}
structure Opening (p:BudgetPoint)(C:ℝ)(H:Bool)(F:Mark N):Prop where
 room : Premier F 0 p C
 strong(x): nub (Tset N) (F x) ≤ C
 only : H=true → pearl F
 front(x y): x.1=y.1→ F x=F y

lemma matinBud(w:Bool){M:Orbit N→OP N} (v:Matinee p 0 e c M) :
     Opening p (costGlass e c) (!w) (cupN w M):=by
 refine ⟨wear3 v w,fun x=>?_,fun a x=>?_,?_⟩
 · have a:=v.pay (pitchK x)
   have b : 0 ≤ c := (PE_nonneg _).trans a
   refine (nub_nectar w (M (pitchK x))).trans ?_
   rw [costGlass,mul_add,mul_one]
   have g:=v.pos
   exact (mul_le_mul_of_nonneg_left a zero_le_two).trans
       (le_add_of_nonneg_right (by positivity))
 · cases w
   · exact ⟨_,rfl⟩
   contradiction
 intro x y h; unfold cupN pitchK
 rw [h]

variable {K:Calibration}{m:Side}{F:Mark (K.c m)}(w:wisp p ⊆ S)
    (r:Roomy S (K.c m))(v:Opening p C H F)
include w v in
lemma arrangeable : AtSupport false (region S (K.c m)) F:=
 v.room.good.mono ((maskalo p).trans (image_mono _ w))

def LitRose (S:Finset Cover)(K:Calibration)(p:BudgetPoint)
   (C:ℝ) (H:Bool):=
   Rose S K (flash p) C (C*aliquot S) H

include w r v in
lemma sunrise :
   ∃ x:Swatch S, x∈LitRose S K p C H ∧ render S K x m = F:=by
 have g:=arrangeable w v
 let x:=mend S K m r g
 have a:appear S K m x=F:=appear_mend S K m r g
 have n:=clean_spin K S m (Roomy.seats r) x F C a v.strong
 have k:Neutral K (render S K x):=
     onceNeutral (texture S K x) (Roomy.seats r)
        (by rw [appearRender,a]; exact v.room.tint)
 have l:=sleek K S m (Roomy.seats r) (z:=x) (by rw [a]; exact v.front)
 refine ⟨x,⟨fun j=>?_,n, k,l,
     fun y=>silky K S m (Roomy.seats r) (z:=x) (by rw [a]; exact v.only y)⟩,a⟩
 have d(t): daub S (x j) t=eye S K m (Roomy.seats r) j (F (replant S _ t)):=by
    rw [←eye_readCover S K m (Roomy.seats r),a]
 refine ⟨fun x=>?_,fun t u=>?_,fun y z b c=>?_⟩
 · rw [d];exact (eye_bounded ..).trans (v.room.paid _)
 · rw [d,v.room.fails _ ((passes p S w (Roomy.seats r) t).not.mpr u),map_zero]
 rw [d,d,←map_sub,mul_assoc]
 let Y:=replant S (K.c m) y; let Z:=replant S (K.c m) z
 refine ((eye_bounded _ _ _ _ _ (F Y-F Z)).trans
    (v.room.varies _ _ ((passes p S w (Roomy.seats r) y).mpr b)
      ((passes p S w (Roomy.seats r) z).mpr c))).trans ?_
 exact mul_le_mul_of_nonneg_left
      ((fare_inc ((readalo p).trans (image_mono _ w)) _ _).trans
        (aliquots S (Roomy.seats r) y z))
        v.room.pos

