import YM.SU5.Selected.Prag.Roof
import YM.SU5.Selected.Time.Pace
import YM.SU5.Selected.Prag.Pr
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
variable (j v:Axis)
local notation "θ" j:max=>mirror K j 0
local notation "T" v:max x:max=> relocate K v x
local notation "Y₀"=> timeMesh Λ
local notation "R" s:max r:max k:max=> Raise Y H Q.circuit k 0 false s r
local notation "Ξ" s:max r:max=> stream Y H D s (r-s)
local notation "W" j:max u:max=> Tower.Field Y H u j 0 false
local notation "M₀" s:max r:max=> castor Y₀ s r
local notation "B₀"=> (Λ.R.L.val:ℤ)
variable (s:ℕ)
structure Refracts (v j : Axis) (z m:ℤ) (x y: Tower.Field Y H s j 0 false)(X Y':Tower.Field Y H s v 0 false):Prop where
 -- oriented v-has X kernel. LARGEER rank both axes restores EXACT.
 early : (θ v) X.val = (T v (-z)) ((θ j) x.val)
 future : Y'.val = (T v (-z-m)) y.val
#print Refracts.mk
-- raises preserve compatibility records. proof commuting stream with mirror.
include V Q
lemma prism_move (z:ℤ){F:Family K}(h:TestFamily K true F) (u:ℕ) : (Ξ s u) ((T j z) F)=(T j (castor (timeMesh Λ) s u z)) ((Ξ s u) F):= by
 unfold relocate gaugeT; rw [show (tent Y H).B=Λ.block from rfl,chime_X Y H V s j (2*z) Q.circuit h]; change _= chime K j (gaugeShift Λ.block (2*((Λ.R.L.val:ℤ)^(u-s)*z))) _; congr 1; unfold gaugeShift; ring
namespace Refracts
variable {j v} {z m:ℤ}{x y: Tower.Field Y H s j 0 false}{X Y': Tower.Field Y H s v 0 false}
   (u:Refracts Y H s v j z m x y X Y')
omit V Q in
private lemma winds (Λ:Preparation)(s t:ℕ)(x y:ℤ): -(castor (timeMesh Λ) s t x)-(castor (timeMesh Λ) s t y) = castor (timeMesh Λ) s t (-x-y):=by unfold castor; ring -- dangerous notation implicit Λ; remove.
omit V Q in
private lemma windsL (Λ:Preparation)(s t:ℕ)(x:ℤ): -(castor (timeMesh Λ) s t x)= castor (timeMesh Λ) s t (-x):=by unfold castor; ring
include u
lemma escalates(t:ℕ)(p:s≤t) : Refracts Y H t v j (castor (timeMesh Λ) s t z) (castor (timeMesh Λ) s t m) ((R s t j) p x) ((R s t j) p y) ((R s t v) p X) ((R s t v) p Y'):=by
 let U :=Ξ s t; constructor
 · change (θ v) (U X.val)= (T v _) ((θ j) (U x.val)); have ht(a:Axis)(i:W a s) : (θ a) (U i.val)=U ((θ a) i.val):= (congrArg (fun z=> mirror K a z (U i.val)) (mul_zero _).symm).trans ((stream_flipped Y H Q.circuit s (t-s) a 0 (field_test Y H s a 0 false i)).symm) -- trans' arg
   rw [ht,ht,u.early]; unfold U; rw [windsL,prism_move _ _ V Q _ _ _ (reflect_ok K j 0 (field_test Y H s j 0 false x))]
 change U Y'.val= (T v _) (U y.val); rw [u.future,winds]; exact prism_move Y H V Q v s (-z-m) (field_test Y H s j 0 false y) t
-- movement lemma preserve (v,j) tagging; no `v≠j` needed.
omit V Q
local notation "F" j:max k:max h:max z:max=> sail Y H s j 0 false k h (2*z)
private lemma twin_r (f:W j s)(w:Axis)(a b:ℤ) : (T w a) ((T v b) f.val)=(T v b) ((T w a) f.val) := twin_slide w v _ _ (field_test Y H s j 0 false f).paid.choose_spec -- include u here triggers heavy, omit
lemma sailBoth (w:Axis)(p:w≠j)(e:w≠v)(a:ℤ): Refracts Y H s v j z m x ((F j w p a) y) X ((F v w e a) Y') := by
 refine ⟨u.early,?_⟩; change (T w a) Y'.val=(T v (-z-m)) ((T w a) y.val); rw [u.future]; exact twin_r Y H s u y w _ _ -- parameter implicit.
lemma sailFuture (p:j≠v)(n:ℕ): Refracts Y H s v j z m x (tick Y H s j 0 false (2*n) y) X ((F v j p (n:ℤ)) Y'):=by
 refine ⟨u.early,?_⟩; rw [timed_apply]; change (T j (n:ℤ)) Y'.val=(T v (-z-m)) ((T j (n:ℤ)) y.val); rw [u.future]; exact twin_r Y H s u y _ _ _ --
end Refracts
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer
#print axioms prism_move
#print axioms Refracts.escalates
#print axioms Refracts.winds
#print axioms Refracts.sailFuture
#print axioms Refracts.sailBoth
#check @Refracts.escalates
