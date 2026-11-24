import YM.CF.BProof.Gauss.Spread
import YM.CF.BProof.Gauss.Journey

/- Determinant receipt after chunk resolution. PL worst-case on severe Jacobian,
keep the NPL long support part. Apply to the actual T. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss.Night
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision RealM SignScalar
open Prox Journey
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
-- for X=Finset A. provide discrete measurable
variable {A X I:Type} [Fintype A][Fintype I]

/-- clearance used also under every admissible contour. Only flags coordinates, so no
measurability hypothesis separate from reading. Terms zero when support avoids selected set. -/
structure Design (B: Prox.Base A) (d:Finset A→ℝ) (t C:ℝ) where
 slot : Finset A → Finset A → ℝ
 fare : Finset A→ℝ
 cost : Moment.Toll id fare t C
 exp_price (S): d S= ∑ i,slot i S
 bounds i S:‖slot i S‖ ≤ fare i
 nont i : fare i≠0 → B.C i ∧ i.Nonempty
 part {S x y:Finset A} : (Scope.flags A).upon S x y→ slot S x=slot S y
 vanish i : slot i (∅:Finset A)=0
namespace Design
variable {B:Base A}{d:Finset A→ℝ}{t C:ℝ}
theorem vacant (D: Design B d t C) (S X:Finset A) (h:Disjoint S X): D.slot S X=0 := by
 refine Eq.trans (D.part (y:=∅) ?_) (D.vanish _); exact fun i hi=> iff_of_false (Finset.disjoint_left.mp h hi) (notMem_empty _)
end Design
section
-- discrete domain finite. canonical MeasurableSpace? use local if fails
variable {B:Prox.Base A}(F:B.Index I) [DecidableEq I]
variable (T:Finset A→Pool I)(t r q:ℝ){k n:ℕ} (v: Prox.Via F (Scope.flags A) T k)(K:Journey.Bloc B t r q F.roof k n)
       (h:∀ x,(T x).IsHermitian)(H:∀ x,Numeric (T x) r t)
def logDiff (x: Finset A) := Real.log (T x).det-Real.log (T ∅).det
def fareD (d b:ℕ)(R q:ℝ):= 2*(R*trBill d b (q/3))
local instance : MeasurableSpace (Finset A) := ⊤
local instance : MeasurableSingletonClass (Finset A):= ⟨fun i=>trivial⟩
include v K h H
lemma settle : Nonempty (Design B (logDiff T) (q/3) (fareD B.dim F.roof (Journey.bill B q F.roof k n) q)) := by
 let p:=q/3; have hp:0<p:=by have := K.cost; unfold p; positivity
 let U:= wind T t Journey.coin; let W:=Journey.bill B q F.roof k n
 have he:Show (Atmos.discrete A (Finset A) (Scope.flags A)) F F U (3*(q/3)) W:=by rw [show 3*(q/3)=q by ring]; exact Journey.warrant F (Scope.flags A) T t r q v K h H Journey.coin coinage
 let s (x:Finset A):= (U x).trace
 have hW:0≤W:=by have :=rent_pos B n k F.roof q; unfold W Journey.bill; positivity
 obtain ⟨g,Y,y,z,u⟩:= trace_price he hp hW
 let f(i S) := g i S-g i (∅:Finset A); have hi(X:Finset A): Real.log (T X).det=s X+(Fintype.card I:ℝ)*Real.log t:= Journey.tourist F (Scope.flags A) T t r q v K h H X
 change s= _ at z; refine ⟨⟨f,fun i=>2*Y i,u.scale (S:=id) (v:=Y) _ (by positivity),?_,fun i S=>(norm_sub_le ..).trans ((add_le_add ((y i).1.exact_bound S) ((y i).1.exact_bound _)).trans_eq (two_mul _).symm),?_,?_,fun i=> sub_self _⟩⟩
 · intro i; unfold logDiff f; rw [hi,hi, add_sub_add_right_eq_sub,z]; rw [Finset.sum_apply,Finset.sum_apply,sum_sub_distrib] -- instance diamond tune
 · intro i h; exact And.symm ((y i).2 (right_ne_zero_of_mul h))
 intro i S X e; have hk := (y i).1.bound_diff (i:=S) (j:=X) (True.intro); rw [show Atmos.read _ _ S X = 0 from if_pos e, mul_zero, norm_le_zero_iff, sub_eq_zero] at hk; unfold f; rw [hk]
end
end YM.CF.BProof.Gauss.Night
