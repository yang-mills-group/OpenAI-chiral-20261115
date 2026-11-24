import GaugeFieldConstruction.ElxH
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
section worth
variable {I J α γ:Type} [Fintype I][LinearOrder I]
-- TYPE rewrite.M capsule.Weight referencing proof. Reef X activation.
variable {p:BudgetPoint}{r h:ℝ}{n:Side}{σ: I → Seat n}
open Py Bake Vow Larch
-- ℓ.radius powers already included in c values.
abbrev Bplain(d:ℕ)(c r:ℝ):= c / r^d
def PitR (p:BudgetPoint)(h r:ℝ)(i:dues I (Scree.Hub n))(U:InkD n)(c:ℝ):Prop:=Medal p i.2.val.2 ∅ (oV U) h (Bplain i.1.card c r)
def PitF (p:BudgetPoint)(h r:ℝ)(k:ℕ)(i:dues I (Force n))(V:Scree.Copy n)(c:ℝ):Prop:=Medal p i.2.val.1.val.2 i.2.val.2 V h (Bplain i.1.card c r) ∧ ∀ u,V u≠0→(i.2.val.2⊆ flags p.threshold u.1 ∧ Lattice.halo k i.2.val.2⊆ i.2.val.1.val.2)
-- Want add
lemma ReefxR: ReefX (α:=Hub n) (I:=I) (PitR p h r):=by
 refine ⟨?_,?_⟩
 · intro i; unfold PitR Bplain; rw[zero_div]; exact Medal.zeroT
 intro i x y a b p q; unfold PitR Bplain; rw[add_div]; exact Medal.plus p q
lemma ReefxF(k:ℕ):ReefX (α:=Force n) (I:=I) (PitF p h r k):=by
 constructor
 · intro i; refine ⟨?_,fun k e=>False.elim (e rfl)⟩; unfold Bplain; rw[zero_div]; exact Medal.zeroT
 intro i x y a b P' Q'; refine ⟨?_,fun k e=>?_⟩
 · unfold Bplain; rw[add_div]; exact Medal.plus P'.1 Q'.1
 by_cases v:x k=0
 · apply Q'.2 k; intro h; exact e (by change x k+y k=0; rw[v,h,add_zero])
 exact P'.2 k v
abbrev BillX (p:BudgetPoint)(σ:I→Seat n)(h r:ℝ) := BondM (fun i:Hub n=>i.val.2) σ (PitR p h r)
abbrev BillF (p:BudgetPoint)(σ:I→Seat n)(h r:ℝ)(k:ℕ) := BondM (fun i:Force n=>i.val.1.val.2) σ (PitF p h r k)
end worth
end YM.CF.Scree.Ing
end
