import Organdy.Rolls
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Lattice Fock Sour Pastry Scree Skye Cadre Vow Palot Rue Tulip Lat Stax Rush Scroll Finset RG
open Cube Rill Mew Ione Bake Rive  Metric
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator Mew
attribute [local instance] opCStarAlgebra
variable {n:Side} {p:BudgetPoint} {h a b c d:ℝ}{q:ℕ} {I : Type} [LinearOrder I] [Fintype I]

open Levier Urn Tenant Hake Salt Spire Nacre Dial SU
variable (s:Sweep n)
local notation "T"=> γS s
local notation "D₁" => detX s.s
local notation "B₁" => s.charge
local notation "JS"=> Single n
local notation "Fz"=> FC (Dwell n)

open Leaf

lemma rockGlide (L:ℕ)(P:BudgetPoint)(i:Aura n)(x y:Seat n)
 (d:(boxA s).symm x=y): moldA s (αK (rockG L P x) i) = αK (rockG L P y) (moldA s i):=by
   have h:(halo (massif L*P.B) ({x}:Finset (Site (More n)))).map (boxA s).symm.toEmbedding=halo (massif L*P.B) {y}:=by
      rw [←d,←sitU,←paysT,map_singleton]; rfl
   apply Subtype.ext
   exact ((Finset.map_union ..).trans (congrArg (· ∪ _) h))

lemma glide
   (V W:Bag n)(L:ℕ) (r:ℝ) (t:whirlB s V=r • W)
   (P:BudgetPoint)(x y:Seat n)(g:(boxA s).symm x=y):
   whirlB s (expand L P x V) = r • expand L P y W:=by
 rw [expand,map_sum,expand,smul_sum]
 refine sum_equiv (moldA s) (by simp) ?_
 intro i _
 funext j
 simp only [Pi.smul_apply]
 change exportQ s (if (moldA s).symm j=_ then _ else 0) = _

 simp only [Equiv.symm_apply_eq,rockGlide s L P i x y g]
 split
 · have h:=congrFun t (moldA s i)
   change exportQ s (V ((moldA s).symm (moldA s i)))=r • W (moldA s i) at h
   rwa [Equiv.symm_apply_apply] at h
 rw [map_zero,smul_zero]
