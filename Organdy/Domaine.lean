import Organdy.LatticeFieldEstimates
import YM.CF.Scree.Brief
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Wilson RG MeasureTheory Scree

variable {n:Side}
-- pressure interface. No assumption on price radius or approx error other than inequalities.
-- q within ball, every nonzero entry anchored.
structure Domaine (k:ℕ)(r τ η D:ℝ)(W:Config SU.group n→ℂ)(A:Ink (Chip n)):Prop where
  meas:Measurable W
  move(g:Site n→SU.E)(U): W (gauge g U)=W U
  loc: LocalOn (halo k {(0:Site n)}) W
  uniform(U): ‖W U‖ ≤ η+D*τ^2
  sym:A.Sym
  inside:A.Within (stains 0 k)
  purse:A.qty ≤ D
  priced(U:Config SU.group n)(x:Dir n):
    Agrees (halo k {(0:Site n)}) U (represent x) →
    ‖x‖<r→ pingS τ (halo k {(0:Site n)}) U →
    ‖W U-A.gilt (blush x)‖≤η+D*‖x‖^3

-- success measure via LatticeFieldEstimates decree
abbrev dint (A:Ink (Chip n)) :ℝ:=(A.gilt (decree ∘ dot)).re

namespace Domaine
variable {k:ℕ}{τ η D:ℝ}{W:Config SU.group n→ℂ}{A:Ink (Chip n)}
open Finset

lemma raises (p:Domaine k r τ η D W A){b c:ℝ}
   (h:η≤b)(q:D≤c):Domaine k r τ b c W A:=
 ⟨p.meas,p.move,p.loc,fun i=>(p.uniform i).trans (add_le_add h (by gcongr)),
   p.sym,p.inside,p.purse.trans q,fun x u i j l=>
     (p.priced x u i j l).trans (add_le_add h (by gcongr))⟩
lemma streak {I:Type}[Fintype I][DecidableEq I]
 {X:I→Config SU.group n→ℂ}{A:I→Ink (Chip n)}{e c:I→ℝ}
 (p:∀ i,Domaine k r τ (e i) (c i) (X i) (A i)):
 Domaine k r τ (∑i,e i) (∑i,c i) (∑i,X i) (∑i,A i):=by
 refine ⟨?_,?_,?_,?_,
    Ink.sym_sum univ A (fun i _=>(p i).sym),
    Ink.within_sum univ A (fun i _=>(p i).inside),
    (Ink.qty_sum univ A).trans (sum_le_sum fun i _=>(p i).purse),?_⟩
 · rw [show (∑i,X i) = fun a=> ∑i, X i a by funext a;rw [Finset.sum_apply]]
   exact Finset.measurable_sum _ (fun i _=>(p i).meas)
 · intro g U; rw [Finset.sum_apply, Finset.sum_apply]
   exact sum_congr rfl fun i _=>(p i).move g U
 · intro U V g;rw [Finset.sum_apply, Finset.sum_apply]
   exact sum_congr rfl fun i _=>(p i).loc _ _ g
 · intro U;rw [Finset.sum_apply,sum_mul,←sum_add_distrib]
   exact (norm_sum_le ..).trans (sum_le_sum fun i _=>(p i).uniform U)
 intro U x g h l
 rw [Finset.sum_apply,Ink.gilt_sum,←sum_sub_distrib,sum_mul,←sum_add_distrib]
 exact (norm_sum_le ..).trans (sum_le_sum fun i _=>(p i).priced U x g h l)

lemma weighted (p:Domaine k r τ η D W A)(z:ℂ):
 Domaine k r τ (‖z‖*η) (‖z‖*D) (fun U=>z*W U) (z•A) :=by
 obtain ⟨i,m,g,l⟩:=Ink.dye_ink z A p.inside p.sym
 refine ⟨measurable_const.mul p.meas,fun t x=>congrArg _ (p.move t x),?_,?_,m,i,
  g.trans_le (mul_le_mul_of_nonneg_left p.purse (norm_nonneg _)),?_⟩
 · exact fun V U h=>congrArg _ (p.loc _ _ h)
 · intro U;rw [norm_mul,mul_assoc,←mul_add]
   exact mul_le_mul_of_nonneg_left (p.uniform U) (norm_nonneg _)
 intro U x h u y
 rw [l, ←mul_sub,norm_mul,mul_assoc,←mul_add]
 exact mul_le_mul_of_nonneg_left (p.priced U x h u y) (norm_nonneg _)

open scoped ComplexConjugate
abbrev white (A: Ink (Chip n)):Ink (Chip n):=fun i j=>conj (A i j)
lemma white_gilt(x):(white A).gilt x=conj (A.gilt x):=by simp [Ink.gilt,white]
lemma charge (p:Domaine k r τ η D W A): Domaine k r τ η D (conj ∘ W) (white A):=by
 have l:(white A).qty=A.qty:=by simp [white,Ink.qty]
 refine ⟨Complex.continuous_conj.measurable.comp p.meas,fun t x=>congrArg (starRingEnd ℂ) (p.move t x),?_,?_,
   fun i j=>congrArg (starRingEnd ℂ) (p.sym i j),?_,l.trans_le p.purse,?_⟩
 · exact fun V U h=>congrArg (starRingEnd ℂ) (p.loc _ _ h)

 · intro U;simpa using p.uniform U
 · intro i j y
   exact p.inside i j (by intro t;apply y;simp [white,t])
 intro U x f h j
 rw [white_gilt]
 change ‖conj _-conj _‖ ≤ _
 rw [←map_sub, RCLike.norm_conj]
 exact p.priced U x f h j
