import YM.CF.Palot.Jade
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Palot
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open scoped Classical
open RG Push Push.AbsoluteSums Push.AbsoluteSums.Ursell Push.AbsoluteSums.Graph Push.AbsoluteSums.Coef Push.AbsoluteSums.Gas
open Trees
variable {n:Side}{ι E: Type*}[Fintype ι][NormedCommRing E][NormOneClass E][NormedAlgebra ℝ E][CompleteSpace E]
local notation "bay"=>Stilo.bay
abbrev jack(O:Support n)(F W:Y n→ E): Y n→ E:= fun i=> mintF (jewel O F W) (beamH i.val)
def Hac (O:Support n)(F:Y n→ E):E:=∑ i∈ highV O,∏ j∈i,F j
lemma hacH(O:Support n)(F W:Y n→ E): hGas O (jack O F W)= Hac O (jack O F W):=by
 unfold hGas Hac; symm; refine sum_subset (show highV O⊆_ from fun i p=> let t:= (mem_filter.mp p).2; mem_filter.mpr ⟨mem_univ _,t.1,t.2.1⟩) ?_; intro i p q; obtain ⟨l,v⟩:= (mem_filter.mp p).2; by_contra h; apply q; exact mem_filter.mpr ⟨mem_univ _,l,v, fun j u => jackF _ _ _ _ (fun x=> h (prod_eq_zero u x))⟩
lemma joinP(i:Finset (Duo n)): i.toLeft.disjSum i.toRight=i:=by ext x; cases x <;> simp
lemma jab(O:Support n)(F W:Y n→ E): Hac O (jack O F W)=∑ i∈ highV O,(∏ j∈i,F j)* ∑ s:hook (Site n) with raisedH (robe i) s,∏ j∈s,W j:=by
 rw [←hacH, ←chimeU O (orgG O F W)]
 let P:= fun i:Finset (Duo n)=>O⊆bay (beatB i) ∧ mine O i
 let M(i: Finset (Duo n)):=∏ j∈i,Sum.elim F W j
 have he(i:Finset (Duo n)): (∑ H:Crowd (Site n) with O⊆bay H,jewel O F W i H)=if P i then M i else 0:=by
    split_ifs with g; · rw [sum_eq_single (beatB i), jewel,if_pos ⟨rfl,g.2⟩]; intro a _ l; unfold jewel; rw [if_neg]; exact fun p=> l p.1.symm; exact fun v=> False.elim (v (mem_filter.mpr ⟨mem_univ _,g.1⟩))
    apply sum_eq_zero; intro H h; unfold jewel; rw [if_neg]; exact fun p=> g ⟨p.1.symm ▸ (mem_filter.mp h).2, p.2⟩
 simp_rw [he,mul_sum]; rw [←sum_filter,sum_sigma']; symm
 apply Finset.sum_nbij' (fun t=> Finset.disjSum t.1 t.2) (fun a=> ⟨a.toLeft,a.toRight⟩); intro i p
 · rcases i with ⟨i,j⟩; obtain ⟨l,q⟩:= mem_sigma.mp p; obtain ⟨r,h,u⟩:= (mem_filter.mp l).2; obtain ⟨-,v⟩:=mem_filter.mp q; refine mem_filter.mpr ⟨mem_univ _,?_⟩; unfold P mine; simp only [toLeft_disjSum,toRight_disjSum,r,u,v,true_and]; refine ⟨h.trans ?_, Finset.Subset.trans inter_subset_left h⟩; rw [←rim_beat,toLeft_disjSum,toRight_disjSum]; exact subset_union_left
 · intro a p; obtain ⟨l,v⟩:= (mem_filter.mp p).2; obtain ⟨r,t,x,g⟩:=v; exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _,r,fun i u=>g (mem_inter.mpr ⟨u,l u⟩), t⟩,mem_filter.mpr ⟨mem_univ _,x⟩⟩
 · intro i p; simp
 · intro i _; exact joinP i
 intro i p; simp [M,Finset.prod_disjSum] -- tune
lemma south_at (O:Support n)(F W:Y n→ E)(h:∀ i,W i≠F i→ ¬Disjoint i.val O) :south O W=south O F:=by
 unfold south; apply sum_congr rfl; intro i p; apply prod_congr rfl; intro j t; by_contra v; exact h _ v (Disjoint.mono_left (show j.val⊆robe i from fun _ l=> mem_biUnion.mpr ⟨_,t,l⟩) (mem_filter.mp p).2.2.symm)
lemma poleX (O: Support n)(f:Y n→ E){a γ δ q:ℝ}{c:Y n→ℝ}{B:ℕ}(p: Ready stern B c a γ δ q)(v:0≤a)(g:∀ i,‖halt f O i‖ ≤c i): hGas O f= exp (∑ i:Y n,jingle (halt f O) i) * Hac O (jack O f (ice (halt f O))):=by
 let W:=halt f O; let A(i):=south (robe i) W; let V:=exp (∑ i:Y n,jingle W i)
 rw [cloven O f,jab,mul_sum]; apply sum_congr rfl; intro i t; change _*south (robe i) f=V * (_ * pier W (robe i))
 have he: south (robe i) f=south (robe i) W:=by
    apply south_at; intro j q p; have hu:= (mem_filter.mp t).2.2.1; exact q (if_pos (show constrainF O j from Disjoint.mono_left hu p.symm)).symm
 rw [he,forge _ g v p]; exact mul_left_comm .. -- tune
end YM.CF.Palot
