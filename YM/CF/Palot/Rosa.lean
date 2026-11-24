import YM.CF.Palot.Afreet
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
def fuelH (O:Support n)(i:Y n): Prop:= ¬Disjoint i.val O
def raisedH (O:Support n)(i: hook (Site n)):Prop:=∀ j∈i, fuelH O j
def tallH(O:Support n)(x:hook (Site n)): hook (Site n):= x.filter (fuelH O)
def highV(O:Support n):Finset (hook (Site n)) := univ.filter fun i=> flow _ i ∧O⊆robe i∧ raisedH O i
def below(O:Support n):Finset (hook (Site n)):= univ.filter fun i=> flow _ i ∧Disjoint O (robe i)
lemma cloven (O:Support n)(W:Y n→ E): hGas O W=∑ i∈ highV O,(∏ j∈i,W j)* south (robe i) W:=by
 unfold hGas south; simp_rw [mul_sum]; symm; rw [sum_sigma'] -- tune
 let L:= highV O; let U: Finset (hook (Site n)):=univ.filter fun i=>flow _ i∧ O⊆robe i
 have he{x r:hook (Site n)}(p:x∈ L)(q:r∈ below (robe x)): Disjoint (robe x) (robe r)∧ Disjoint x r:=by
    have hv:= (mem_filter.mp q).2.2; refine ⟨hv,Finset.disjoint_left.mpr fun {i} s g=>?_⟩; obtain ⟨y,t⟩:=i.property; exact Finset.disjoint_left.mp hv (mem_biUnion.mpr ⟨_,s,t⟩) (mem_biUnion.mpr ⟨_,g,t⟩)
 have hx(B:Finset (Site n))(x:hook (Site n))(i:leaf (Site n))(v:i∈x):i.val⊆ robe x:=fun _ t=>mem_biUnion.mpr ⟨_,v,t⟩
 have hg{x r:hook (Site n)}(p:x∈ L)(q:r∈ below (robe x)): tallH O (x∪r)=x:=by
    ext i : 1; rw [tallH,mem_filter]; obtain ⟨u,f,g⟩:= (mem_filter.mp p).2; constructor
    · rintro ⟨i',v⟩; exact (mem_union.mp i').resolve_right (fun b=> v (Disjoint.mono (hx O r i b) f (he p q).1.symm))
    intro t; exact ⟨mem_union_left _ t,g _ t⟩
 refine sum_nbij' (fun a=> a.1∪a.2) (fun a=> ⟨tallH O a,a\ tallH O a⟩) ?_ ?_ ?_ ?_ ?_ -- tune
 · rintro ⟨i,r⟩ p; obtain ⟨l,t⟩:= mem_sigma.mp p; obtain ⟨u,f,g⟩:= (mem_filter.mp l).2; have hd:= he l t; obtain ⟨hr,hp⟩:= (mem_filter.mp t).2; refine mem_filter.mpr ⟨mem_univ _,?_,?_ ⟩
   · intro a p b q n; rcases mem_union.mp p with p|p<;>rcases mem_union.mp q with q|q
     exact u _ p _ q n
     exact Disjoint.mono (hx O _ _ p) (hx O _ _ q) hp
     exact Disjoint.mono (hx O _ _ p) (hx O _ _ q) (he l t).1.symm
     exact hr _ p _ q n
   refine Finset.Subset.trans f ?_; intro y p; obtain ⟨x,v,c⟩:=mem_biUnion.mp p; exact hx O _ x (mem_union_left _ v) c
 · intro a p; let T:=tallH O a; have ht:T⊆ a:=filter_subset ..; obtain ⟨l,r⟩:= (mem_filter.mp p).2; refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, flow_m l ht,?_, fun i p=>(mem_filter.mp p).2⟩,mem_filter.mpr ⟨mem_univ _,flow_m l (sdiff_subset (t:= T)),?_⟩⟩
   · intro y v; obtain ⟨i,u,g⟩:= mem_biUnion.mp (r v); exact mem_biUnion.mpr ⟨_,mem_filter.mpr ⟨u, (show fuelH O i from fun p=> Finset.disjoint_left.mp p g v)⟩,g⟩
   refine Finset.disjoint_left.mpr fun {x} p q=>?_ ; obtain ⟨y,v,c⟩:=mem_biUnion.mp p; obtain ⟨z,h,m⟩:=mem_biUnion.mp q; obtain ⟨p,f⟩:= mem_sdiff.mp h; exact Finset.disjoint_left.mp (l y (ht v) z p (fun w=>f (w ▸ v))) c m
 · rintro ⟨a,b⟩ p; obtain ⟨l,r⟩:= mem_sigma.mp p; dsimp only; rw [hg l r]; congr; ext i : 1; rw [Finset.mem_sdiff,mem_union]; exact ⟨fun g=> g.1.resolve_left g.2, fun g=>⟨Or.inr g,fun p=> Finset.disjoint_left.mp (he l r).2 p g⟩⟩
 · intro a _; dsimp only; exact Finset.union_sdiff_of_subset (filter_subset ..)
 rintro ⟨a,b⟩ p; exact (prod_union (he (mem_sigma.mp p).1 (mem_sigma.mp p).2).2).symm
variable {F:Y n→ E}{B:ℕ}{Z:Support n}{c: Y n→ℝ}{a γ δ q:ℝ}{S:Support n}
abbrev ice (W:Y n→ E)(i:Y n):E:=exp (-jingle W i)-1
abbrev pier(W:Y n→ E)(O:Support n):E:= ∑ s:hook (Site n) with raisedH O s,∏ i∈s,ice W i
lemma forge(O:Support n)(u:∀ i,‖F i‖≤c i)(h:0≤a)(H:Ready stern B c a γ δ q): south O F=exp (∑ i:Y n,jingle F i) * pier F O:=by
 letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
 let L: Finset (Y n):=univ.filter (fuelH O); rw [sung O H h u]
 have he: ∀ (s: Finset (Y n)),(∀ i∈s,fuelH O i) ↔ s⊆ L:=fun s=>⟨fun h i u=> mem_filter.mpr ⟨mem_univ _,h _ u⟩,fun i s t=> (mem_filter.mp (i t)).2 ⟩
 rw [pier, show ((univ:Finset (hook (Site n))).filter _)=L.powerset from Finset.ext fun s=> by rw [mem_filter, and_iff_right (mem_univ _),mem_powerset]; exact he s, ← Finset.prod_add_one]
 simp_rw [ice,sub_add_cancel]; rw [←exp_sum, ←exp_add]
 apply congrArg; rw [sum_neg_distrib]; unfold L; rw [sum_filter,sum_filter]; simp only [← sum_sub_distrib,← sub_eq_add_neg]; -- tune
 apply sum_congr rfl; intro i p; unfold fuelH; by_cases v: Disjoint i.val O; · rw [if_pos v, if_neg (not_not.mpr v), sub_zero]
 rw [if_neg v, if_pos v,sub_self]
end YM.CF.Palot
