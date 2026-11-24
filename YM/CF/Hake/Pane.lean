import YM.CF.Stilo.Rive
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
variable {ι I J n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
-- traditional ψ↑ Bool true. normal use poke star t. in generalized G uses star of tag formed by star transform.
abbrev Oboe(n:Type*):= Bool × n
abbrev bell : Oboe n→ FC n:= fun i=> if i.1 then put i.2 else takeF i.2
abbrev revertP (i: Oboe n):Oboe n:=( !i.1, i.2)
abbrev Restart (F:Oboe n→FC m):Prop:=∀ i j,antiB (F i) (F j)= if i=revertP j then 1 else 0
lemma orchestra: Restart (bell (n:=n)):=by
 rintro ⟨b,i⟩ ⟨u,j⟩; cases b<;>cases u <;> simp [antiB,bell,revertP,take_take,mixed,put_put]; rw [add_comm,mixed]; by_cases h:j=i; rw [if_pos h,if_pos h.symm]; rw [if_neg h,if_neg (Ne.symm h)]
lemma pore_s (i:Finset n) : acts (star (poke i)) (basisKet i)=basisKet (∅:Finset n):=by
 induction i using Finset.induction_on_min with
 | empty=> rw [poke,Poly.tag_void,star_one,act_one]
 | @insert j S u ih=>
    rw [poke, Poly.tag_min _ _ _ u,star_mul,act_mul]; let T:= insert j S
    have hv: j∉ S:= fun p=>lt_irrefl _ (u _ p)
    rw [show star ((cane n).term j)=takeF j from rfl,take_act,if_pos (mem_insert_self ..), erase_insert hv,show parity j _=1 from ?_,one_smul]; exact ih
    have hp : ((insert j S).filter fun x=>x<j)=∅:= by rw [Finset.filter_eq_empty_iff]; intro i h; rcases mem_insert.mp h with rfl|h; simp; exact (u _ h).not_gt
    simp [parity,hp] -- tune
lemma pore_k (i j: Finset n)(h : ¬ i ⊆ j): acts (star (poke i)) (basisKet j)=0:=by
 induction i using Finset.induction_on_min generalizing j with
 | empty=>simp at h
 | @insert x S u ih=>
    rw [poke, Poly.tag_min _ _ _ u,star_mul,act_mul,show star ((cane n).term x)=takeF x from rfl,take_act]; split_ifs with v
    · rw [map_smul,ih _ (fun t=>h (insert_subset v (t.trans (erase_subset ..)))),smul_zero] -- tune ih
    rw [map_zero]
abbrev piano (i: Finset n × Finset n):FC n:= poke i.1*star (poke i.2)
abbrev pour (w: Finset n × Finset n→ℂ) := ∑ i : Finset n × Finset n, w i • piano i
lemma piano_unique (w: Finset n×Finset n→ℂ)(h:pour w=0): w=0:=by
 let f(s t:Finset n):=w (t,s)
 suffices H:∀ s t,f s t=0 from funext fun (t,s)=> H s t
 intro s; induction s using WellFoundedLT.induction with
 | ind s ih=>
    have ht:= act_zero (basisKet s); let u:= basisKet s
    have he:= Eq.trans (congrArg (fun x:FC n=>acts x u) h) ht
    rw [pour,Fintype.sum_prod_type] at he; simp_rw [act_sum] at he
    have hy(i:Finset n):∑ j:Finset n,acts (w (i,j) • piano (i,j)) u = f s i • basisKet i:= by
       rw [sum_eq_single s, act_smul,piano,act_mul,pore_s]; exact congrArg (fun x: Wave n=>f s i • x) (poked i)
       intro b _ l; by_cases hk:b ⊆ s; · rw [show w (i,b)=0 from ih b (lt_of_le_of_ne hk l) i,zero_smul,act_zero]
       rw [act_smul,piano,act_mul,pore_k _ _ hk,map_zero,smul_zero]
       simp
    simp_rw [hy] at he; intro i; have hg:= congrArg (fun x=> inner ℂ (basisKet i) x) he; simp only [inner_sum,inner_zero_right,inner_smul_right,basis_inner,basis_apply] at hg; simpa using hg -- tune
lemma piano_same : Injective (pour (n:=n)):=by
 intro x y f; apply sub_eq_zero.mp; apply piano_unique; change ∑ u,(x u-y u) • _=_; simp_rw [sub_smul,sum_sub_distrib]; exact sub_eq_zero.mpr f
end YM.CF.Hake
