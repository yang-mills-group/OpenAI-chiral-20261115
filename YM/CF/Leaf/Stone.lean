import YM.CF.Stax.Eval
import YM.CF.Sault.Gilt
import YM.CF.Cadre.Point
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Leaf
open Function NormedSpace Fock Pastry Tap Sault Cadre Matrix Palot MeasureTheory Filter
open Finset
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι σ α:Type*}[LinearOrder ι][Fintype ι]
-- logarithmic response. Exact finite-body stencil law. arity-2 independent other variables. 
abbrev bump(P Q:FC ι): FC ι:= P*Q-Q*P
lemma τb(F:FC ι)(g:ℂ)(X:FC ι):bump F (g • X)=g • bump F X:=by unfold bump; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_sub]
lemma τq(F:FC ι)(g:ℂ)(X:FC ι):bump (g • X) F=g • bump X F:=by unfold bump; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_sub]
lemma σb(F:FC ι)(S:Finset α)(X:α→FC ι):bump F (∑ i∈S, X i)=∑ i∈S,bump F (X i):=by unfold bump; rw [mul_sum,sum_mul,sum_sub_distrib]
lemma σq(F:FC ι)(S:Finset α)(X:α→FC ι):bump (∑ i∈S,X i) F=∑ i∈S,bump (X i) F:=by unfold bump; rw [mul_sum,sum_mul,sum_sub_distrib]
lemma δb(F X Y:FC ι): bump (F+X) Y=bump F Y+bump X Y:=by unfold bump; rw [add_mul,mul_add]; abel
lemma hp_b(F X Y:FC ι): bump (F-X) Y=bump F Y-bump X Y:=by unfold bump; rw [sub_mul,mul_sub]; abel
lemma ο_b(F X Y:FC ι): bump F (X*Y)= (bump F X)*Y+X*bump F Y:=by unfold bump; rw [sub_mul,mul_sub]; simp only [mul_assoc]; abel
lemma ο_q(F X Y:FC ι): bump (X*Y) F=(bump X F)*Y+X*bump Y F:=by unfold bump; rw [sub_mul,mul_sub]; simp only [mul_assoc]; abel
lemma bS_v(F:FC ι)(u:Scree.spanP ι F)(x:Dough ι):bump F x.val=0:=by rw [u,(fineShape x).pin,σq]; apply sum_eq_zero; intro i _; rw [τq,σb,sum_eq_zero,smul_zero]; intro j p; rw [τb, show bump (poke i) (poke j)=0 from sub_eq_zero.mpr ((Poly.commute _ _ _ (mem_filter.mp p).2).eq), smul_zero]
private lemma σp(i:ι): Scree.spanP ι (put i):= (show poke {i}=put i from Poly.tag_once (Pastry.cane _) i) ▸ Scree.spanPt {i} -- tune
lemma ζb(i a b:ι): Scree.spanP ι (bump (takeF i) (put a*put b)):=by
 let z(a:ι):ℂ:= if i=a then 1 else 0; have he(a): takeF i*put a=z a • 1-put a*takeF i:=by rw [eq_sub_iff_add_eq,mixed]; unfold z; split_ifs <;> simp
 rw [show bump (takeF i) (put a*put b)= z a • put b + (-z b) • put a from ?_]; exact (show Scree.spanP ι _ from (by unfold Scree.spanP; simp_rw [crumb_add,add_smul,sum_add_distrib]; exact congrArg₂ (·+·) (Scree.spanS (σp _) _) (Scree.spanS (σp _) _)))
 unfold bump; rw [←mul_assoc,he,sub_mul,mul_assoc (put a),he,mul_sub, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,mul_one, mul_assoc,neg_smul]; abel
lemma ζt(i:ι)(S:Finset ι)(p:Even S.card): Scree.spanP ι (bump (takeF i) (poke S)):=by
 induction S using Finset.strongInductionOn with
 | _ s ih=>
    by_cases k:s.Nonempty
    · obtain ⟨j,g⟩:=k; have h:(s.erase j).Nonempty:=by rw [←card_pos,card_erase_of_mem g]; have hx:= (show s.Nonempty from ⟨j,g⟩).card_pos; obtain ⟨i,f⟩:=p; omega
      obtain ⟨l,u⟩:=h; let t:= (s.erase j).erase l; have hx:t⊂s:=lt_trans (erase_ssubset u) (erase_ssubset g); have hv: Even t.card:=by unfold t; rw [card_erase_of_mem u,card_erase_of_mem g]; have hj:=(show (s.erase j).Nonempty from ⟨l,u⟩).card_pos; obtain ⟨i,f⟩:=p; rw [card_erase_of_mem g] at hj; exact ⟨i-1,by omega⟩
      have he:poke s= parity j (s.erase j) • parity l t • ((put j*put l)*poke t):=by
         unfold poke; nth_rw 1 [← insert_erase g]; rw [Poly.tag_any _ _ _ (notMem_erase j s)]; rw [show (cane ι).tag (s.erase j)=parity l t • ((cane ι).term l*poke t) from by nth_rw 1 [← insert_erase u]; exact Poly.tag_any _ _ _ (notMem_erase l (s.erase j)),Algebra.mul_smul_comm,mul_assoc]; rfl
      rw [he,τb,τb,ο_b]; apply Scree.spanS; apply Scree.spanS; unfold Scree.spanP; simp_rw [crumb_add,add_smul,sum_add_distrib]; exact congrArg₂ (·+·) (Scree.spanT (ζb ..) (Scree.spanPt _)) (Scree.spanT (Scree.spanT (σp _) (σp _)) (ih _ hx hv))
    rw [not_nonempty_iff_eq_empty.mp k, show poke ∅=(1:FC ι) from Poly.tag_void _, show bump _ 1=(0:FC ι) from sub_eq_zero.mpr (Commute.one_right _).eq]; exact show Scree.spanP _ _ from (by unfold Scree.spanP; simp [crumb])
abbrev rank2(A:FC ι):Prop:= ∀ x y z:Dough ι, bump (bump (bump A x.val) y.val) z.val=0
abbrev rank1(A:FC ι):Prop:= ∀ x y:Dough ι, bump (bump A x.val) y.val=0
lemma τX(A B:FC ι)(p:rank1 A)(q:rank1 B): rank2 (A*B):=by intro i j k; rw [ο_q,δb,ο_q,ο_q,p i j,q i j,zero_mul,zero_add,mul_zero,add_zero,δb,ο_q,ο_q,p i k,p j k,q j k,q i k]; simp
lemma αb(i:ι):rank1 (put i):=by intro x y; rw [bS_v _ (σp _)]; simp [bump]
lemma βb(i:ι):rank1 (takeF i):=by
 intro x y; rw [(fineShape x).pin,σb,σq]; apply sum_eq_zero; intro j p; rw [τb,τq,bS_v _ (ζt i j (mem_filter.mp p).2),smul_zero]
lemma δX(S:Finset α)(V:α→ FC ι)(p:∀ i∈S,rank2 (V i)):rank2 (∑ i∈S,V i):=by intro x y z; rw [σq,σq,σq,sum_eq_zero]; exact fun i h=>p i h x y z
lemma ψX(a:ℂ)(F:FC ι)(p:rank2 F):rank2 (a • F):=by intro x y z; rw [τq,τq,τq,p x y z,smul_zero]
lemma σX(F G:FC ι)(p:rank2 F)(q:rank2 G): rank2 (F+G):=by intro i j k; rw [δb,δb,δb,p,q,add_zero]
lemma θX(F G:FC ι)(p:rank2 F)(q:rank2 G): rank2 (F-G):=by intro i j k; rw [hp_b F G, hp_b (bump F i.val) (bump G i.val) j.val,hp_b (bump (bump F i.val) j.val) (bump (bump G i.val) j.val) k.val,p,q,sub_zero]
lemma ρX : rank2 (1:FC ι):=by intro i j k; simp [bump]
lemma ore2(P F A B C:Op ι):rank2 (Sault.forge P F A B C):=by
 let h(P:Op ι)(f g:ι→FC (LeanV ι))(u:∀ i,rank1 (f i))(v:∀ i,rank1 (g i)):=show rank2 (Sault.urn f g P) from δX _ _ fun i _=>δX _ _ fun j _=>ψX _ _ (τX _ _ (u _) (v _)); exact σX _ _ (σX _ _ (σX _ _ (h F _ _ (fun _=> αb (true,_)) (fun _=>αb (false,_))) (h _ _ _ (fun _=>αb (true,_)) (fun _=>βb (true,_)))) (θX _ _ (ψX _ _ ρX) (h _ _ _ (fun _=>αb (false,_)) (fun _=>βb (false,_))))) (h _ _ _ (fun _=>βb (false,_)) (fun _=>βb (true,_)))
end YM.CF.Leaf
