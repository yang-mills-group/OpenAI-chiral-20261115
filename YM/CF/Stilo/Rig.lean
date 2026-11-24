import YM.CF.Stilo.Fife
set_option autoImplicit false
noncomputable section
namespace YM.CF.Stilo
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {ι I J n m:Type*}[LinearOrder n][Fintype n][LinearOrder m][Fintype m]
open Scree Pastry
abbrev lank(P:ι→n→ℂ)(i:ι):FC n:= ∑ j:n,P i j • put j
lemma sumB {F G:FC n}(h:spanP n F)(p:spanP n G):spanP n (F+G):=by
 change F+G=∑ _,_; simp_rw [crumb_add,add_smul,sum_add_distrib]; rw [←h,←p]
lemma grandP : spanP n (1:FC n):=by rw [show (1:FC n)=poke ∅ from (Poly.tag_void ..).symm]; exact spanPt _
lemma mountT (L:ι→ℂ)(F:ι→FC n)(j:List ι)(h:∀ i∈j, spanP n (F i)):spanP n (j.map F).sum:=by
 induction j with
 | nil=> change (0:FC n)=_; simp [crumb]
 | cons i j ih=> rw [List.map_cons,List.sum_cons]; exact sumB (h i (List.mem_cons_self ..)) (ih fun i p=> h i (List.mem_cons_of_mem _ p)) -- tune
lemma slap(P:ι→n→ℂ)(i:ι) : spanP n (lank P i):= snack fun j _=> spanS (by rw [show put j=poke {j} from (Poly.tag_once (cane n) j).symm]; exact spanPt _) _
lemma rent_m(P:ι→n→ℂ)(L:ι→ι→ℂ)(j:List ι): spanP n (taskC (lank P) (price L n) j):=by
 suffices he:∀ a:ℕ,∀ j:List ι, spanP n (ticketB (lank P) (price L n) a j) from he j.length j
 intro a; induction a with
 | zero=> exact fun _=>grandP
 | succ a ih=> intro j; cases j with
            | nil=> exact grandP
            | cons i j=> rw [ticketB]; exact sumB (spanT (slap P i) (ih _)) (mountT 0 _ (picks j) (fun x p=> spanT (by rw [side]; exact spanS (spanS grandP _) _) (ih _)))
abbrev pod (n:Type*)[LinearOrder n][Fintype n]:Wave n:=basisKet (∅:Finset n)
lemma borderE {F G:FC n}(h:spanP n F)(p:spanP n G)(g: acts F (pod n)=acts G (pod n)): F=G:=by
 apply Eq.trans h; refine Eq.trans ?_ p.symm; apply sum_congr rfl; intro i _; apply congrArg (· • _); exact (basis_act F i ∅).symm.trans ((congrArg (fun x:Wave n=> x.ofLp i) g).trans (basis_act G i ∅))
variable [LinearOrder ι][Fintype ι]
abbrev LinkI(ι n:Type*):= Lex (ι⊕ n)
abbrev seenH:n ↪ LinkI ι n := ⟨Sum.inr,fun _ _ h=>Sum.inr.inj h⟩
abbrev flame:ι↪ LinkI ι n:= ⟨Sum.inl,fun _ _ h=>Sum.inl.inj h⟩
-- test instance & deck
lemma dH :Deck (seenH (ι:=ι) (n:=n)) ∅:= ⟨by simp⟩
abbrev smallH(w:ι→ι→ℂ)(i:ι): FC (LinkI ι n):= ∑ j, w i j • takeF (flame j)
abbrev largeH(P:ι→n→ℂ)(i:ι):FC (LinkI ι n):= put (flame i) + ∑ j, P i j • put (seenH j)
lemma minus_sum (X Y Z: FC n): antiB X (Y+Z)=antiB X Y+antiB X Z:=by unfold antiB; simp only [mul_add,add_mul]; abel
lemma plus_sum (X Y Z:FC n): antiB (X+Y) Z=antiB X Z+antiB Y Z:=by unfold antiB; simp only [mul_add,add_mul]; abel
lemma distinguish(i:ι)(j:n): flame i ≠ seenH j:=fun (h: Sum.inl (β:=n) i=Sum.inr j)=> by contradiction
lemma shoot (P:ι→n→ℂ)(w:ι→ι→ℂ)(i j : ι):antiB (smallH w i) (largeH P j)= price w (LinkI ι n) i j:=by
 unfold smallH largeH; rw [minus_sum]; simp_rw [antiB_sum,antiB_sum',antiB_smul,antiB_smul',antiB, mixed]; simp only [distinguish,if_false,Embedding.apply_eq_iff_eq,smul_zero,sum_const_zero,add_zero,smul_ite]; simp only [sum_ite_eq',mem_univ,if_true]; rfl
lemma clash(P:ι→n→ℂ)(w:ι→ι→ℂ)(i j :ι):antiB ((largeH P+smallH (n:=n) w) i) ((largeH P+smallH (n:=n) w) j)=price w (LinkI ι n) i j+price w (LinkI ι n) j i:=by
 have h: antiB (largeH P i) (largeH P j)=0:=by unfold largeH; simp_rw [plus_sum, minus_sum,antiB_sum,antiB_sum',antiB_smul,antiB_smul',antiB, put_put]; simp
 have hg:antiB (smallH (n:=n) w i) (smallH w j)=0:=by unfold smallH; simp_rw [antiB_sum,antiB_sum',antiB_smul,antiB_smul',antiB,take_take]; simp
 rw [Pi.add_apply,Pi.add_apply]
 rw [plus_sum (largeH P i),minus_sum _ (largeH P j),minus_sum _ (largeH P j),h,hg, shoot P w, antiB_comm (smallH (n:=n) w j) (largeH P i),shoot]; abel
lemma pitchA(P:ι→n→ℂ)(w:ι→ι→ℂ)(j:List ι): acts (taskC (lank P) (price w n) j) (pod n)=pailL seenH ∅ (chime (largeH P+smallH w) (pod _) j):=by
 let g:=largeH P; let f:= g + smallH w; let p:= pod (LinkI ι n); let B':= largeH P
 have h : p=hoist seenH ∅ (pod n):=by rw [pod,hoops,knot_empty]
 have hz(i:ι):acts (smallH w i) p=0:=by
    unfold smallH; rw [act_sum]; apply sum_eq_zero; intro j _; rw [act_smul]; rw [show acts (takeF (flame j)) p=0 from ?_,smul_zero]
    unfold p pod; exact Eq.trans (take_act (n:=LinkI ι n) _ _) (if_neg (notMem_empty _))
 let R: Deck (@seenH ι n) ∅:= dH
 have hx(i j:ι):antiB (smallH w i) (f j)=price w (LinkI ι n) i j:=by
    unfold f g; rw [Pi.add_apply,minus_sum,shoot]; unfold smallH; simp only [antiB_sum',antiB_sum,antiB_smul,antiB_smul',antiB,take_take,smul_zero,sum_const_zero,add_zero]
 have he(i:ι)(x:Wave (LinkI ι n)):pailL seenH ∅ (acts (largeH P i) x)=acts (lank P i) (pailL seenH ∅ x):=by
    have hp:flame (n:=n) i∉ lows seenH:=by simp only [lows,Finset.mem_map,mem_univ,true_and]; rintro ⟨j,h⟩; exact distinguish i j h.symm
    unfold largeH lank; rw [act_add,map_add,show pailL seenH ∅ (acts (put (flame i)) x)=0 from branchX seenH ∅ R hp (notMem_empty _) _,zero_add,act_sum,map_sum,act_sum]
    exact sum_congr rfl fun j _=> by rw [act_smul,map_smul,act_smul,show pailL seenH ∅ (acts (put (seenH j)) x)=_ from petals _ ∅ R j x]
 have hh:=devote f g (smallH w) _ p (pailL _ ∅) w rfl hz hx he j; rw [show pailL _ ∅ p= pod n from h ▸ pourL _ _ R _] at hh; exact hh.symm
end YM.CF.Stilo
