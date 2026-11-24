import YM.CF.BPress.Pf.Recursive
import YM.CF.BPress.Lily.Petal
import YM.CF.BPress.Palmer.School
/-! VolumeB-poly Pf rule. Auxiliary exterior (OVER LETTERS, not CAR of physics) only to price the two-type ordered Wick values. Laplace formula proved here; sign factoring of decorated Wick terms will be through THIS pure exterior and sectors. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable (C:Op I) (l:List I)
abbrev raw (l:List I):FC I:= (l.map Fock.put).prod
lemma raw_join (k:List I) : raw (l++k)=raw l*raw k:=by simp [raw,List.prod_append]
local notation "Ω"=>vacuum I
def shape (C: Op I)(l:List I):= inner ℂ (acts (raw l) Ω) (pairWave C)
lemma shape_void : shape C []=1:=by rw [shape, show raw []=(1:FC I) from rfl,act_one,vacuum,basis_inner,paired_vac]
private lemma apart (i j:I): antiB (star (coupleRow C i)) (put j)=star (C i j) • 1:=by unfold coupleRow; rw [star_sum,antiB_sum]; simp_rw [star_smul,antiB_smul]; have he(k:I): antiB (star (put k)) (put j)=if k=j then 1 else 0:=mixed ..; simp_rw [he]; rw [sum_eq_single j]; simp; intro k _ h; simp [h]; simp -- tune
private lemma light (i:I):acts (star (coupleRow C i)) Ω=0:=by unfold coupleRow; rw [star_sum,act_sum]; apply sum_eq_zero; intro x _; rw [star_smul,act_smul,show star (put x)=takeF x from rfl,← remove_take,vacuum_take,smul_zero] -- tune
-- commute formal pair through pure word, exact Pf recurrence.
theorem linear (k:List I)(i : I) : inner ℂ (acts (raw k * star (coupleRow C i) *raw l) Ω) (pairWave C)= dues (C i) (shape C) k l:=by
 induction l generalizing k with
 | nil=> unfold dues; simp only [fee]; rw [show raw []=(1:FC I) from rfl,mul_one,act_mul,light,map_zero,inner_zero_left]
 | cons j l ih=>
   let P:= put j; let S:=star (coupleRow C i); let A:= raw k; let B:=raw l
   rw [show raw (j::l)=P*B from rfl,←mul_assoc _ P, mul_assoc (raw k) S P, eq_sub_of_add_eq (apart C i j)]; unfold dues; rw [mul_sub,sub_mul,act_sub, inner_sub_left,fee]; apply congrArg₂ (·-·); · rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc,act_smul,mul_one,inner_smul_left,shape,raw_join]; simp [B] -- tune
   have he: A*P=raw (k++[j]):=by rw [raw_join]; simp [A,P,raw]
   rw [←mul_assoc A, he]; exact ih _ -- tune
lemma shape_cons (i:I)(h:Cᵀ= -C): shape C (i::l) = dues (C i) (shape C) [] l := by
 rw [shape]; rw [show raw (i::l)= put i*raw l from rfl,act_mul]; nth_rw 1 [←star_star (put i)]; rw [act_inner,pull h]; rw [←act_inner,←act_mul]; let X:=shape C; simpa only [show (raw ([]:List I))= (1:FC I) from rfl,one_mul] using linear C l [] i -- tune pull star abbreviation
-- runtime f evaluated recursively only on permitted order (e.g. stable species) including sublists. equality proof by rec local functions.
structure ShapeFit(C:Op I)(l:List I)(F:List I→ℂ):Prop where
 pay(i:I)(k:List I) (p:(i::k).Sublist l): F (i::k)=dues (C i) F [] k
 void:F []=1
lemma fee_exact {l L:List I}{i:I}{F G: List I→ℂ}(p:∀ k,k.Sublist (L++l) → k.length < L.length+l.length+1→ F k= G k): dues (C i) F L l=dues (C i) G L l:=by
 induction l generalizing L with|nil=>rfl|cons j l ih=>
    unfold dues; rw [fee,fee]; apply congrArg₂ (·-·)
    · rw [p (L++l) (List.Sublist.append_left (.cons j (List.Sublist.refl l)) L) (by simp)] -- tune placeholders
    refine ih (p:=?_) -- tune returns equality with ++
    intro m t q; apply p m; · simpa only [List.append_assoc,List.cons_append,List.nil_append] using t
    rw [List.length_cons]; rw [List.length_append,List.length_singleton] at q; omega
lemma ShapeFit.coin {C:Op I}{l:List I}{F:List I→ℂ}(p:ShapeFit C l F)(t:Cᵀ= -C): F l=shape C l := by
 generalize h:l.length=n; induction n using Nat.strong_induction_on generalizing l with|h n ih=>
    cases l with|nil=>exact p.void.trans (shape_void _).symm|cons i l=> rw [p.pay i l (List.Sublist.refl _),shape_cons _ _ _ t]; apply fee_exact; intro k v x; let v':= v.trans (show (([]:List I)++l).Sublist (i::l) from (.cons _ (List.Sublist.refl _))); refine ih k.length ?_ ⟨fun i l u=> p.pay _ _ (u.trans v'),p.void⟩ rfl; rw [List.length_cons] at h; simpa only [List.length_nil, zero_add, ←h] using x -- tune arg k order
end YM.CF.BPress.Pine
