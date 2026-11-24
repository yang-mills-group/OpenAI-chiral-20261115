import YM.CF.BProof.Crystal.Link
/-! Mandatory ordered Wick value on vertex subsets with specific exclusions.
Expanding ordinary (``type-2'') separately from insertion vertices makes it
unnecessary to postulate a CAR reordering identity between types. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Crystal.Dew
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {V I U J R K: Type}[DecidableEq V][DecidableEq U][Fintype V][Fintype U]
variable [Fintype I][LinearOrder I][Fintype J][LinearOrder J][Fintype K][LinearOrder K] [Fintype R][LinearOrder R]
def addD(A:Dew V I)(B:Dew U I): Dew (V⊕U) I where
 line:= Sum.elim A.line B.line
 free:= fun i=>Sum.elim (fun x=>Sum.elim (fun y=>A.free x y) (fun _=>True)) (fun x=>Sum.elim (fun _=>True) (fun y=>B.free x y)) i
 fresh:= fun i=> by cases i; exact A.fresh _; exact B.fresh _
 even:= fun i=> by cases i; exact A.even _; exact B.even _
def castD(A:Dew V I)(e:I↪J): Dew V J where
 line:=fun i=>(A.line i).map e
 free:=A.free
 fresh:=fun i=>(A.fresh i).map e.injective
 even:=fun i=>by simpa only [List.length_map] using A.even i
lemma whole (A:Dew V I)(B:Dew U I)(S: Finset V)(T: Finset U): (A.addD B).mild (S.disjSum T) ↔ A.mild S ∧ B.mild T:=by
 constructor
 · intro h; constructor; · intro i hi j hj e; exact h (show Sum.inl i ∈ S.disjSum T from inl_mem_disjSum.mpr hi) (show Sum.inl j ∈ S.disjSum T from inl_mem_disjSum.mpr hj) (fun t=>e (Sum.inl.inj t))
   intro i hi j hj e; exact h (show Sum.inr i ∈ S.disjSum T from inr_mem_disjSum.mpr hi) (show Sum.inr j ∈ S.disjSum T from inr_mem_disjSum.mpr hj) (fun t=>e (Sum.inr.inj t)) -- indent tune
 rintro ⟨a,b⟩ (i|i) hi (j|j) hj e; exact a (inl_mem_disjSum.mp hi) (inl_mem_disjSum.mp hj) (fun t=>e (by rw [t])); exact trivial; exact trivial; exact b (inr_mem_disjSum.mp hi) (inr_mem_disjSum.mp hj) (fun t=>e (by rw [t]))
lemma disjSum {D:Type*}[AddCommMonoid D](X:Finset (V⊕U)→D): ∑ i,X i=∑ i:Finset V,∑ j:Finset U,X (i.disjSum j):=by
 rw [← Equiv.sum_comp (Finset.sumEquiv.symm.toEquiv) X,Fintype.sum_prod_type]; rfl
lemma feed (A:Dew V I)(B:Dew U I)(S: Finset V)(T: Finset U): (A.addD B).beam (S.disjSum T) = A.beam S * B.beam T:=by rw [beam,prod_disjSum]; rfl
lemma hollowM (a b:ℂ) : (hollow (n:=I) a)*hollow b=hollow (a*b):=Subtype.ext (by change (a • (1:FC I))*(b • (1:FC I))= _; rw [Algebra.smul_mul_assoc,one_mul]; exact (mul_smul _ _ _).symm)
def wrap (A:Dew V I)(F:V→ℂ)(S:Finset V):Dough I:= if A.mild S then hollow (∏ i∈ S,F i)*A.beam S else 0
def foldS(A:Dew V I)(F:V→ℂ): Dough I:= ∑ i:Finset V,A.wrap F i
theorem phaseFold (A:Dew V I)(B:Dew U I)(F:V→ℂ)(G:U→ℂ): (A.addD B).foldS (Sum.elim F G)=A.foldS F *B.foldS G:=by
 unfold foldS; rw [disjSum,sum_mul]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j _; unfold wrap; rw [prod_disjSum,whole]; by_cases p:A.mild i; swap; · simp [p]
 by_cases g:B.mild j; simp only [p,g, and_self, ↓reduceIte, Sum.elim_inl,Sum.elim_inr]; rw [← hollowM, feed,mul_mul_mul_comm]; simp only [p,g,and_false,↓reduceIte,mul_zero]
-- valuation of an oven
lemma cookEven (v:Poly I K)(l:List I)(f:Even l.length): v.eval (word l)=rollC v.term l:=by
 induction l using List.twoStepInduction with
 | nil=> exact v.eval_one
 | singleton i=> simp at f
 | cons_cons i j l ih=>
   have ht:Even l.length:=by simpa only [List.length_cons,Nat.even_add_one,not_not] using f
   let B:Dough I:=⟨_,(wordP l ht (subset_univ _)).1⟩; rw [word_c,word_c,←mul_assoc, show v.eval (put i*put j * word l)= v.eval (put i*put j)*v.eval (word l) from v.eval_mul (cell i j) B,v.eval_double, ih ht]; unfold rollC; simp only [List.map_cons,List.prod_cons,mul_assoc]
-- pair-wise type order
abbrev Flame(I J:Type):= I ⊕ₗ J
abbrev bendL : I ↪ Flame I J:= Function.Embedding.inl.trans toLex.toEmbedding
abbrev bendR : J ↪ Flame I J:= Function.Embedding.inr.trans toLex.toEmbedding
def fire(A:Dew V I)(B:Dew U J):= (A.castD (bendL (J:=J))).addD (B.castD bendR)
def polite(i j:Flame I J):Prop:= Sum.elim (fun _=>True) (fun _=> (ofLex j).isRight) (ofLex i) -- Bool? coerces Sort
lemma kind(l:List I)(t:List J): (l.map bendL++t.map bendR).Pairwise (@polite I J) := by
 rw [List.pairwise_append]; refine ⟨?_,?_,?_⟩; · rw [List.pairwise_map]; exact List.pairwise_of_forall (fun a b =>trivial) -- tune
 · rw [List.pairwise_map]; exact List.pairwise_of_forall (fun a b=> by change true=true; rfl)
 intro i hi j hj; obtain ⟨x,d,rfl⟩:=List.mem_map.mp hi; exact trivial
lemma mappedWord(e:I↪J)(A:Dew V I)(l:List V)(t:l.Nodup) : ((A.castD e).beam l.toFinset).val=word ((l.flatMap A.line).map e):=by rw [beamWord _ l t]; congr ; simp only [castD,List.map_flatMap]
lemma duoString(A:Dew V I)(B:Dew U J)(S:List V)(T:List U)(u:S.Nodup)(v:T.Nodup)(C:Op (Flame I J)): let L:=(S.flatMap A.line).map (bendL (J:=J)); let R:=(T.flatMap B.line).map (bendR (I:=I)); (A.fire B).magic C (S.toFinset.disjSum T.toFinset)= Nose C (L++ R):=by
 intro L R; unfold magic Nose fire; rw [feed,chime]; change _=inner ℂ _ (acts (word (L++R)) _); congr 2; rw [word_ap,← mappedWord bendL A S u,←mappedWord bendR B T v]; rfl
variable (A:Dew V I)(B:Dew U J)(v:Poly I K)(y:Poly J K)(F:V→ℂ)(G:U→ℂ)(z:FC K→ₗ[ℂ] ℂ) {C:Op (Flame I J)}
def act(v:Poly I K)(y:Poly J K): Flame I J → FC K:=Sum.elim v.term y.term ∘ ofLex
lemma flatEven(A:Dew V I)(L:List V) : Even (L.flatMap A.line).length:=by induction L with| nil=> simp| cons i L ih=> rw [List.flatMap_cons,List.length_append]; exact (A.even i).add ih
lemma evalGiven(l:List V)(h:l.Nodup): v.cook (A.beam l.toFinset)=rollC v.term (l.flatMap A.line):=by change v.eval _=_; rw [A.beamWord l h,cookEven v _ (flatEven ..)]
lemma couple (l:List I)(t:List J): rollC (act v y) (l.map bendL ++ t.map bendR)=rollC v.term l * rollC y.term t:=by simp only [rollC,List.map_append,List.prod_append,List.map_map]; congr 2 
lemma cookPoly (x:Dough I)(c:ℂ):v.cook (hollow c*x)=c • v.cook x:=by rw [map_mul,cookH,Algebra.smul_mul_assoc,one_mul]
variable {d: Flame I J→ Flame I J→ℂ}(m:Scores d (fun l=> z (rollC (act v y) l))) (e:∀ i j, polite i j→ d i j=C i j)(u:Cᵀ= -C)
include m e u in
theorem relay : z (v.cook (A.foldS F)*y.cook (B.foldS G))=∑ Z: Finset (V⊕U),(A.fire B).silica (Sum.elim F G) C Z:=by
 unfold foldS; rw [Dew.disjSum,map_sum,map_sum, sum_mul,map_sum]; apply sum_congr rfl; intro i _; rw [mul_sum,map_sum]; apply sum_congr rfl; intro j _
 unfold silica wrap; rw [show (A.fire B).mild (i.disjSum j) ↔ A.mild i∧ B.mild j from whole ..]; by_cases k:A.mild i; swap; · simp only [k,false_and,ite_false,map_zero,zero_mul]
 by_cases f:B.mild j; swap; · simp only [f,and_false,ite_false,map_zero,mul_zero]
 rw [if_pos k, if_pos f, if_pos ⟨k,f⟩, prod_disjSum]; simp only [cookPoly,Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul, smul_eq_mul,Sum.elim_inl,Sum.elim_inr]; rw [mul_assoc]
 -- assuming factors aligned, convert using strings
 let L:= i.toList; let R:=j.toList; let l:= L.flatMap A.line; let t:= R.flatMap B.line; have hl: L.toFinset=i:= toList_toFinset ..; have hr: R.toFinset=j:= toList_toFinset ..; rw [←hl,←hr]; have hx:L.Nodup:=nodup_toList ..; have ht:R.Nodup:=nodup_toList ..
 rw [duoString A B L R hx ht,← compatible u m e ((l.map bendL)++(t.map bendR)) (kind ..),couple,evalGiven A v _ hx,evalGiven B y _ ht]; exact mul_left_comm .. 
end YM.CF.BProof.Crystal.Dew
