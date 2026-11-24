import YM.CF.Operator.Basic
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Finset Filter
-- l1 Corners. Abstract absolute convex finite hull for keeping all ballots' prices. Not assuming positivity of unreflected expectation. K weights exact.
variable {V:Type*}[AddCommGroup V][Module ℂ V]
inductive Blend (Q: V→Prop): ℝ→ V→ Prop where
 | item (A:V): Q A → Blend Q 1 A
 | smul {A:V}{k:ℝ}: Blend Q k A→∀ c:ℂ,Blend Q (‖c‖*k) (c • A)
 | join {k d:ℝ}{A B:V}: Blend Q k A→Blend Q d B→ Blend Q (k+d) (A+B)
 | zero: Blend Q 0 0
 | extendsTo {v w:ℝ}{A:V}:Blend Q v A→v≤w→ Blend Q w A
variable {R S Q:V→Prop} {A:V}{k:ℝ}
lemma Blend.proper (h: Blend Q k A): 0≤k:=by induction h with|item A p=> norm_num | smul p c h=> positivity|zero=> rfl| extendsTo _ u h=>exact h.trans u|join _ _ h q=> positivity
-- flexible embedded & used in price.
lemma Blend.tight (p:Blend Q k A){h:ℝ}(t:0≤h)(g:∀ i,Q i→ Blend R h i): Blend R (k*h) A := by
 induction p with
 | extendsTo _ e ih=> exact ih.extendsTo (mul_le_mul_of_nonneg_right e t)
 | item i v=> rw [one_mul]; exact g i v
 | zero=> rw [zero_mul]; exact .zero
 | smul p a ih=> rw [mul_assoc]; exact ih.smul a
 | join _ _ u v=> rw [add_mul]; exact u.join v
lemma Blend.mono (p:Blend Q k A)(t:∀ i,Q i→ S i): Blend S k A:= by simpa only [mul_one] using (p.tight zero_le_one fun i w=> .item i (t i w)) -- P undeclared
lemma Blend.charge (S:ℝ→ V→Prop)(p: Blend Q k A)(v:∀ i,Q i→ S 1 i)(t:S 0 0)(q:∀ (a b:ℝ) (X Y:V),S a X→S b Y→ S (a+b) (X+Y))(g: ∀ (a:ℝ) (X:V), S a X→∀ c:ℂ,S (‖c‖*a) (c • X))(u:∀ a b X,S a X→ a≤b→ S b X): S k A:=by induction p with| item A p=> exact v A p| join _ _ a b=> exact q _ _ _ _ a b| smul _ c a=> exact g _ _ a c| zero => exact t|extendsTo _ h t=>exact u _ _ _ t h
lemma Blend.sum {α:Type*}(S:Finset α)(f:α→V)(v:α→ℝ)(t:∀ a∈S, Blend Q (v a) (f a)):Blend Q (∑ i∈S,v i) (∑ i∈S,f i):=by
 classical
 induction S using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact .zero|insert a S q h=> rw [sum_insert q,sum_insert q]; exact (t a (mem_insert_self ..)).join (h (fun i hi=>t _ (mem_insert_of_mem hi)))
section mul
-- cost convolution both sides scalar algebra. No reordering.
variable {R:Type*}[Ring R][Algebra ℂ R](p q rb:R→Prop){v b:ℝ}{A B:R}
lemma Blend.merge (h:Blend p v A)(t:Blend q b B)(e:∀ i j:R,p i→q j→ rb (i*j)): Blend rb (v*b) (A*B):=by
 have ht(i:R)(g:p i): Blend rb b (i*B):=by induction t with
    | zero=> rw [mul_zero]; exact .zero
    | item A u=> exact .item _ (e _ _ g u)
    | smul _ c h=> rw [Algebra.mul_smul_comm]; exact h.smul _
    | join _ _ a b=> rw [mul_add]; exact a.join b
    |extendsTo _ q v=> exact v.extendsTo q
 induction h with
 | item i w=> rw [one_mul]; exact ht i w
 | zero=> rw [zero_mul,zero_mul]; exact .zero
 | smul _ c h=> rw [mul_assoc, Algebra.smul_mul_assoc]; exact h.smul _
 | join _ _ u v=> rw [add_mul,add_mul]; exact u.join v
 | extendsTo _ q h=> exact h.extendsTo (mul_le_mul_of_nonneg_right q t.proper)
end mul
variable {R:Type*}[Ring R][Algebra ℂ R]{α:Type*}{G:α→R→Prop}{v:α→ℝ}{F:α→R}
lemma Blend.prod (L:List α)(u:L.Nodup)(q:∀ i∈L, Blend (G i) (v i) (F i)) : Blend (fun x=> ∃ f:α→R,(∀ i∈L,G i (f i)) ∧ x=(L.map f).prod) (L.map v).prod (L.map F).prod:=by
 classical
 induction L with
 | nil=> exact .item _ ⟨fun i=>0,by simp⟩
 | cons i L ih=>
    apply Blend.merge _ _ _ (q _ List.mem_cons_self) (ih (List.nodup_cons.mp u).2 (fun i h=>q i (List.mem_cons_of_mem _ h)))
    rintro x _ g ⟨f,h,rfl⟩; refine ⟨Function.update f i x,fun j l=>?_,?_⟩
    · rcases List.mem_cons.mp l with l|l; · subst j; simpa using g
      rw [update_of_ne]; exact h _ l; intro p; exact (List.nodup_cons.mp u).1 (p ▸ l)
    · rw [List.map_cons,List.prod_cons,update_self,show L.map (Function.update f i x)=L.map f from ?_]; exact List.map_congr_left (fun j h=>update_of_ne (show j≠i from fun t=>(List.nodup_cons.mp u).1 (t ▸ h)) x f)
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Blend.prod
#print axioms Blend.sum
