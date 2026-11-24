import YM.CF.Buffered.Occupancy
/-! Estimate #non-quiescent unshared tiles by number of deep-tail factors.
The *limited order* of each factor and the allowance for arbitrary additional
particles need to be tracked. DON'T commute error terms and local terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Cache
open Function Filter Metric Fock Finset Flare
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n] [LinearOrder n]
variable {m:Type*} [Fintype m] [DecidableEq m]
variable {S:n→m}
inductive Deal where
 | zero -- local P F P
 | left -- local Q F
 | right -- local P F Q
 | error -- full - local
 deriving DecidableEq, Fintype
namespace Deal
variable (S) (W:Finset n)
def eval (A B: FC n) (x:m) : Deal→ FC n | zero => fixed S W x * A * fixed S W x | left => (1-fixed S W x)*A | right=>fixed S W x*A*(1-fixed S W x) | error=> B
omit [Fintype m] in
lemma total (A B:FC n)(x:m): eval S W A B x zero+eval S W A B x left+eval S W A B x right+eval S W A B x error=A+B:=by unfold eval; rw [sub_mul,mul_sub,one_mul,mul_one]; change ((fixed S W x)* A * (fixed S W x)+ (A-_))+ (_-_)+_= _; generalize fixed S W x * A * fixed S W x=u, fixed S W x * A = v; abel
variable {S W} {A B:FC n}{x y:m}
omit [Fintype m] in
private lemma gives {s t:Finset n}(v:Deal)(p:v≠error)(h: eval S W A B x v s t≠0): A s t≠0:=by
 intro he; cases v <;> simp_all [eval, fix_left,fix_right,sub_mul,mul_sub,one_mul,mul_one]
def costs : Deal→Bool | left => true | right=>true | _ => false
def charge (j:ℕ) : Deal→ℕ | error=>j | _ => 0
def hits (D:Deal)(S:n→m) (s t:Finset n) := if D=error then changes S s t else ∅
lemma hit {j:ℕ}{s t:Finset n}{x:m}(D:Deal)(h: eval S W A B x D s t≠0) (g:ChangeBill S j B) : (hits D S s t).card≤charge j D:=by cases D <;> first | (solve | simp [hits,charge]; done)| simpa [hits,charge] using g s t h
lemma scatter {s t: Finset n}(D:Deal)(h: eval S W A B x D s t≠0) (g:Sector (variety S x) false A) (e:x≠y) (t':y∈changes S s t) : y∈hits D S s t:=by
 unfold hits; split; exact t'; next p=> exact False.elim ((mem_filter.mp t').2 (exclusive S g (gives D p h) e))
lemma stimulus {s t:Finset n}{x:m}(D:Deal)(p:costs D)(h:eval S W A B x D s t ≠ 0): x∈changes S s W ∨ x∈changes S t W:=by
 cases D with
 | left=>
   refine Or.inl (mem_filter.mpr ⟨mem_univ _, fun g=>?_⟩); apply h; rw [eval,sub_mul,one_mul,Matrix.sub_apply,fix_left,if_pos g,sub_self]
 | right=>
   refine Or.inr (mem_filter.mpr ⟨mem_univ _, fun g=>?_⟩); apply h; rw [eval,mul_sub,mul_one,Matrix.sub_apply,fix_right,if_pos g,sub_self]
 | _=>cases p
end Deal
abbrev Cart (m:Type*) := List (m×Deal)
variable (S) (W:Finset n)(A B:m→ FC n)
def crate (p:m×Deal) := Deal.eval S W (A p.1) (B p.1) p.1 p.2
def story (L:Cart m) := (L.map (crate S W A B)).prod
variable {S W A B} {j k:ℕ} (p:∀ x,Sector (variety S x) false (A x))(g:∀ x,ChangeBill S j (B x))
omit [Fintype m][DecidableEq m] in
abbrev xp (L:Cart m)(j:ℕ):= (L.map (fun t=>Deal.charge j t.2)).sum
abbrev live (L:Cart m):= (L.filter (fun t=>t.2.costs)).map Prod.fst
variable {Z:FC n} (h:ChangeBill S k Z)
include p g h
private lemma harvest (L: Cart m)(x:(L.map Prod.fst).Nodup) {s: Finset n}(he: (story S W A B L * Z) s W ≠ 0) : ∃ X: Finset m,X.card ≤ xp L j + k ∧ (∀ i∈live L,i∈changes S s W ∨ i∈X) ∧ changes S s W ⊆ (L.map Prod.fst).toFinset ∪ X := by
 induction L generalizing s with
 | nil => rw [story,List.map_nil,List.prod_nil,one_mul] at he; exact ⟨changes S s W,by simpa [xp] using h s W he,fun i e=> List.not_mem_nil e |>.elim,by simp⟩
 | cons t L ih =>
   rw [story,List.map_cons,List.prod_cons, mul_assoc,←story,Matrix.mul_apply] at he
   obtain ⟨w,_,t'⟩:= exists_ne_zero_of_sum_ne_zero he; let l:= (L.map Prod.fst)
   rw [List.map_cons,List.nodup_cons] at x
   obtain ⟨T,H,P,U⟩:= ih x.2 (right_ne_zero_of_mul t'); have hy:crate S W A B t s w≠0:=left_ne_zero_of_mul t'
   let R:= t.2.hits S s w
   have hr(i:m)(p':t.1 ≠ i)(hi:i∈changes S w s) : i∈R:= Deal.scatter t.2 hy (p _) p' (changes_comm (S:=S) s w ▸ hi)
   refine ⟨R∪T, (card_union_le ..).trans ((Nat.add_le_add (Deal.hit t.2 hy (g _)) H).trans ?_),?_,?_⟩
   · simp [xp,add_assoc]
   · intro i e
     have hx : i∈live L → i∈changes S s W ∨ i∈R∪T:=by
        intro hl
        obtain v|v:=P i hl
        · obtain l'|l':=mem_union.mp (changes_union w W s v)
          · refine Or.inr (mem_union_left _ (hr i ?_ l')); intro hh; refine x.1 ?_; rw [hh]; exact ((List.filter_sublist).map Prod.fst).subset hl
          exact Or.inl l'
        exact Or.inr (mem_union_right _ v)
     cases hb:t.2.costs
     · apply hx; simpa only [live,List.filter_cons,hb,Bool.false_eq_true,ite_false] using e
     simp only [live,List.filter_cons,hb,ite_true,List.map_cons,List.mem_cons] at e
     rcases e with e|e
     · subst i
       obtain q|q:=Deal.stimulus t.2 hb hy; exact Or.inl q
       exact Or.inr (mem_union_right _ ((Finset.mem_union.mp (U q)).resolve_left (by exact fun v=> x.1 (List.mem_toFinset.mp v))))
     exact hx e
   intro i v; simp only [List.map_cons,List.toFinset_cons]; by_cases b:t.1=i
   · exact mem_union_left _ (mem_insert.mpr (Or.inl b.symm))
   obtain u|u :=mem_union.mp (changes_union s W w v)
   · exact mem_union_right _ (mem_union_left _ (hr _ b (changes_comm (S:=S) w s ▸ u)))
   rcases mem_union.mp (U u) with v|v; exact mem_union_left _ (mem_insert_of_mem v); exact mem_union_right _ (mem_union_right _ v)
lemma frequencies (L:Cart m)(x:(L.map Prod.fst).Nodup) (he: (story S W A B L*Z) W W≠0): (live L).length ≤ xp L j+k:=by
 obtain ⟨T,g,v,U⟩:= harvest p g h L x he
 have hx: (live L).Nodup:= x.sublist ((List.filter_sublist).map Prod.fst)
 rw [←List.toFinset_card_of_nodup hx]; exact (card_le_card (fun i hi=> (v i (List.mem_toFinset.mp hi)).resolve_left (by simp [changes]))).trans g
end YM.CF.Buffered.Cache

#print axioms YM.CF.Buffered.Cache.frequencies
