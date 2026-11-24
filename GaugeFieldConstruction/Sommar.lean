import GaugeFieldConstruction.Lathy
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Roots.Connect
open Function Filter Metric MeasureTheory Finset Mew
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I J K X Y T E F:Type*}[LinearOrder I][LinearOrder J][LinearOrder K][Fintype I][Fintype J][Fintype K][DecidableEq X][DecidableEq Y][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℂ F][CompleteSpace F] [DecidableEq T]
variable (σ:I→X)(t:J→X)(C:J→ Key I)(ρ:K→Y)(τ:J→Y)(A:J→Key K)
-- expansion.Span.
abbrev Lands (V:Finset X)(R:Finset I):Prop:= Set.InjOn σ (↑R) ∧ (∀ i∈R,σ i∈V)
-- representable functions at all keys.
inductive Hatch (σ:I→X) (E:Type*) [NormedAddCommGroup E][NormedSpace ℂ E] (V:Finset X): (Key I→ E)→Prop where
| mon(R:Finset I)(u:Lands σ V R)(x:E):Hatch σ E V (fun z=> Mew.pine R z • x)
| nil:Hatch σ E V 0
| add (f g:Key I→E):Hatch σ E V f→ Hatch σ E V g → Hatch σ E V (fun x=>f x+g x)
variable {f g:Key I→ E}
lemma Hatch.rivers (V:Finset X)(p:Hatch σ E V f):River f:=by induction p with| mon R _ x=>exact lift_b _ _| nil=>exact zeroR _| add _ _ _ _ h v=>exact dub_V h v
lemma Hatch.cost (V:Finset X)(p:Hatch σ E V f): f=palm_R f σ:=by
 let R:=realm_C σ; have h(i:Finset I)(v:i∈R):i.sort (· ≤ ·)=_:= (rfl : Mew.Cue I i=Mew.Cue I i) -- remove
 induction p with
 | mon i t x=>
    let F(z):= Mew.pine i z • x; have ht:i∈R:= mem_filter.mpr ⟨mem_univ _,t.1⟩
    have hA(j:Finset I): gemI F j=if j=i then x else 0:=(tip_tape _ (Finset.sort_nodup ..) i x).trans (by rw [Finset.sort_toFinset]) -- name
    funext z; change F z= ∑ j∈R,Mew.pine j z • gemI F j; simp_rw [hA]; rw [sum_eq_single_of_mem i ht]; · rw [if_pos rfl]
    intro b _ e; rw [if_neg e,smul_zero]
 | nil=> funext z; change (0:E)=∑ j∈R,Mew.pine j z • tipI _ _; exact Eq.symm (sum_eq_zero fun j h=>by rw [show tipI (0:Key I→E) _=0 from tip_0 _,smul_zero])
 | add u v p q r e=>
    funext z; refine (congrArg₂ (·+·) (congrFun r z) (congrFun e z)).trans ?_; unfold palm_R seedΞ gemI; rw [←sum_add_distrib]; exact sum_congr rfl fun i _=>by rw [tip_A (p.rivers ..) (q.rivers ..),smul_add] -- inductive circular
lemma Hatch_enlarge {V W:Finset X}(p:Hatch σ E V f)(t:V⊆W): Hatch σ E W f:=by induction p with
 | mon R u x=>exact Hatch.mon R ⟨u.1,fun i h=> t (u.2 _ h)⟩ _
 | nil=>exact Hatch.nil
 | add _ _ _ _ h v=>exact Hatch.add _ _ h v
lemma Hatch.sum (s:Finset T)(V:Finset X)(u:T→ Key I→ E)(t:∀ i∈s,Hatch σ E V (u i)):Hatch σ E V (fun x=>∑ j∈s,u j x):=by
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Hatch.nil
 | insert i s h ih=> simp_rw [sum_insert h]; exact Hatch.add _ _ (t i (mem_insert_self ..)) (ih fun j l=> t j (mem_insert_of_mem l))
lemma Hatch_prod (V W:Finset X)(p:Disjoint V W){F: Key I→ℂ}(h:Hatch σ ℂ V F)(g:Hatch σ E W f): Hatch σ E (V∪ W) (fun x=>F x • f x):=by
 induction h with
 | mon R t z=>
    induction g with
    | mon R' u x=>
       let C:=R∪ R'; have ht(x y)(p:x∈R)(q:y∈R'):σ x≠σ y:=fun e=>Finset.disjoint_left.mp ‹Disjoint V W› (t.2 x p) (e.symm ▸ u.2 y q)
       have hD: Disjoint R R':= Finset.disjoint_left.mpr (fun x h=> fun g=> ht x x h g rfl) -- x implicit!
       have he:Lands σ (V∪W) C:=by
          refine ⟨fun i v j w p=>?_,fun i q=>?_⟩
          · rcases mem_union.mp v with v|v<;> rcases mem_union.mp w with w|w
            exact t.1 v w p
            exact False.elim (ht _ _ v w p)
            exact False.elim (ht _ _ w v p.symm)
            exact u.1 v w p
          exact (mem_union.mp q).elim (fun h=>mem_union_left _ (t.2 i h)) (fun h=> mem_union_right _ (u.2 i h))
       change Hatch _ _ _ (fun x' : Key I=>_)
       rw [show (fun a:Key I=>(pine R a • z) • pine R' a • x)=(fun a:Key I=>pine C a • z • x) from ?_]; · exact Hatch.mon C he _
       funext a; unfold pine C; rw [prod_union hD]; rw [smul_smul,smul_smul]; change ((∏ i∈R,a i)* z * (∏ i∈R',a i)) • x = _; rw [mul_right_comm] -- pine unfold 1 occurrence
    | nil=> simp only [Pi.zero_apply,smul_zero]; exact Hatch.nil
    | add H K' _ _ h f=> simp_rw [smul_add]; exact Hatch.add _ _ h f
 | nil=> simp only [Pi.zero_apply,zero_smul]; exact Hatch.nil
 | add u v _ _ h k=> simp_rw [add_smul]; exact Hatch.add _ _ h k
variable (u:Tours σ t C)
include u
lemma Hatch_comp {V:Finset X}(p:Hatch σ E V f): Hatch t E V (fun x=>f (SpotQ C x)):=by
 induction p with
 | mon R h e=>
    have ht(i:I):Hatch t ℂ {σ i} (fun x=>SpotQ C x i):=by
       have he(x): SpotQ C x i=∑ j: J,x j*C j i:= Finset.sum_apply _ _ _ -- tune
       simp_rw [he]; refine Hatch.sum t univ _ (fun j x=> x j*C j i) (fun j _=>?_) -- η
       by_cases w:t j=σ i
       · have hc:Lands t {σ i} {j}:=by simp only [Finset.mem_singleton, Lands,coe_singleton, Set.injOn_singleton,true_and]; exact fun _ e=> e.symm ▸ w -- tune
         exact (show _ from (by simpa [pine] using (Hatch.mon (σ:=t) {j} hc (C j i))))
       have hx:C j i=0:= u j i fun h=>w ((mem_filter.mp h).2.symm); simp_rw [hx,mul_zero]; exact Hatch.nil
    suffices hR:Hatch t E (R.image σ) (fun x=>pine R (SpotQ C x) • e) from Hatch_enlarge t hR (fun i p=>by obtain ⟨j,t,rfl⟩:=mem_image.mp p; exact h.2 _ t)
    induction R using Finset.induction_on with
    | empty=>
       have he:Lands t ∅ ∅:=by simp [Lands]
       simpa [pine] using (Hatch.mon (σ:=t) ∅ he e) -- indent
    | insert i r q ih=>
       have hj:Lands σ V r:=⟨h.1.mono (Finset.coe_subset.mpr (subset_insert ..)),fun i v=> h.2 _ (mem_insert_of_mem v)⟩
       have he: Disjoint {σ i} (r.image σ):=Finset.disjoint_left.mpr fun _ u v=>by obtain ⟨k,p,e⟩:=mem_image.mp v; have hd:k=i:=h.1 (mem_insert_of_mem p) (mem_insert_self ..) (e.trans (mem_singleton.mp u)); exact q (hd ▸ p)
       have hu:= Hatch_prod t _ _ he (ht i) (ih hj); simpa [pine,prod_insert q,mul_smul,image_insert] using hu
 | nil=>exact Hatch.nil
 | add _ _ _ _ ih v=>exact Hatch.add _ _ ih v
end YM.CF.Roots.Connect
end
