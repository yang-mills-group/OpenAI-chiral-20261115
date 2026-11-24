import YM.CF.BProof.Tetrad.Words
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List
open scoped BigOperators Classical
abbrev weight :=wage false
abbrev polar:=wage true
def Last(x:Road)(c:Tone):Prop:=∃ u:Road,x=u++[c]
def First(x:Road)(c:Tone):Prop:=∃ u,x=c::u
@[simp] lemma last_nil(c):¬ Last [] c:=by simp [Last]
@[simp] lemma first_nil(c):¬First [] c:=by simp [First]
@[simp] lemma last_c (x:Road)(a c):Last (x++[a]) c ↔ a=c :=by simp [Last] -- simp left-append cancel?
@[simp] lemma first_c(x:Road)(a c):First (a::x) c↔ a=c:=by simp [First]
lemma easy(x y:Road)(a:Tone)(p:Line x)(q:Line y)(hx:¬ Last x a)(hy:¬First y a):Line (x++a::y):=by
 induction x using List.reverseRecOn with
 | nil=> cases y with | nil=> simp [Line]|cons b y=> simpa [Line] using And.intro (Ne.symm (show b ≠ a by simpa [First] using hy)) q
 | append_singleton x c _ =>
   have he:Line (a::y):=by cases y with | nil=>simp [Line]|cons b y=> simpa [Line] using And.intro (Ne.symm (show b≠a by simpa using hy)) q
   rw [List.append_assoc,List.cons_append,List.nil_append]; exact isChain_append_cons_cons.mpr ⟨p, fun h=>hx (last_c _ _ _|>.mpr h), he⟩
lemma clockwise(x:Road)(a:Tone)(p:Line x)(hx:¬ Last x a)(hy:¬First x a): smooth true (x++[a]):=by
 rw [smooth_app]; unfold smooth; simp only [if_true,List.cons_append,List.nil_append]
 cases x with
 | nil=> -- error: singleton Cycle chain false; choose length earlier
    left; simp
 | cons c x=>
   right; rw [Cycle.chain_coe_cons]; simp only [cons_append]; apply isChain_cons_cons.mpr; exact ⟨Ne.symm (show c≠a by simpa using hy), easy (c::x) [] a p List.IsChain.nil hx (first_nil _)⟩
lemma suit(x y:Road)(a:Tone)(p:Line x)(q:Line y): excerpt weight (x++a::y) = weight (x++a::y) + (if Last x a then 2*weight (x++y) else 0)+(if First y a then 2*weight (x++y) else 0) :=by
 unfold weight; by_cases ht: Last x a
 · obtain ⟨x,rfl⟩:=ht; simp only [if_pos (show Last (x++[a]) a from ⟨_,rfl⟩), List.append_assoc, List.cons_append, List.nil_append]; rw [derivative_double, unpaid,zero_add]; by_cases hv: First y a; · obtain ⟨y,rfl⟩:= hv; rw [if_pos (show First (a::y) a from ⟨_,rfl⟩), unpaid]
   rw [if_neg hv,add_zero]
 rw [if_neg ht,add_zero]; by_cases hv:First y a
 · obtain ⟨y,rfl⟩:=hv; rw [if_pos (show First (a::y) a from ⟨_,rfl⟩),derivative_double, unpaid,zero_add]
 rw [if_neg hv,add_zero,paid false _ (by simp) (easy x y a p q ht hv)] -- tune defeq
lemma cloak (x:Road)(a:Tone)(p:Line x)(h:2 ≤ x.length):excerpt polar (x++[a])=polar (x++[a])+(if Last x a then 2*polar x else 0)+(if First x a then 2*polar x else 0):=by
 have he(t:Road)(b:Tone):polar (b :: t ++ [b])=0:=by
    change wage true (([b]++ t)++[b])=0 -- not defeq append?
    rw [trim ([b]++ t),List.cons_append,nil_append,show b::([b]++t)= []++b::b::t from rfl, unpaid]
 by_cases u:Last x a
 · obtain ⟨x,rfl⟩:=u; rw [if_pos (show Last (x++[a]) a from ⟨_,rfl⟩)] -- tune
   simp only [List.append_assoc, List.cons_append,List.nil_append, polar]; rw [derivative_double,unpaid,zero_add]; by_cases v:First (x++[a]) a; · rcases x with _|⟨c,x⟩; simp at h; rw [if_pos v]; have hg:c=a:= (first_c (x++[a]) c a).mp (show First (c::(x++[a])) a from v); rw [hg, show wage _ _=0 from he x a]
   rw [if_neg v,add_zero]
 rw [if_neg u,add_zero]; by_cases q:First x a
 · obtain ⟨x,rfl⟩:=q; unfold polar; rw [if_pos (show First (a::x) a from ⟨_,rfl⟩), d_trim,trim (a::x), show [a]++(a::x)=[]++(a::a::x) from rfl, derivative_double,unpaid,zero_add]; rfl
 rw [if_neg q,add_zero]; exact (paid true _ (by simp) (clockwise x a p u q)).symm

def pot (t:Bool)(x y:Road):ℕ:= ∑ a:Tone,wage t (x++a::y)
def carryC (x:Road)(w:ℕ):= if x=[] then 0 else 2*w
lemma cashU(f:List Tone→ℕ)(x y:Road): (∑ a:Tone, excerpt f (x++a::y)) = (excerpt (fun l=>∑ a:Tone, f (l++a::y)) x+excerpt (fun l=>∑ a:Tone, f (x++a::l)) y)+4 *f (x++y):=by simp_rw [d_app,d_cons,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,sum_d]; simp only [nsmul_eq_mul]; ring -- tune
lemma purse(x:Road)(w:ℕ) : (∑ a:Tone, if Last x a then 2*w else 0)=carryC x w:=by induction x using List.reverseRecOn with|nil=> simp [carryC]|append_singleton x c _=> simp [carryC]
lemma purs(x:Road)(w:ℕ) : (∑ a:Tone, if First x a then 2*w else 0)=carryC x w:=by cases x with|nil=> simp [carryC]|cons=> simp [carryC]
lemma payroll(x y:Road)(p:Line x)(q:Line y):excerpt (fun l=>pot false l y) x + excerpt (pot false x) y+ 4 * weight (x++y) = (pot false x y+carryC x (weight (x++y)))+carryC y (weight (x++y)):=by
 unfold pot; rw [←cashU weight x y]; simp_rw [show ∀ a:Tone,excerpt weight (x++a::y)= _ from fun a=>suit x y a p q,Finset.sum_add_distrib,purse,purs]
lemma enroll(x:Road)(p:Line x)(q:2≤ x.length):excerpt (fun l=>pot true l []) x=pot true x []:=by
 let u:=∑ a:Tone, excerpt polar (x++[a]); have hk:u=excerpt (fun l=>pot true l []) x+4*polar x:=by simpa only [d_nil,add_zero,append_nil,pot,u,polar] using cashU polar x []
 have he:u=pot true x []+4*polar x:=by unfold u pot; simp_rw [show ∀ a:Tone, excerpt polar (x++[a])= _ from fun a=>cloak x a p q,sum_add_distrib,purse,purs,carryC,if_neg (show x≠[] by intro u; simp [u] at q)]; unfold polar; ring
 omega
end YM.CF.BProof.Tetra
