import YM.CF.BProof.Tetrad.Fare
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List
open scoped BigOperators Classical
abbrev Script := List (Option Tone)
def fill (f:Road→ℕ) : Script→ℕ
 | []=> f []
 | (some i)::x=> fill (fun x=> f (i::x)) x
 | none::x=> ∑ a:Tone, fill (fun x=> f (a::x)) x
@[simp] lemma f_nil(f:Road→ℕ): fill f []=f []:=rfl
lemma f_c(f:Road→ℕ)(a:Tone)(x:Script): fill f (some a::x)=fill (fun x=>f (a::x)) x:=by rw [fill]
lemma f_s(f:Road→ℕ)(x:Script):fill f (none::x)=∑ a:Tone,fill (fun x=>f (a::x)) x:=by rw [fill]
lemma merge(f:Road→ℕ)(x y:Script):fill f (x++y)=fill (fun l=>fill (fun m=>f (l++m)) y) x:=by
 induction x generalizing f with
 | nil=> simp
 | cons i x ih=>
   rw [List.cons_append]; cases i; · rw [f_s,f_s]; apply sum_congr rfl; intro a _; rw [ih]; rfl
   rw [f_c,f_c,ih]; rfl
lemma f_con(f g:Road→ℕ)(x:Script)(h:∀ l:Road,l.length=x.length→f l=g l):fill f x=fill g x:=by
 induction x generalizing f g with
 | nil=> simp [h [] rfl]
 | cons i x ih=>
   have hx(i):fill (fun x=>f (i::x)) x=fill (fun x=>g (i::x)) x:= ih _ _ (fun l p=>h _ (by simp [p])); cases i; rw [f_s,f_s]; exact sum_congr rfl fun i _=>hx i
   rw [f_c,f_c,hx]
lemma f_sum{I:Type*}(f:I→Road→ℕ)(s:Finset I)(x:Script): fill (fun l=>∑ i∈s,f i l) x=∑ i∈s,fill (f i) x:=by
 induction x generalizing f with
 | nil=>simp
 | cons i x ih=>
    cases i; · rw [f_s]; simp_rw [f_s]; rw [sum_comm (f:=fun i a=> fill (fun l=> f i (a::l)) x)]; exact sum_congr rfl fun i _=> ih _
    rw [f_c]; simp_rw [f_c]; exact ih _
lemma f_mul(a:ℕ)(f:Road→ℕ)(x:Script): fill (fun l=> a*f l) x=a*fill f x:=by induction x generalizing f with|nil=> rfl|cons i x ih=> cases i; rw [f_s,f_s,mul_sum]; exact sum_congr rfl fun i _=> ih _; rw [f_c,f_c]; exact ih _
lemma f_comm(f:Road→Road→ℕ)(x y:Script): fill (fun a=>fill (f a) y) x=fill (fun a=>fill (fun b=> f b a) x) y:=by
 induction x generalizing f with
 | nil=>simp
 | cons i x ih=>
   cases i; · rw [f_s]; simp_rw [f_s]; rw [f_sum]; apply sum_congr rfl; intro i _; exact ih _
   rw [f_c]; simp_rw [f_c]; exact ih _
abbrev merit:=fill weight
abbrev massZ:=fill polar
lemma segment(x y:Script) : merit (x++none::y)= merit x*merit y*fare x.length y.length:=by
 unfold merit; rw [merge]; let a:=fare x.length y.length
 have hp(l:Road)(p:l.length=x.length): fill (fun v:Road=>weight (l++v)) (none::y)= weight l*a*fill weight y :=by
    rw [f_s] -- tune
    rw [←f_sum (fun i:Tone=> (fun u:Road=> weight (l++i::u))),←f_mul]; apply f_con; intro u hu; change pot false l u=_; rw [gap,p,hu]; unfold a; ring
 rw [show fill _ x = fill (fun l => a*merit y*weight l) x from (f_con _ _ _ (fun l e=> (hp l e).trans (by unfold merit; ring))),f_mul]; unfold merit a; ring
lemma revolve(x y:Script): massZ (x++y)=massZ (y++x):=by
 unfold massZ; rw [merge,merge,f_comm (fun v w=>polar (v++w)) x y]; apply f_con; intro l p; apply f_con; intro h q; exact trim ..
lemma deleteZ(x:Script)(p:x≠[]): massZ (x++[none])=6*merit x:=by
 unfold massZ merit; rw [merge,←f_mul]; apply f_con; intro l h; rw [f_s]; simp only [f_nil]; exact gate l (by intro v; subst l; apply p; have hx:=length_pos_of_ne_nil p; simp at h; omega)
lemma money {x:Script} (p:∀ i∈x,i=none):0 < merit x:=by
 induction x with
 | nil=> simp [merit,weight]
 | cons a x ih=> rw [p a (mem_cons_self ..), ← List.nil_append (none::x),segment]; simp [merit,weight]; -- mb remove simp
                  have h:=ih (fun i v=>p i (mem_cons_of_mem _ v)); unfold merit weight at h; positivity

abbrev Tale:=Option (Bool × Tone×Tone)
def fear(a b:Tale):Prop:= ∀ i:Bool×Tone×Tone,∀ j:Bool×Tone×Tone,a=some i→ b=some j→ i.1=j.1
def spot (i j:Bool) (a:Tale):Option Tone := a.map fun (b,y,z)=> if (if b then i else j) then y else z
def showQ(i j:Bool)(u:List Tale):Script:=u.map (spot i j)
def Bet(st:Script→ℕ)(x:List Tale):Prop:= st (showQ true true x)*st (showQ false false x)= st (showQ true false x)*st (showQ false true x)
lemma betUni(st:Script→ℕ)(a:Bool)(x:List Tale)(p:∀ i:Bool×Tone×Tone,some i ∈ x→ i.1=a): Bet st x:=by
 let f (i j:Bool)(z:Tale):= spot i j z; let X:=showQ
 have h(i j k l:Bool)(q:(if a then i else j)=(if a then k else l)): X i j x=X k l x:=by
    unfold X showQ; apply List.map_congr_left; intro e v; cases e <;> unfold spot <;> simp only [Option.map_none,Option.map_some]; rename_i z; simp only [p z v,q]
 unfold Bet; cases a
 · rw [show showQ false true x=showQ true true x from h _ _ _ _ rfl, show showQ true false x=showQ false false x from h _ _ _ _ rfl,mul_comm]
 rw [show showQ true false x=showQ true true x from h _ _ _ _ rfl,show showQ false true x=showQ false false x from h _ _ _ _ rfl]
lemma uniform (i:Bool×Tone×Tone)(x:List Tale)(p:IsChain fear (some i::x))(h:none ∉ x) : ∀ y:Bool×Tone×Tone,some y ∈ some i :: x → y.1=i.1 :=by
 induction x generalizing i with
 | nil=> simp
 | cons a x ih=> cases a; simp at h
                 rename_i a; intro y v; have e:=p.rel i a rfl rfl; rcases List.mem_cons.1 v with v|v; simp at v; rw [v]
                 rw [e]; exact ih a p.tail (fun t=> h (mem_cons_of_mem _ t)) y v -- tune
lemma alone(st:Script→ℕ)(x:List Tale)(p:IsChain fear x)(q:none ∉ x) : Bet st x:=by cases x with | nil=> rfl|cons a x=> cases a; simp at q; rename_i a; exact betUni st _ _ (uniform a x p (fun h=> q (mem_cons_of_mem _ h)))
lemma mul_carry{a b u v w z p q:ℕ}(h:a*b=u*v)(g:w*z=p*q)(t:ℕ): a*w*t*(b*z*t)=u*p*t*(v*q*t):=by calc
 _ = (a*b)*(w*z)*(t*t):=by ring
 _ = _:=by rw [h,g]; ring
lemma bet (x:List Tale) (p:IsChain fear x): Bet merit x:=by
 generalize h:x.length=z; induction z using Nat.strong_induction_on generalizing x with| h z ih=>
   by_cases q:none ∈x; swap; exact alone merit x p q
   obtain ⟨x,y,rfl⟩:=List.mem_iff_append.mp q; have g(i j:Bool): merit (showQ i j (x++none::y))= merit (showQ i j x)*merit (showQ i j y)*fare x.length y.length:=by simp [showQ,spot,segment]; -- tune
   have he:Bet merit x:= ih x.length (by rw [←h]; simp) x p.left_of_append rfl; have hg:Bet merit y := ih y.length (by rw [←h]; simp; omega) y (p.right_of_append.tail) rfl; unfold Bet at *; simp_rw [g]; generalize fare x.length y.length=t
   exact mul_carry he hg t -- define earlier
lemma quartZ (x:List Tale)(h:2 ≤ x.length)(p:Cycle.Chain fear x) : Bet massZ x:=by
 by_cases q:none∈ x; swap; · apply alone _ _ _ q; cases x with|nil=>simp|cons a l=> exact IsChain.left_of_append (l₂:=[a]) ((Cycle.chain_coe_cons ..).mp p)
 obtain ⟨x,y,rfl⟩:= List.mem_iff_append.mp q; let Y:= y++x; have ht:Cycle.Chain fear (none::Y):=by
    change Cycle.Chain fear (none::y++x:List Tale); suffices (↑(none::y++x:List Tale):Cycle Tale)=↑(x++none::y) by rw [this]; exact p
    exact (show (↑(x++none::y):Cycle Tale)=_ from Quotient.sound isRotated_append).symm
 have hk:IsChain fear Y:= ((Cycle.chain_coe_cons ..).mp ht).tail.left_of_append
 have he(i j:Bool):massZ (showQ i j (x++none::y))=6*merit (showQ i j Y):=by
    unfold Y showQ; simp only [List.map_append,List.map_cons,spot,Option.map_none]; rw [revolve (List.map _ x), List.cons_append]; apply Eq.trans (revolve [none] _); apply deleteZ; intro u; simp_all
 unfold Bet; simp_rw [he]; rw [mul_mul_mul_comm 6,mul_mul_mul_comm 6 (merit (showQ true false Y)), show merit _ * _= _ from bet Y hk] -- tune
end YM.CF.BProof.Tetra
