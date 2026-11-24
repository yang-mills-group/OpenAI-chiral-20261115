import Mathlib
/-!
 # Finite cycles, deletion-rate sampling of Lemma fd
 Part I -- derivation d. Open or clockwise in four Colours.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Tetra
open Function Finset List
open scoped BigOperators Classical
variable {E:Type*}{C:Type*}
section algebra
variable [AddCommMonoid E]
def excerpt(f:List C→ E) : List C → E
 | []=>0
 | a::l=>f l+ excerpt (fun l=>f (a::l)) l
@[simp] lemma d_nil(f:List C→E): excerpt f []=0:=rfl
lemma d_cons(f:List C→E)(a:C)(x):excerpt f (a::x)=f x+excerpt (fun l=>f (a::l)) x:=rfl -- rec? tune
lemma d_con (f g:List C→E)(x:List C)(p:∀ l:List C,l.length+1=x.length→f l=g l):excerpt f x=excerpt g x:=by
 induction x generalizing f g with
 | nil=> rw [d_nil,d_nil]
 | cons a x ih=> rw [d_cons,d_cons,p x rfl,ih _ _ (fun l h=> p (a::l) (by simp [h]))] -- tune ih explicit
lemma d_zero{f:List C→E}(x:List C)(p:∀ l:List C,l.length+1=x.length→f l=0):excerpt f x=0:=by
 induction x generalizing f with | nil=> rfl| cons a x ih=>rw [d_cons,p x rfl, ih (f:=fun l=>f (a::l)) (fun l h=> p (a::l) (by simp [h])),add_zero]
lemma d_app(f:List C→E)(x y:List C): excerpt f (x++y)= excerpt (fun l=>f (l++y)) x+excerpt (fun l=>f (x++l)) y:=by induction x generalizing f with|nil=>simp|cons a x ih=>simp only [cons_append,d_cons,ih,add_assoc]
lemma sum_d {I:Type*}(f:I→List C→E)(x:List C)(s:Finset I):∑ i∈s,excerpt (f i) x=excerpt (fun l=> ∑ i∈s, f i l) x:=by induction x generalizing f with|nil=>simp|cons a x ih=> simp only [d_cons,sum_add_distrib]; rw [ih (fun i l=> f i (a::l))]
end algebra
lemma d_mul(f:List C→ ℕ)(x:List C)(a:ℕ):excerpt (fun l=> f l * a) x= excerpt f x * a:=by induction x generalizing f with|nil=>simp|cons b x ih=> simp only [d_cons,add_mul]; rw [ih (fun l=>f (b::l))]

abbrev Tone:= Fin 4
abbrev Road:= List Tone
abbrev Line(x:Road):= List.IsChain (· ≠ ·) x
def smooth (t:Bool)(x:Road):Prop:= if t then x.length <2 ∨ Cycle.Chain (· ≠ ·) (x:Cycle Tone) else Line x
lemma smooth_p (t:Bool)(x:Road)(h:smooth t x):Line x:=by
 unfold smooth at h; split at h; swap; exact h
 rcases x with _|⟨a, l⟩; simp [Line]
 rcases h with h|h
 · rcases l with _|⟨c,l⟩ <;> simp_all [Line] -- impossible
 have hp:Line ((a::l)++[a]):= Cycle.chain_coe_cons .. |>.mp h; exact hp.left_of_append
lemma smooth_app(x y:Road): smooth true (x++y)↔ smooth true (y++x):=by
 have h:(((x++y):List Tone):Cycle Tone)= (((y++x):List Tone):Cycle Tone):= by apply Quotient.sound; exact isRotated_append -- tune
 simp only [smooth,List.length_append,add_comm x.length y.length, h,if_true]
lemma stiff(t:Bool)(x y:Road)(a:Tone): ¬ smooth t (x++a::a::y):=fun h=> (isChain_append_cons_cons.mp (smooth_p _ _ h)).2.1 rfl

private def stack (t:Bool):ℕ→Road→ℕ
 | 0,_=>1
 | k+1,x=> if x=[] then 1 else if smooth t x then excerpt (stack t k) x else 0

def wage (t:Bool)(x:Road):ℕ:=stack t x.length x
@[simp] lemma w_nil(t:Bool):wage t []=1:=by rw [wage]; rfl
lemma rule (t:Bool)(x:Road)(h:x≠[]) : wage t x= if smooth t x then excerpt (wage t) x else 0:=by
 rw [wage]; rcases x with _|⟨a,l⟩; contradiction
 rw [length_cons,stack,if_neg h]; split; next h=> exact d_con _ _ _ (fun l' p=> by change _= stack _ l'.length _; rw [show l'.length=l.length from by simp only [length_cons] at p; omega])
 rfl
lemma paid (t:Bool)(x:Road)(h:x≠[])(p:smooth t x): wage t x=excerpt (wage t) x:=by rw [rule _ _ h,if_pos p]
lemma clash (t:Bool)(x:Road)(p:¬ smooth t x):wage t x=0:=by rcases eq_or_ne x [] with r|r; subst x; cases t <;> simp_all [smooth,Line]; rw [rule _ _ r,if_neg p]
lemma trim (x y:Road): wage true (x++y)=wage true (y++x):=by
 suffices h:∀ n:ℕ,stack true n (x++y)=stack true n (y++x) by rw [wage,wage,List.length_append,List.length_append, add_comm x.length,h] -- tune rw
 intro n; induction n generalizing x y with
 | zero=>rfl
 | succ n ih=>
   rw [stack, stack, smooth_app]; rcases x with _|⟨a,x⟩; simp
   by_cases hu: smooth true (y ++ (a::x)) <;> simp only [hu,reduceIte]; · simp only [List.append_eq_nil_iff,cons_ne_nil,false_and,and_false,ite_false]; rw [d_app,d_app]; rw [d_con (fun l=>stack true n (l++y)) (fun l=>stack true n (y++l)) (a::x) (fun l _=>ih ..), d_con (fun l=>stack true n ((a::x)++l)) (fun l=>stack true n (l++(a::x))) y (fun l _=>ih ..)]; exact add_comm ..
   simp
@[simp] lemma singleW(a:Tone)(t:Bool):wage t [a]=1:= by rw [paid _ _ (by simp) (by cases t <;> simp [smooth,Line]),d_cons,d_nil,w_nil,add_zero]
-- Conflict identity. Works even when more conflicts occur.
lemma unpaid (t:Bool)(x y:Road)(a:Tone):wage t (x++a::a::y)=0:= clash t _ (stiff t x y a)
lemma derivative_double (t:Bool)(x y:Road)(a:Tone): excerpt (wage t) (x++a::a::y)=2*wage t (x++a::y):=by
 rw [d_app, d_zero x (fun l _=>unpaid ..)]; simp only [d_cons]; rw [d_zero y (fun l _=>unpaid ..),add_zero,zero_add,two_mul]
lemma d_trim(x y:Road):excerpt (wage true) (x++y)= excerpt (wage true) (y++x):=by
 rw [d_app,d_app]; rw [d_con (fun l=>wage true (l++y)) (fun l=>wage true (y++l)) x (fun l _=>trim ..),d_con (fun l=> wage true (x++l)) (fun l=>wage true (l++x)) y (fun l _=>trim ..)]; exact add_comm ..
end YM.CF.BProof.Tetra
