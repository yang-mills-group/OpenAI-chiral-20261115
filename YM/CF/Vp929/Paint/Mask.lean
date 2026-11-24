import YM.CF.Vp929.Paint.Trip
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape.Paint
open Finset Function
open scoped Classical
local notation "ℙ" => Fin 4
abbrev Mask (I:Type*):=I→(Fin 4)→ℤ
variable {I:Type*}
def poll(h:Mask I): List I→ Bill→ℤ
| [],f=> f []
| i::x,f=>∑ a:ℙ, h i a * poll h x (fun y=> f (a::y))
lemma poll_nil(h:Mask I)(f):poll h [] f=f []:=rfl
lemma poll_cons(h:Mask I)(i x f):poll h (i::x) f=∑ a:ℙ,h i a * poll h x (fun y=> f (a::y)):=rfl
lemma poll_congr(h:Mask I)(x)(f g:Bill)(u:∀ y:Word,y.length=x.length→f y=g y):poll h x f=poll h x g:=by
 induction x generalizing f g with
 | nil=> exact u [] rfl
 | cons i x ih=> rw [poll_cons,poll_cons]; refine sum_congr rfl fun j hj=>?_ ; rw [ih (fun y=> f (j::y)) (fun y=>g (j::y)) (fun u' H=>u (j::u') (by simp [H]))]
lemma poll_const(h:Mask I)(x)(c:ℤ)(f):poll h x (fun y=> c*f y)=c*poll h x f:=by
 induction x generalizing f with
 | nil=> rfl
 | cons i x ih=> rw [poll_cons,poll_cons,mul_sum]; refine sum_congr rfl fun j h=>?_ ; rw [ih (fun y=> f (j::y))]; ring
lemma poll_sum{J:Type*}[Fintype J](h:Mask I)(x)(f:J→Bill): poll h x (fun y=>∑j:J,f j y)=∑j:J,poll h x (f j):=by
 induction x generalizing f with
 | nil=> rfl
 | cons i x ih=> simp_rw [poll_cons]; rw [sum_comm]; apply sum_congr rfl; intro a u; rw [← mul_sum,← ih (fun j y=> f j (a::y))]
lemma poll_app(h:Mask I)(x y:List I)(f:Bill):poll h (x++y) f=poll h x (fun a=>poll h y fun b=> f (a++b)):=by
 induction x generalizing f with
 | nil=> simp [poll_nil]
 | cons i x ih=> simp_rw [List.cons_append,poll_cons]; refine sum_congr rfl fun a _=>?_ ; exact congrArg (h i a * ·) (ih (fun y=> f (a::y)))
lemma poll_fub(h:Mask I)(x y:List I)(f: Word→Bill): poll h x (fun a=>poll h y (f a))=poll h y (fun b=>poll h x (fun a=> f a b)):=by
 induction x generalizing f with
 | nil=> simp [poll_nil]
 | cons i x ih=> simp_rw [poll_cons]; rw [poll_sum h _ (fun j b=> h i j * _)]; refine sum_congr rfl fun a p=>?_ ; rw [poll_const h _ (h i a) (fun b=> _),ih (fun v b=>f (a::v) b)]
abbrev clear(h:Mask I)(i:I): Prop:=h i=1
lemma poll_agree(h t:Mask I)(x)(f:Bill)(v:∀ i∈x,h i=t i): poll h x f=poll t x f:=by
 induction x generalizing f with
 | nil=> simp [poll_nil]
 | cons i x ih=> rw [poll_cons,poll_cons,v i (by simp)]; exact sum_congr rfl fun a _=>congrArg (_ * ·) (ih _ (fun a p=>v a (List.mem_cons_of_mem i p)))
lemma poll_line(h:Mask I)(x y:List I)(i:I)(c:ℤ)(q: Splits x.length y.length c)(p:clear h i):poll h (x++i::y) (chain (x++i::y).length)= c * poll h x (chain x.length)*poll h y (chain y.length):=by
 let f:= chain (x.length+y.length+1); rw [List.length_append, List.length_cons, ← add_assoc]; rw [poll_app]; change poll h x (fun a=>poll h (i::y) fun b=> f (a++b))=_
 have Z(a:Word)(v:a.length=x.length): poll h (i::y) (fun b=> f (a++b))= c * poll h y (chain y.length)*chain x.length a:=by
    rw [poll_cons]; simp_rw [p,Pi.one_apply,one_mul]; rw [← poll_sum h _ (fun j b=> f (a++j::b)),poll_congr h _ _ _ (q a · v · : ∀ b:Word,b.length=y.length→ _),poll_const h _ (c*chain x.length a) (chain y.length)]
    ring
 rw [poll_congr h x _ _ Z,poll_const]; ring
lemma poll_shift(h:Mask I)(x y:List I)(k:ℕ)(e:x.length+y.length=k+2):poll h (x++y) (circle k)=poll h (y++x) (circle k):=by rw [poll_app,poll_app,poll_fub h x y (fun a b=> circle k (a++b))]; apply poll_congr; intro i u; apply poll_congr; intro j k; rw [circShift' j i _ (by omega)]
lemma poll_erase(h:Mask I)(x:List I)(i:I)(k:ℕ)(e:x.length=k+1)(v:clear h i):poll h (i::x) (circle k)=6*poll h x (chain (k+1)):=by
 rw [poll_cons]; simp_rw [v,Pi.one_apply,one_mul]; rw [← poll_sum h _ (fun a b=>circle k (a::b)), poll_congr h x (fun b=>∑a:ℙ,circle k (a::b)) _ (fun b p=> circ_pay _ b (p.trans e)),poll_const]
lemma poll_exist{X:List I} :0< poll (1:Mask I) X (chain X.length):=by
 induction X with
 | nil=> simp [poll_nil]
 | cons i x ih=> obtain ⟨c,h,g⟩:=Paint.charge 0 x.length; rw [show i::x=[]++i::x from rfl,poll_line _ [] x i c g rfl]; simpa [poll_nil] using mul_pos h ih
lemma poll_circ{X:List I}{k:ℕ}(v:X.length=k+2):0<poll (1:Mask I) X (circle k):=by cases X; simp at v; next i z=> rw [poll_erase _ z i k (by simpa using v) rfl]; exact mul_pos (by norm_num) (show 0< poll _ z _ from by rw [show k+1=z.length from (by simp at v; omega)]; exact poll_exist)
end YM.CF.VolumeCape.Paint
