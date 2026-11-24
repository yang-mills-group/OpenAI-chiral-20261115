import Mathlib
/-!
# The one-dimensional even-N chess argument

No power-of-two requirement on the circumference. Keep marks on P indivisible (later).
`pi` is orientation flip on a single tile. Same as the maximal-run argument in
VolumeD-sew, using the max of the normalized prices: at such a max we can follow any
branch, it is enough to follow paths growing one run. (Avoids probability at absorption.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter
variable {α:Type*}
abbrev maxL {n:ℕ} (h:List α →ℝ)(x:List α):Prop:=∀ y:List α,y.length=n→ h y≤h x
def flop (π:α→α)(x:List α) : List α:= (x.map π).reverse
theorem flop_app(π:α→α)(x y:List α): flop π (x++y)=flop π y++flop π x:=by simp [flop]
@[simp] theorem flop_cons (π:α→α)(x:α)(L:List α) : flop π (x::L)=flop π L++[π x]:=by simp [flop]
@[simp] theorem flop_one(π:α→α)(x:α): flop π [x]=[π x]:=rfl
@[simp] theorem flop_len (π:α→α)(x:List α) : (flop π x).length=x.length:=by simp [flop]
def beat (π:α→α)(h:α):ℕ→ List α
|0=> []
|n+1=>h::beat π (π h) n -- recursive on n explicit use argument issue h fixed?
@[simp] lemma bzero(π:α→α)(h:α):beat π h 0=[]:=rfl
@[simp] lemma bone(π:α→α)(h:α):beat π h 1=[h]:=rfl
@[simp] lemma blen(π:α→α)(h:α)(n:ℕ):(beat π h n).length=n:=by induction n generalizing h with| zero=> rfl| succ n t=>simp only [beat,List.length_cons,t]
lemma beat_split(π:α→α)(a:α)(n k:ℕ) : beat π a (n+k)= beat π a n ++ beat π (π^[n] a) k:=by
 induction n generalizing a with
 | zero=> simp [beat]
 | succ n h=> rw [Nat.succ_add,beat,beat]; simpa [Function.iterate_succ_apply] using congrArg (a::·) (h (π a))
lemma norep(π:α→α)(p:Involutive π)(x:α)(n:ℕ):beat π x (2*n)= (List.replicate n [x,π x]).flatten:=by
 induction n with
 | zero=> simp
 | succ n h=> rw [show 2*(n+1)=(2*n+1)+1 from by omega,beat,beat,p x,h]; simp [List.replicate_succ]
lemma flop_beat(π:α→α)(p:Involutive π)(x:α)(n:ℕ) : flop π (beat π x n)=beat π (π^[n] x) n:=by -- induct tricky
 have he (a:α)(k:ℕ): π^[2*k] a=a:=by induction k with|zero=>simp|succ k i=> rw [Nat.mul_succ,iterate_add_apply, iterate_succ_apply,iterate_one,p a,i]
 have hv(x:α)(n:ℕ) :flop π (beat π x (2*n))=beat π x (2*n):=by
    simp only [flop,norep π p,List.map_flatten,List.map_replicate,List.map_cons, p x,List.map_nil]
    -- reverse_flatten
    simp [List.reverse_flatten]
 cases n.even_or_odd with
 | inl H=> obtain ⟨v,g⟩:=H; rw [g,← two_mul,he,hv]
 | inr H=>
    obtain ⟨v,g⟩:=H; rw [g,iterate_add_apply, he,iterate_one]; nth_rw 1 [show beat π x _= x :: beat π (π x) (2*v) from rfl]; rw [flop_cons,hv,beat_split π (π x) (2*v) 1,he,bone]
lemma alternate (π:α→α)(p:Involutive π)(x:α)(n:ℕ) : flop π (beat π x n) ++ beat π x n = beat π (π^[n] x) (2*n):=by
 rw [two_mul, beat_split, flop_beat π p]; rw [← iterate_add_apply]; have hp: ∀ k:ℕ, π^[k+k] x=x:=by
    intro k; induction k with|zero=>rfl|succ k h=> rw [show k+1+(k+1)=k+k+1+1 from by omega,iterate_succ_apply',iterate_succ_apply',h,p x]
 rw [hp]
end YM.CF.BProof.Chess
