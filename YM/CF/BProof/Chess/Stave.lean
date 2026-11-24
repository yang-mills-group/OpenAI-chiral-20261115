import YM.CF.BProof.Chess.Fort
/-! Positive-weight (avoids any log at zero) version. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter
open scoped Classical Topology
variable {α:Type*} {n:ℕ}{π:α→α}{h:List α→ℝ}
namespace Price
abbrev rate (f:α→ℝ)(x:List α) := (x.map f).prod
lemma append(f:α→ℝ)(x y:List α):rate f (x++y)=rate f x*rate f y:= by simp [rate]
variable (T:Price n π h) (f:α→ℝ)(u:∀ i,0<f i)(v:∀ i,f (π i)=f i)
include T
include v
private lemma joy_beat (x:α) (k:ℕ):rate f (beat π x k)=(f x)^k:=by
 induction k generalizing x with| zero=> simp [rate]| succ k g=> rw [beat,rate,List.map_cons,List.prod_cons]; change f x*(rate f (beat π (π x) k))=_; rw [g (π x),pow_succ',v]
private lemma joy_right(x:List α):rate f (flop π x)=rate f x:=by rw [flop,rate,List.map_reverse,List.prod_reverse,List.map_map,show f∘π=f from funext v]
omit v
include u
private lemma upbeat (x:List α):0<rate f x:=List.prod_pos (fun i y=> let ⟨a,p,t⟩:=List.mem_map.mp y; t ▸ u a)
include v u
lemma rent :Price n π (fun x=> h x/rate f x):=by
 refine ⟨fun i p=>div_nonneg (T.nonneg i p) (upbeat T f u i).le,T.prep,T.bend,fun x y p=>?_,fun x y p v'=>?_⟩
 · rw [append,append,T.spin x y p,mul_comm (rate f x)]
 have he:= T.split x y p v'; rw [div_pow,div_mul_div_comm,append,append,append,joy_right T f v,joy_right T f v,show (rate f x*rate f y)^2=(rate f x*rate f x)*(rate f y*rate f y) from by ring]; exact div_le_div_of_nonneg_right he (by have := upbeat T f u x; have := upbeat T f u y; positivity)
lemma victory [Finite α](p:∀ i,h (beat π i (2*n))≤ f i^(2*n))(x:List α)(t:x.length=2*n): h x≤rate f x:=by
 obtain ⟨i,g⟩:=(T.rent f u v).maximal x t; apply (div_le_one (upbeat T f u x)).mp; refine g.trans ((div_le_one (upbeat T f u _)).mpr ?_); rw [joy_beat T f v]; exact p i
end Price
end YM.CF.BProof.Chess
