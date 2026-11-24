import YM.CF.DPress.Wagon.Turf
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
/-!
 A tile *description*, can hold any of a **class of operators**, not necessarily exact Chess images of the first tile's. This will prove the instance of eq:Chess-P being used (allowance U_P for *all* P-slot tests of our sup-cost), without needing any dissemination-consistency assumptions. One bit carried along to alternate Chess orientations. Product comparison keeps offsets already removed. -/
namespace Race
variable {T:Race n L}
def turned : ℕ→Bool→ Bool
 | 0,b=>b
 | n+1,b=>turned n (!b)
lemma turn_!(n:ℕ)(p:Bool):turned n (!p)= !turned n p:=by induction n generalizing p with|zero=>rfl|succ n h=> exact h _ -- name ! lemma
lemma turn₂(n:ℕ)(p:Bool):turned n (turned n p)=p:=by induction n generalizing p with|zero=>rfl|succ n h=> change turned n _=_; rw [turned,← turn_!,Bool.not_not,h] -- rw may unfold outer
lemma turn_v(x y:ℕ)(p:Bool):turned (x+y) p=turned x (turned y p):=by induction y generalizing p with|zero=>rfl|succ n h=> exact h (!p)
lemma turn_left(n:ℕ)(p:Bool):turned (n+1) p= !(turned n p):=turn_! n p
lemma turn0{n:ℕ}(g:Even n)(p:Bool):turned n p=p:= by obtain ⟨v,rfl⟩:=g; rw [turn_v,turn₂]
structure Style (T:Race n L) where
 w:ℕ
 p : 0 < w
 V:ℝ -- per tile sup
 part:ℤ→ Bool→ Bool→ Fixed.Test n → Prop -- start, bit orientation, stable label(2), mark
 seed (a b x):part a b x 1
 roof {a b c X} (h:part a b c X): IsMark (T.S_ a (a+w)) X V
 fold {a b c X} (h:part (a) b c X) (w':ℤ) : part (retro w' (a+w)) (!b) c (peer (T.wall w') X) -- remove dummy
 per (a b c X): part (a+(T.η :ℤ)) b c X ↔ part a b c X
lemma rem_T (a b:ℤ)(i:ℕ): retro a (b+i)+ (i:ℤ)= retro a b:=by unfold retro; omega
lemma Rem (a b c:ℤ){w:ℝ}{T:Race n L}{X:Fixed.Test n}(v:IsMark (T.S_ a b) X w):IsMark (T.S_ (retro c b) (retro c a)) (peer (T.wall c) X) w:=by rw [←T.port_v]; exact penny _ v
lemma peer_times(a b c d i:ℤ){T:Race n L}{A B:Fixed.Test n}{u v:ℝ}(p:IsMark (T.S_ a b) A u)(q:IsMark (T.S_ c d) B v) (z:b ≤ c)(w:d ≤ a+T.η): peer (T.wall i) (A* B)= peer (T.wall i) B*peer (T.wall i) A:=by rw [(p.commute q (T.own z w)).eq]; exact funext (fun _=> Fock.theta_mul ..)
variable {P:Style T}
abbrev blockP (P:Style T)(a:ℤ)(B: List Bool):ℤ:= a+(B.length*P.w:ℕ)
lemma tapL {P:Style T} (p q: List Bool)(x:ℤ): blockP P x (p++q)=blockP P (blockP P x p) q:=by unfold blockP; rw [List.length_append,add_mul,Nat.cast_add]; omega
@[simp] lemma block_nil (P:Style T)(x:ℤ): blockP P x []=x:=by simp [blockP]
lemma block_c (P:Style T)(x:ℤ)(v:Bool)(B:List Bool): blockP P x (v::B)=blockP P (x+P.w) B:=by unfold blockP; rw [List.length_cons,add_mul,one_mul,Nat.cast_add]; omega -- P.w Nat convert ∎
lemma upper(P:Style T)(x:ℤ)(B:List Bool):x ≤ blockP P x B:=by unfold blockP; omega
-- Store exact tests by array, but ordered output product. mirror statement uses locality to reverse.
inductive Credit (P: Style T):ℤ→ Bool→ List Bool → Fixed.Test n→Prop
| zero (a b): Credit P a b [] 1
| next {a b c X Y U}: P.part a b c X→Credit P (a+P.w) (!b) U Y→Credit P a b (c::U) (X*Y)
namespace Credit
variable {a b:ℤ}{c d i:Bool}{X Y U:Fixed.Test n}{s t:List Bool}
lemma nil_p{X:Fixed.Test n}: Credit P a c [] X ↔ X=1:=⟨fun g=>(by cases g; rfl),fun p=> p.symm ▸ zero a c⟩
lemma pick (p:Credit P a c (d::s) X):∃ F G,P.part a c d F∧ Credit P (a+P.w) (!c) s G∧ X=F*G:=by cases p with|next u v=> exact ⟨_,_,u,v,rfl⟩
lemma pin (p:P.part a c d X): Credit P a c [d] X:=(mul_one X) ▸ (Credit.next p (zero _ _)) -- tune orientation
lemma unitP(P: Style T)(a:ℤ)(b:Bool)(s:List Bool):Credit P a b s 1:=by induction s generalizing a b with|nil=> exact zero a b|cons c s ih=> simpa only [one_mul] using Credit.next (P.seed a b c) (ih _ _)
lemma tag (p:Credit P a c s X): IsMark (T.S_ a (blockP P a s)) X (P.V^s.length):=by
 induction p with
 | zero a b=> simpa only [block_nil,List.length_nil,pow_zero] using IsMark.one (_:Support (More n))
 | @next a b c x y t h e ih=> rw [block_c,List.length_cons,pow_succ']; exact ((P.roof h).weaken (T.lane le_rfl (upper ..)) le_rfl).mul (ih.weaken (T.lane (by omega) le_rfl) le_rfl)
lemma companion (u:Credit P a c s X)(v: Credit P (blockP P a s) (turned s.length c) t Y): Credit P a c (s++t) (X*Y):=by
 induction u with
 | zero i j=> rw [one_mul,List.nil_append]; exact Eq.mp (congrArg (fun x:ℤ=> Credit P x j _ _) (block_nil P i)) v
 | next p h ih=> rw [mul_assoc]; refine next p (ih ?_); rw [block_c] at v; exact v
lemma splitC (p:Credit P a c (s++t) X): ∃ A B,Credit P a c s A ∧ Credit P (blockP P a s) (turned s.length c) t B ∧ X=A*B:=by
 induction s generalizing a X c with
 | nil=> rw [block_nil]; exact ⟨1,X, zero _ _,p,(one_mul X).symm ⟩
 | cons i s ih=>
    rw [block_c,List.cons_append] at *; obtain ⟨A,Q,v,e,x⟩:=pick p; obtain ⟨U,V,K,k,l⟩:= ih e; exact ⟨_,V,next v K,k,by rw [x,l,mul_assoc]⟩
end Credit
end Race
end YM.CF.DPress.Wagon
