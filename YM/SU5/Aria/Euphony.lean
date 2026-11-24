import YM.SU5.Aria.Screens
/-! # Euclidean spread-collars adjoint, including all gaps -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric ContinuousLinearMap
open scoped Topology InnerProductSpace NNReal
variable {H:Hilbert}{i:Axis}(S:OS.Semigroup H i){J : Type*} (u v:J→ℝ)
-- `squeeze` on both ends with heat; compatible even empty
local notation "E"=> S.E
local notation "τ" p:max=> Real.toNNReal p
def Chat (l:List J) (b c:ℝ):Prop:=match l with
| []=> b≤c
| j::l=> b ≤ u j ∧ Chat l (v j) c
variable (X:J→ H.Op)
noncomputable def pinch (l:List J) (b c:ℝ): H.Op:=match l with
 | []=> E (τ (c-b))
 | j::l=> (E (τ (u j-b))).comp ((X j).comp (pinch l (v j) c))
lemma pays {x:H}(f:∀ t,S.E t x=x)(l:List J)(b c:ℝ): pinch S u v X l b c x=rector S X u v l b x:=by induction l generalizing b with
 | nil=> exact f _
 | cons i l t=>exact congrArg (fun y:H=> E (τ (u i-b)) (X i y)) (t _)
lemma paid (x:H)(f:∀ t,S.E t x=x)(l:List J)(b c:ℝ): inner ℂ x (pinch S u v X l b c x)= receive S x X u v l:=by rw [pays S u v X f, rector_view S x X u v f]
lemma chat_start {b b' c:ℝ}(h:b ≤ b')(l: List J) (f:Chat u v l b' c):
    Chat u v l b c∧ (E (τ (b'-b))).comp (pinch S u v X l b' c)=pinch S u v X l b c:=by cases l with
 | nil=> exact ⟨h.trans f,(terraces S _ _ (sub_nonneg.mpr h) (sub_nonneg.mpr f)).trans (congrArg _ (congrArg Real.toNNReal (show (b'-b)+(c-b')=c-b by abel)))⟩ -- congrArg type infer
 | cons i l=>
   obtain ⟨p,f⟩:=f; refine ⟨And.intro (h.trans p) f,?_⟩; rw [pinch,pinch, ←Germ.Alliance.just (H:=H), terraces S _ _ (sub_nonneg.mpr h) (sub_nonneg.mpr p), show b'-b+(u i-b')=u i-b from by abel]
lemma pin_board {b c d:ℝ}(l k:List J)(g:Chat u v l b c)(f:Chat u v k c d): Chat u v (l++k) b d∧ pinch S u v X (l++k) b d=(pinch S u v X l b c).comp (pinch S u v X k c d):=by
 induction l generalizing b with
 | nil=>
    have ht:=chat_start S u v X (b:=b) g k f; exact ⟨ht.1,ht.2.symm⟩ -- l++k
 | cons i t ih=>
    obtain ⟨p,h⟩:=g; obtain ⟨y,z⟩:=ih h
    refine ⟨And.intro p y,?_⟩; rw [List.cons_append,pinch,pinch,z]; rfl
lemma card_flip (s:List J)(b c:ℝ)(t:Chat u v s b c): Chat (-v) (-u) s.reverse (-c) (-b) ∧
    pinch S (-v) (-u) (fun i=>star (X i)) s.reverse (-c) (-b)=star (pinch S u v X s b c):=by
 induction s generalizing b with
 | nil=> refine ⟨neg_le_neg t,?_⟩; change E (τ (-b - -c))=_; rw [pinch, (show star (E _) = E (τ (c-b)) from S.sym _)]; congr 2; abel -- tune
 | cons i s ih=>
    obtain ⟨h,t⟩:=t; obtain ⟨p,k⟩:=ih (v i) t
    let U:=-v; let V:=-u; let y(j:J):=star (X j); have ht:Chat U V [i] (-v i) (-b):=And.intro (le_refl _) (neg_le_neg h)
    let a:=τ (u i-b); have he:pinch S U V y [i] (-v i) (-b)=(star (X i)).comp (E a):=by unfold pinch; rw [show U i=-(v i) from rfl,pinch,show -b-V i=u i-b from (by unfold V; simp; abel),sub_self,Real.toNNReal_zero,S.eZero]; rfl
    obtain ⟨q,p'⟩:=pin_board S U V y _ _ p ht
    rw [List.reverse_cons]; refine ⟨q,?_⟩; let B:=pinch S u v X s (v i) c
    have g : E a* (X i* B) = pinch S u v X (i::s) b c:=rfl
    rw [←g]; change pinch S U V y _ _ _= star (E a * (X i * B)); rw [p',he,k,star_mul,star_mul,show star (E a)= E a from S.sym a]; rfl
lemma slim_pinch (L:List J)(b:ℝ): Sheet u v L b→ ∃ c:ℝ, Chat u v L b c:=by induction L generalizing b with
 | nil=> exact fun _=>⟨b,le_rfl⟩
 | cons i l ih=> rintro ⟨t,p⟩; obtain ⟨c,h⟩:= ih _ p; exact ⟨c, And.intro t.le h⟩
end YM.CF.Buffered.Afterglow.Tower.Aria
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.card_flip
