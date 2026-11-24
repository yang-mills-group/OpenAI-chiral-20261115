import YM.CF.BProof.Chess.TwoStep
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter
open scoped Classical Topology
variable {α:Type*}
structure Price (n:ℕ)(π:α→α)(h:List α→ℝ):Prop where
 nonneg x : x.length=2*n→0 ≤ h x
 prep : 0 < n
 bend : Involutive π
 spin (x y : List α) (p:x.length+y.length=2*n) : h (x++y)=h (y++x)
 split (x y : List α) (e:x.length=n)(g:y.length=n) : h (x++y)^2 ≤ h (x++flop π x)*h (flop π y++y)
namespace Price
variable {n:ℕ}{π:α→α}{h:List α→ℝ}(T:Price n π h)
local notation "P" x:max=> maxL (n:=2*n) h x
include T
lemma roll(x y:List α)(p:x.length+y.length=2*n)(u:maxL (n:=2*n) h (x++y)) : maxL (n:=2*n) h (y++x):=fun a b=> (u _ b).trans_eq (T.spin x y p)
lemma derive(x y:List α)(e:x.length=n)(g:y.length=n)(u:maxL (n:=2*n) h (x++y)):maxL (n:=2*n) h (x++flop π x):=by
 have hh:= T.split x y e g; have hp:h (flop π y++y) ≤ h (x++y):= u _ (by rw [List.length_append,flop_len]; omega); have hu:=T.nonneg (x++flop π x) (by rw [List.length_append,flop_len]; omega); intro i y'; refine (u i y').trans ?_; rcases lt_or_ge 0 (h (x++y)) with t|t; swap; · linarith
 exact le_of_mul_le_mul_right (by rw [pow_two] at hh; exact hh.trans (mul_le_mul_of_nonneg_left hp hu)) t
-- from prefix length say k, up to n
lemma prefixGrow(x:α)(l:List α)(k:ℕ)(p:k≤n)(v:k+l.length=2*n)(g:maxL (n:=2*n) h (beat π x k++l)): ∃ x' t, 2*k+List.length t=2*n ∧ maxL (n:=2*n) h (beat π x' (2*k)++t) :=by
 let W:=beat π x k; let a:=l.take (n-k); let b:=l.drop (n-k); have he:k+a.length=n:=by unfold a; simp [List.length_take]; omega
 have hz:a++b=l:= List.take_append_drop ..; have hb:b.length=n:=by have t:=congrArg List.length hz; rw [List.length_append] at t; omega
 let A:=W++a; have hA:A.length=n:=by rw [show A=W++a from rfl,List.length_append]; exact (blen π x k).symm ▸ he
 have h':A++b=W++l:=by rw [show A=W++a from rfl,List.append_assoc,hz]
 have ht:=T.derive A b hA hb (h'.symm ▸ g : maxL (n:=2*n) h (A++b)); let H:= flop π; let B:=W++(a++H a); have hK:A++H A=B++ H W:=by simp [A,B,H,flop_app,List.append_assoc]
 have hl:= T.roll B (H W) (by rw [←List.length_append,← hK,List.length_append]; change _+(flop π A).length=_; rw [flop_len,hA]; omega) (hK ▸ ht)
 refine ⟨π^[k] x,a++H a,?_,?_⟩; · simp only [List.length_append,H,flop_len]; omega
 unfold B H W at hl; rw [← List.append_assoc (flop π (beat π x k)),alternate π T.bend] at hl
 exact hl
variable [Finite α]
lemma maximal (D:List α)(v:D.length=2*n) :∃ x:α,h D ≤ h (beat π x (2*n)):=by
 letI:= Fintype.ofFinite α
 let B:=List.Vector α (2*n); haveI: Nonempty (List.Vector α (2*n)):=⟨(⟨D,v⟩:B)⟩; let f(x:B):=h (x.val); obtain ⟨⟨l,hl⟩,-,g⟩:= Finset.exists_max_image Finset.univ f Finset.univ_nonempty; have hp:P l:=fun i v=>g ⟨i,v⟩ (Finset.mem_univ _); have hx:= T.prep
 have he(k:ℕ)(e:0<k)(u:k≤n) :∃ x:α,∃ l:List α,k+l.length=2*n ∧ maxL (n:=2*n) h (beat π x k++l):=by
    induction k,e using Nat.le_induction with
    | base=> rcases l with (_|⟨x,l⟩); simp only [List.length_nil] at hl; omega; refine ⟨x,l,?_,?_⟩; rw [List.length_cons] at hl; omega; exact hp
    | succ k p ih=>
      obtain ⟨x,d,z,f⟩:= ih (by omega); obtain ⟨x',t,g,p'⟩:=T.prefixGrow x d k (by omega) z f; let a:=2*k-(k+1); have h:k+1+a=2*k:=by unfold a; omega
      refine ⟨x',beat π (π^[k+1] x') a++t,?_,?_⟩; swap; rw [←h,beat_split] at p'; rw [List.append_assoc] at p'; exact p'
      rw [List.length_append,blen]; omega
 obtain ⟨x,t,g,p⟩:= he n hx le_rfl; obtain ⟨y,t',k,p'⟩:= T.prefixGrow x t n le_rfl g p; have hw:t'=[]:= List.length_eq_zero_iff.mp (by omega); rw [hw,List.append_nil] at p'; exact ⟨y,p' D v⟩
end Price
end YM.CF.BProof.Chess
