import YM.SU5.Reconstruction.Marque.Commuter
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Passage
open Function Set Filter Metric
open scoped Topology Classical
variable {H:Type*} [MetricSpace H] (P:Passage H)
local notation "W"=> Wander H
-- paddles proof param.Better use nondependent J for simplicity.Require effects on lifts target positive motion. Matrix positions & −time not needed now.
structure Paddles (J:Two→W) : Prop extends Centre P,Upright P where
 agrees (s t:Two)(p: Blank s)(q:t∈Wrap s):J s=J t
 power (s:Two)(p:Blank s):J s*J s=1
 lift (s t:Two)(p:Blank s)(q:Blank t): J s * J t∈P.ok (s*t)
 mirrors (g s:Two)(u:W)(p:u∈P.ok g)(h:Blank s): J (rehome g s)= rehome u (J s)
local notation "κ"=> P.ok
variable {J:Two→ Wander H}{P} (p:P.Paddles J)
namespace Paddles
variable (q s t:Two)(e: Reverse q s)(f: Reverse q t)
abbrev snap (J:Two→ Wander H) (q s:Two):=J s * J (s⁻¹*q)
include p e
lemma repeatSnap(t:Two)
   (v: t∈Wrap s): snap J q s=snap J q t:=by
 unfold snap; rw [p.agrees _ _ e.1 v, p.agrees _ _ (pairUp _ _ e)];
 rcases wrap_case _ v with v|v; exact Or.inl (by rw [v]); right
 rw [v,mul_inv_rev,bezel_inv, Set.mem_singleton_iff,← bezel_stays s⁻¹]; group
lemma snapMoved (g:Two)(u:W)(h:u∈P.ok g): snap J (rehome g q) (rehome g s)=rehome u (snap J q s):=by
 unfold snap; rw [rehome_mul u,p.mirrors g s u h e.1,show (rehome g s)⁻¹*rehome g q=rehome g (s⁻¹*q) from (by unfold rehome;group),p.mirrors _ _ u h (pairUp _ _ e)]
lemma accepts : snap J q s ∈P.ok q:= by simpa only [mul_inv_cancel_left] using p.lift s (s⁻¹*q) e.1 (pairUp _ _ e)
lemma atCentre (h:q∈Wrap 1): snap J q s=1:= by
   unfold snap; have ht:(s⁻¹*q)∈Wrap s:=by
      rcases wrap_case _ h with h|h; rw [h,mul_one]; exact Or.inr (revers _ e.1)
      rw [h,mul_one,revers s e.1,mul_assoc,← bezel_stays s,← mul_assoc,bezel_sq,one_mul]; exact Or.inl rfl -- check associativity
   rw[←p.agrees _ _ e.1 ht, p.power _ e.1]
include f
lemma invertSlate (h:(∃ k,q=Pole k)∨ (∃ k,q∈Wrap (Head k))):snap J q s=snap J q t:=by
 rcases h with ⟨k,h⟩|⟨k,h⟩
 · subst q; by_cases d:(k:ℂ)=(k:ℂ)⁻¹
   · rw [atCentre p _ s e (poleDead k d),atCentre p _ t f (poleDead k d)]
   obtain ⟨w,hw⟩:= sub_pole s t k d e f; obtain ⟨u,hu⟩:= p.toUpright.always (Pole w); let R:=snap J (Pole k) s
   have he:rehome (Pole w) (Pole k)=Pole k:= by unfold rehome; rw [(Pole_comm ..).eq];group
   rw [← hw,show snap J (Pole k) (rehome (Pole w) s)= rehome u (snap J (Pole k) s) from (by simpa only [he] using snapMoved p (Pole k) s e (Pole w) u hu),rehome,(costume p.toCentre p.toUpright w k _ _ hu (accepts p (Pole k) s e)).eq]; group  -- tune
 by_cases d:k=0
 · rw [d,Head_one] at h; rw [atCentre p q s e h,atCentre p q t f h]
 obtain ⟨w,hw⟩:=sub_tuber _ _ e f h d; obtain ⟨u,z⟩:= p.toUpright.always (Head w)
 have he: rehome (Head w) q=q:= by
    rcases wrap_case _ h with h|h <;> rw [h]
    · unfold rehome; rw[(Head_comm ..).eq]; group
    rw[rehome_mul,rehome_bezel,rehome,(Head_comm ..).eq]; group
 have hp: Reverse q (rehome (Head w) s):= he ▸ shifted q s (Head w) e -- tune
 have hk:u*snap J q s=snap J q s*u:= (chit_form p.toCentre p.toUpright w k z (reverseLock p.toCentre (accepts p q s e) (show Head k∈Wrap q by rcases wrap_case _ h with h|h; exact Or.inl h.symm; rw[h,wrap_bezel]; exact Or.inl rfl))).eq
 have hy:= snapMoved p _ s e _ u z; rw[he] at hy; rw [←repeatSnap p q _ hp t hw, hy,rehome,hk]; group
lemma snapYes:snap J q s=snap J q t:=by
 obtain ⟨w,h⟩:=canonical q; obtain ⟨u,hu⟩:=p.toUpright.always w; have hk:=invertSlate p _ _ _ (shifted q s w e) (shifted q t w f) h -- tune
 rw [snapMoved p q s e w u hu,snapMoved p q t f w u hu] at hk
 exact (rehome_back ..).symm.trans ((congrArg (rehome u⁻¹) hk).trans (rehome_back ..))
omit e f p
variable (J)
noncomputable def Victory:= snap J q (findReverse q).choose
local notation "U"=> Victory (H:=H)
variable {J}
include p
lemma answer (q:Two):U J q∈P.ok q:= accepts p q _ (findReverse q).choose_spec
lemma swipe (i:Two)(a:Blank t)(b:Blank i) : U J (t*i)= J t*J i:=by rw[Victory, snapYes p _ _ t (findReverse _).choose_spec (reverseOf ..),snap]; simp; all_goals assumption -- tune
lemma first:U J 1=1:= atCentre p 1 _ (findReverse _).choose_spec (Or.inl rfl)
lemma double:U J bezel=1:=atCentre p bezel _ (findReverse _).choose_spec (Or.inr (mul_one _).symm)
lemma rotate (g:Two)(u:W)(h:u∈P.ok g) : U J (rehome g q)= rehome u (U J q):= by
 let z:=(findReverse q).choose_spec; unfold Victory; rw[snapYes p _ _ (rehome g (findReverse q).choose) (findReverse _).choose_spec (shifted q (findReverse q).choose _ z), snapMoved p q _ z _ u h]
include e in
lemma toll (i:Two)(p':Reverse i s):U J (q*i)=U J q*U J i:=by
 let a:= q*s⁻¹; let b:=s⁻¹*i; have hp:Blank a:= by unfold a Blank; rw [revers _ e.1,←mul_assoc,← bezel_stays q,mul_assoc,lip_bezel,e.2,neg_zero]
 have e₁:a*s=q:= by unfold a;group
 have e₂:s*b=i:=by unfold b;group
 have e₃:=pairUp _ _ p'
 rw[← e₁,←e₂, show a*s*(s*b)=(bezel*a)*b from (by rw [mul_assoc,← mul_assoc s,reverse2 s e.1,←mul_assoc,← bezel_stays a]),swipe p (bezel*a) b (lipSign a hp (Or.inr rfl)) e₃,←p.agrees _ _ hp (show bezel*a∈Wrap a from Or.inr rfl),swipe p _ _ hp e.1,swipe p _ _ e.1 e₃]
 rw [mul_assoc,← mul_assoc (J s), p.power s e.1,one_mul]
end Paddles
end YM.Marque.Passage
