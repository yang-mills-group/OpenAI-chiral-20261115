import YM.SU5.Reconstruction.Marque.Taffeta
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Passage.Paddles
open Function Set Filter Metric
open scoped Topology Classical
variable {H:Type*} [MetricSpace H] {P:Passage H}
local notation "W"=> Wander H
variable {J:Two→Wander H} (p:P.Paddles J)
variable (q s:Two)(t:ℂ)
local notation "U" => Victory J
include p
lemma pour (t:Two)(e:U (rehome t q*rehome t s)=U (rehome t q)*U (rehome t s)): U (q*s)=U q*U s:= by
 obtain ⟨u,h⟩:=p.toUpright.always t; rw[← rehome_mul,rotate p _ _ u h,rotate p _ _ u h,rotate p _ _ u h,← rehome_mul] at e
 exact (rehome_back ..).symm.trans ((congrArg (rehome u⁻¹) e).trans (rehome_back ..))
private lemma shelf (e:B q≠0) : U (Tail t*q)=U (Tail t)*U q:= by
   let z:= rehome turn⁻¹ q; have hd: C z≠0:=by unfold z; simpa [rehome,turn] using e
   obtain ⟨s,p1,p2⟩:= goodHead z (-t) (Or.inl hd)
   refine p.pour _ _ turn⁻¹ ?_; rw [show rehome turn⁻¹ (Tail t) = Head (-t) from (by rw [← rehome_back turn (Head (-t)),dart]; rw [neg_neg])]; exact toll p _ s p2 z p1 -- tune involving rw target
lemma headHonors: U (q*Head t)=U q*U (Head t):= by
   have h(q:Two)(e:C q≠0∨A q=D q): U (q* Head t)=U q*U (Head t):= by obtain ⟨s,v,p1⟩:=goodHead q t e; exact toll p q s v _ p1
   by_cases e:C q≠0∨A q=D q; exact h q e
   push Not at e
   obtain ⟨w,hw,hc,v,z⟩:= chooseHead q t e.1 e.2
   apply p.pour q (Head t) w
   rw[hw]; apply mul_left_cancel (a:=U (Tail 1)); rw [← shelf p _ _ z,← mul_assoc (Tail 1),← mul_assoc (U (Tail 1)),← shelf p _ _ v,h _ (Or.inl (multiply_help _ hc))] -- tune
lemma tailHonors: U (q*Tail t)=U q*U (Tail t):= by
   apply p.pour _ _ turn⁻¹; rw [show rehome turn⁻¹ (Tail t) = Head (-t) from (by rw [← rehome_back turn (Head (-t)),dart]; rw [neg_neg])]; exact p.headHonors ..
lemma allHonors: U (q*s)=U q*U s:=by
 obtain ⟨v,h⟩:= padded s; let X:=s*Head v; have e:s= Tail ((D X-1)/B X)* Head (B X)*Tail ((A X-1)/B X)*Head (-v):= by rw[← pad]; unfold X; rw[mul_assoc,Head_add]; simp; exact h
 -- rw at s only ok X let
 rw[e]; simp only [← mul_assoc, headHonors p,tailHonors p] -- tune assoc simpl
noncomputable def Pennant : Two →* W:= { toFun := Victory J, map_one':=first p,map_mul':=allHonors p }
private def Vr := Pennant p
noncomputable def Altar : Passage H where
  ok g:={Vr p g}
  pass:=(map_one (Vr p)).symm
  plus {x y u v} i j:= by change u*v=Vr p _; rw [show u=Vr p x from i, show v=Vr p y from j,map_mul]
  opp {x u} h:=by change u⁻¹=Vr p _; rw [show u=Vr p x from h,map_inv]
lemma arches (Z:Continues fun v:ℝ=> Vr p (Tuning v))(X:Continues fun v:ℝ=> Vr p (Zip v))(Y:Continues fun v:ℝ=> Vr p (Yell v)):Continues (Pennant p):=by
   let U':=Altar p; have e {g:Two}{u:W}:u∈U'.ok g↔u=Pennant p g:=Iff.rfl
   have h: Upright U':= ⟨⟨_,Z,fun _=> rfl⟩, ⟨_,X,fun _=> rfl⟩, ⟨_,Y,fun _=> rfl⟩⟩ -- rfl membership fails
   apply nowC.mpr; intro q; obtain ⟨u,v,z,h,v'⟩:= h.cross _ (show Tendsto id (𝓝 q) (𝓝 q) from tendsto_id); replace v:= e.mp h
   rw [← v]; -- within maybe occurrence
   exact fun a=> (z a).congr' (v'.mono fun i p => by change u i a=_; rw [e.mp p]; rfl)
end YM.Marque.Passage.Paddles
