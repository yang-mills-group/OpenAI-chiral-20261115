import YM.SU5.Thin.Cascade.Sea
set_option autoImplicit false
set_option maxHeartbeats 680000
noncomputable section
namespace YM.CF.Rapids
open Function Filter NormedSpace Fock Thera Finset
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Classical ContDiff
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
variable {P Q K:Op I}(p:Clad P Q 1 1 K)
include p
lemma dual : Clad Q P 1 1 (star K):=by
 refine ⟨p.helm,p.proj,(by simp),?_,?_,?_,?_⟩
 · have he:= congrArg star p.right; simp only [star_mul,star_one,p.proj.isSelfAdjoint.star_eq,p.helm.isSelfAdjoint.star_eq,one_mul] at he; rw [mul_one]; exact he
 · have he:= congrArg star p.left; simp only [star_mul,star_one,p.proj.isSelfAdjoint.star_eq,p.helm.isSelfAdjoint.star_eq,one_mul] at he; rw [mul_one]; exact he
 · nth_rw 1 [←p.helm.2]; rw [←star_mul,p.stem]
 nth_rw 1 [←p.proj.2]; rw [←star_mul,p.tray]
lemma spine : laneP Q 1 K=K-Q:=by unfold laneP; rw [sub_mul,sub_mul,one_mul,one_mul,p.quotaW] -- blocked mul_one
open Gall Flare
variable {C D:ℝ}
include p
lemma liftCore [Nonempty I] (u:SnowCone (laneP Q 1 K) C) : SnowCone (laneP P 1 (star K)) (C+2) :=by
 have hx: SnowCone K (C+1):=by
    rw [spine p] at u; have hv:= u.add (SnowCone.pilot (IsStarProjection.norm_le _ p.helm)); rw [sub_add_cancel] at hv; exact hv
 rw [spine (dual p)]; rw [show C+2=C+1+1 by ring, sub_eq_add_neg]; exact hx.pose.add ((SnowCone.pilot (IsStarProjection.norm_le _ p.proj)).neg)
variable {F:Op I}
omit p
lemma star_word (i:Gall.WordX I): Gall.pack i=star (Gall.pack (!i.1,i.2)):=by rcases i with ⟨x,t⟩; cases x<;> simp [Gall.pack,artW,ton,creed,remove]
def badge (Q K:Op I)(t:Gall.WordX I):= star (iceT (laneP Q 1 K) (artW ((!t.1),t.2))) -- depends Q K? add args
include p
lemma present_b [Nonempty I] (g:SnowCone (laneP Q 1 K) C)(i:List (Gall.WordX I)): let l:=laneP Q 1 K; let L:=star (1+l); let G:=quant L; let S:=badge Q K; G*rollC Gall.pack i=rollC S i * G∧‖rollC S i‖≤ (C+1)^i.length:=by
 intro l L G S
 have hi(t:Gall.WordX I): G*Gall.pack t=S t *G:=by
    unfold G L S badge; rw [star_word t]; rw [quant_star,← star_mul, ← star_mul]; exact congrArg star (mixC p _)
 constructor
 ·
    induction i with
    | nil=>simp [rollC]
    | cons i j ih=>unfold rollC; rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,←rollC, ←rollC,←mul_assoc,hi,mul_assoc,ih,mul_assoc]
 ·
    induction i with
    | nil=>simp [rollC]
    | cons i j ih=>unfold rollC; rw [List.length_cons,List.map_cons,List.prod_cons,pow_succ', ← rollC]; have hi : ‖S i‖ ≤ C+1:= (norm_star _).trans_le (bill_p (n:=I) (fun i=> ⟨g.right i,g.left i⟩) _); exact (norm_mul_le ..).trans (mul_le_mul hi ih (norm_nonneg _) ((norm_nonneg _).trans hi))
omit p
set_option maxHeartbeats 400000 in
private lemma payFT [Nonempty I](G:FC I)(S:Gall.WordX I→ FC I)(i:List (Gall.WordX I))(x w s:Wave I)(a:ℂ)(q Z:ℝ)(v:‖s‖=1)(h:0≤q)(he:x=a • acts (star G) s)(hp:‖a‖=q)(hb:‖acts G w‖ ≤ Z)(hw':G*rollC Gall.pack i=rollC S i* G)(hx:‖rollC S i‖≤(C+1)^i.length):‖inner ℂ x (acts (rollC Gall.pack i) w)‖≤ (q*Z)*(C+1)^i.length:=by
 have hp:‖(starRingEnd ℂ) a‖=q:= by simpa only [show ‖(starRingEnd ℂ) a‖=‖a‖ from norm_star _] using hp
 rw [he]; rw [inner_smul_left,norm_mul,hp,act_inner, ←act_mul,hw',act_mul]; let u0:=rollC S i; change q*‖inner ℂ s _‖≤(q*Z)*_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ h; have ht:= (norm_inner_le_norm (𝕜:=ℂ) s (acts u0 (acts G w))); rw [v,one_mul] at ht; exact ht.trans ((show ‖acts u0 (acts G w)‖≤ ‖u0‖*‖acts G w‖ from (by nth_rw 1 [← Matrix.l2_opNorm_toEuclideanCLM u0]; exact (acts u0).le_opNorm _)).trans ((mul_le_mul hx hb (norm_nonneg (acts G w)) ((norm_nonneg _).trans hx)).trans_eq (mul_comm ..))) -- trouble L reinterpretation
include p

lemma payment [Nonempty I] (g:SnowCone (laneP Q 1 K) C) (w:Wave I)(u:Sea F w)(s:Wave I)(v:Sea Q s)(x:Wave I)(t:Sea P x)(hx:IsStarProjection F):
 Gall.Yep (C+1) x w (‖inner ℂ x s‖*Real.exp (((1+C)^2+1)* DriveL1 (F-Q)/2)):=by
 let l:=laneP Q 1 K; let L:=star (1+l); let G:=quant L; let a:= skyGlow s 1 x
 have he:x=a • acts (star G) s:=by
    have he:=broomstick p _ _ t v; rw [quant_one,act_one,tallied _ p.reef] at he; unfold G L; rw [←quant_star,star_star]; exact he
 have hz: L*Q=Q:=by
    unfold L; rw [star_add,star_one,add_mul,one_mul]; have hq: star l*Q=0:=by nth_rw 1 [←p.helm.2]; rw [←star_mul,p.bare,star_zero]
    rw [hq,add_zero]
 have hw: SnowCone L (1+C):=(SnowCone.solo.add g).pose
 let Z:=(((1+C)^2+1)*DriveL1 (F-Q)/2);
 have hb: ‖acts G w‖ ≤ Real.exp Z:= ship_le L F Q hx p.helm hz w u (((1+C)^2+1)*DriveL1 (F-Q)) (by exact (Complex.re_le_norm _).trans (flowEntry _ _ _ (fun i j=> hw.entry i j))) -- concludes exp /2 maybe simp
 intro i; let S(t: Gall.WordX I):= badge Q K t
 obtain ⟨e,hx'⟩:=present_b p g i; apply payFT G (badge Q K) i x w s a ‖inner ℂ x s‖ (Real.exp Z) v.2 (norm_nonneg _) he _ hb e hx'
 unfold a skyGlow; rw [quant_one,act_one,norm_inner_symm]
end YM.CF.Rapids
