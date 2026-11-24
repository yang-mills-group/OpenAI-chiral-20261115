import YM.SU5.LitCurrent.Source
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Urn Salt
variable {P T:SOp N}{p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
variable (x:Site N)(z:Checked p K t d a k q)(E:Pattern P T r d a v) (s:Sweep N)
local notation "R"=>det_S s
local notation "A"=>tickA N
local notation "O"=>lotB s.charge R (γS s)
local notation "g"=>flashA s
local notation "u1"=>pose s x
local notation "H"=>Scroll.hush R
variable (X Y:Fields N)(w:Y.1=flashA s X.1)

include z w
lemma poses_gauge : O (gaugeSeed K p k x E X)=H (gaugeSeed K p k u1 E Y):=by
 unfold gaugeSeed taxHat; rw [w,E.rollTax z,visage,map_one, ← Sault.lune s.charge R (γS s)]
 let F:=live K p k x (E.A x) X.1; change Matrix.trace (if R then star (ech s F) else ech s F) • 1=H (Matrix.trace (Thera.jazz R (ech s F)) • 1); cases R <;> simp [Thera.jazz]
lemma poses_current (i:FaceDir): O (currentSeed K p k (1/2) x E i X)=H (currentSeed K p k (1/2) u1 E (faceAt s i) Y):=by
 unfold currentSeed carrierHat; rw [w]; change _=H (preHalf (1/2) A (live _ _ _ _ (E.J (teamTravel s (x,i))) _)); rw [E.rollCurrent z]; exact carryPre _ _ _ _ _ _ (tick_travel s) (touchP N ▸ cutM_idp _)
lemma poses_fat (i:FaceDir): O (fatSeed K p k (1/2) x E i X)= H (fatSeed K p k (1/2) u1 E (faceAt s i) Y):=by
 unfold fatSeed carrierHat; rw [w]; change _=H (liftHalf (1/2) (live _ _ _ _ (E.J (teamTravel s (x,i))) _)); rw [E.rollCurrent z]; exact lotHalf ..
omit z w
lemma paints_room : doveL s.charge R (γS s) (roomW x r)=roomW u1 r:=by unfold doveL; rw [show sings _ _ _=_ from room_move s r x,room_star,ite_self]
private lemma poses_s : let V:=roomW x r; let Y:=roomW (pose s x) r
    cSignX (s.charge.xor R) ((A*V).trace)= if R then Y.trace-(A*Y).trace else (A*Y).trace:=by
 intro v J; rw [← Sault.lune s.charge R (γS s)]; unfold doveL; rw [singm,show sings _ _ A=_ from tick_travel s,show sings _ _ v=J from room_move s r x]; cases h:R; rfl
 simp only [ite_true,swapX,star_mul, show star J=J from room_star .., star_sub,star_one,tick_star]; rw [Matrix.trace_mul_comm J, sub_mul,one_mul,Matrix.trace_sub]
private lemma sign_real (b:Bool)(v:ℝ): cSignX b (v:ℂ)=(v:ℂ):=by cases b; rfl; simp [cSignX]
include w
lemma poses_excess (r:ℕ)(p:BudgetPoint): O (excess p x r X)=H (excess p u1 r Y):=by
 unfold excess; rw [offset_pose,w]; let q:=p.threshold
 have hp:= glowA q (offsetMask p.B x) s X.1
 split; swap; next t=> rw [if_neg (mt hp.mp t),map_zero]; cases R<;>simp
 next u=>
 rw [if_pos (hp.mpr u)]; let T:= roomW x r; let V:=roomW (pose s x) r; have hx:modesIn N univ=modesIn N univ:=rfl
 have ht: O (liftHalf (1/2) T)= H (liftHalf (1/2) V):=by rw [lotHalf,show Sault.doveL _ _ _ T= _ from paints_room x s] -- syntax
 have hv(X:Op I):dg X= liftHalf (1/2) X+ (((1/2:ℝ):ℂ) • (X.trace • 1)):=by unfold liftHalf; abel
 have hL:Matrix.trace V=cSignX (s.charge.xor R) (Matrix.trace T):= by rw [←Sault.lune]; exact congrArg Matrix.trace (paints_room x s|>.symm)
 change O (dg T- _) = H (dg V-_)
 rw [hv T,hv V,map_sub,map_add,visage,visage,visage,map_one,ht,←hL,show cSignX _ ((A*T).trace)=_ from poses_s x s, sign_real]
 cases R
 · simp
 simp only [ite_true,hush_true,sub_smul]; module
omit w
private lemma hush_sum {ι:Type*}[Fintype ι](F:ι→FC I) (q:Bool): Scroll.hush q (∑ i:ι,F i)=∑ i:ι, Scroll.hush q (F i) :=by cases q; rfl; simp
private lemma hush_add(F G:FC I): H (F+G)=H F+H G:=by cases R; rfl; simp [add_comm]
private lemma hush_sub(F G:FC I): H (F-G)=H F-H G:=by cases R; rfl; simp; abel
include z w
lemma posesY : O (physicalSeed K p k (1/2) x E X)=H (physicalSeed K p k (1/2) u1 E Y):=by
 simp only [physicalSeed,Pi.add_apply,map_add,Finset.sum_apply,map_sum,hush_add,hush_sum,poses_gauge x z E s X Y w]; refine congrArg _ ?_
 let W(i:FaceDir):= H (currentSeed K p k (1/2) (destSite u1 r i) E i Y)
 refine Eq.trans (b:= ∑ i:FaceDir,W (bearings s i)) (sum_congr rfl fun i _=>?_) (Equiv.sum_comp (bearings s) W)
 unfold W; change _= H (currentSeed K p k (1/2) (destSite u1 r (faceAt s i)) E (faceAt s i) Y); rw [←pose_hop]; exact poses_current _ z E _ _ _ w i
lemma poses_surrogate : O (surrogate K p k (1/2) x E X) =H (surrogate K p k (1/2) u1 E Y):=by
 simp only [surrogate,Pi.sub_apply,Pi.add_apply,map_add,map_sub,Finset.sum_apply,map_sum,hush_sub,hush_add,hush_sum,poses_gauge x z E s X Y w,poses_excess x s X Y w]
 congr 2 -- tune
 let W(i:FaceDir):=H (fatSeed K p k (1/2) (destSite u1 r i) E i Y)
 refine Eq.trans (b:= ∑ i:FaceDir,W (bearings s i)) (sum_congr rfl fun i _=> ?_) (Equiv.sum_comp (bearings s) W)
 unfold W; change _= H (fatSeed K p k (1/2) (destSite u1 r (faceAt s i)) E (faceAt s i) Y); rw [←pose_hop]; exact poses_fat _ z E _ _ _ w i
end YM.CF.LitCurrent
