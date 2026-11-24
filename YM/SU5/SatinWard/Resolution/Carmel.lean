/- adaptation of LitCurrent.Source, Reached, Copy to sectors.
 Exact same expenditures on untouched and retained, using that scope on same pattern after cut. -/
import YM.SU5.SatinWard.Resolution.Chevy
import YM.SU5.LitCurrent.ReflectLeg
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
open Buffered Salt
-- Circ on Pane too: note one mesh q, areal. shared mask for tax (inc bar subtraction)
-- and for each chir ingredient.
variable {P T:SOp N} {p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
open Urn

namespace Chamber
section proof
variable (bI:Division)(K:Scree.Loom N)(p:BudgetPoint)(k:ℕ)(w:ℝ)(x:Site N)(E:Pattern P T r d a v)
local notation "S"=>offsetMask p.B x
local notation "Â"=> skyHat bI x E K p k
local notation "J"=> centHat bI x E K p k
local notation "Λ"=> (tickA N)
private lemma seed_dg (w:ℝ)(A:Op I): Continuous (preHalf w A):=by
 have he: Continuous (Fock.dg (n:=I)):=by unfold dg dyad; refine continuous_finsetSum _ fun i _=>?_ ; refine continuous_finsetSum _ fun j _=>?_ ; exact (continuous_id.matrix_elem i j).smul continuous_const
 unfold preHalf preJ; exact ((((continuous_const.mul continuous_id).matrix_trace).smul continuous_const).add (he.comp ((continuous_const.mul continuous_id).mul continuous_const))).sub ((continuous_const (y:=(w:ℂ))).smul ((continuous_id.matrix_trace).smul (continuous_const (y:=(1:FC I)))))
variable (z:Checked p K t d a k q)
local notation "HΩ"=>tendril p r x
local notation "MΩ"=>modesIn N HΩ
local notation "Y"=>jewelO bI x E K p k w
local notation "Ξ"=>jewelT bI x E K p k w
include z
lemma gauge_support : AtSupport false (inspectFoot p x) (jewelY bI x E K p k) := by
 let f:Pane N→ FC I:= fun U=>Matrix.trace (Â U) • 1
 change AtSupport false _ (toMark f); refine AtSupport.fromEval f (Girt.pole_w Â _ (continuous_id.matrix_trace.smul continuous_const) (enve_pass x _ z (show moored (node x) (grantA bI E x) from E.moorA x))) (fun U V u=> congrArg (fun z:Op I=> Matrix.trace z • (1:FC I)) (live_local x _ z (show moored (node x) (grantA bI E x) from E.moorA x) U V u)) (fun U=> Reed.Fine.one.scale _)
lemma current_support (e:FaceDir) : AtSupport false (inspectFoot p x) (jewelJ bI x E K p k w e):=by
 let f:Pane N→ FC I:= fun V=> preHalf w Λ (J e V)
 have ht:= show moored (node x) (grantJ bI E (x,e)) from E.moorJ (x,e)
 refine AtSupport.fromEval f (Girt.pole_w (J e) (preHalf w Λ) (seed_dg ..) (enve_pass x _ z ht)) (fun U V h=>congrArg (preHalf w Λ) (live_local x _ z ht _ _ h)) ?_
 intro U; unfold f preHalf; rw [touchP,sub_eq_add_neg]
 exact Reed.Fine.add (Window.fine_enlarge (modes_monotone (halo_foot p x)) (inSector (J e U) (Tset N) _ (modes_pass x _ z ht (U,Classical.arbitrary (Ids N))))) (Buffered.fine_neg ((Reed.Fine.one.scale _).scale _))
lemma physical_support : AtSupport false (tendril p r x) Y:=by
 let Z:= fun e=>jewelJ bI (destSite x r e) E K p k w e
 have ht(e:FaceDir):inspectFoot p (destSite x r e) ⊆ tendril p r x := fun i hi=> mem_union_right _ (mem_biUnion.mpr ⟨e,mem_univ _,hi⟩)
 apply (gauge_support bI K p k x E z|>.mono subset_union_left).addM
 change AtSupport false HΩ (∑ e,Z e)
 suffices h:∀ T:Finset FaceDir, AtSupport false HΩ (∑ e∈T,Z e) from h _
 intro A; induction A using Finset.induction_on with
 |empty=> rw [sum_empty]; exact AtSupport.zeroM
 |insert i A v ih=>rw [sum_insert v]; exact ((current_support bI K p k w _ E z i).mono (ht i)).addM ih
lemma gauge_moves : covariant (jewelY bI x E K p k):=by
 intro i g; change Matrix.trace (live K p k x (grantA bI E x) (gauge i g.1)) • 1= twist _ (Matrix.trace (Â g.1) • 1); rw [glyphMove x (grantA bI E x) z (E.moorA x), trace_twist,twist_scalar,map_one]; rfl
lemma current_moves (e:FaceDir) : covariant (jewelJ bI x E K p k w e):=by
 intro g U; let t:=tradew N g
 change preHalf w Λ (J e (gauge g U.1))= twist (quantU t) (preHalf w Λ (J e U.1)); let Y':= J e U.1
 have hp:=glyphMove x _ z (show moored (node x) (grantJ bI E (x,e)) from E.moorJ (x,e)) U.1 g
 rw [show J e (gauge g U.1)=twist t Y' from hp]
 change preHalf _ _ _= twist _ (preHalf w Λ Y')
 unfold preHalf preJ; rw [map_sub,map_add, twist_scalar,twist_scalar,twist_scalar,map_one,dg_cov,map_mul,map_mul,Cascade.tick_g, map_sub,map_one,Cascade.tick_g, trace_twist, ←show twist t (Λ*Y')= _ from (show twist t (Λ*Y')=Λ*twist t Y' from (by rw [map_mul,Cascade.tick_g])) ,trace_twist]
lemma physical_moves : covariant Y:=by
 intro g U; simp only [jewelO,Pi.add_apply,map_add,gauge_moves bI K p k x E z g U,Finset.sum_apply,map_sum,current_moves bI K p k w _ E z _ g U]

omit z in
lemma centered_bra (V: Fields N) : acts (star (Y V)) (mateK N)=acts (star (Ξ V)) (mateK N):=by
 let A:=mateK N; have he: IsStarProjection Λ:=touchP N ▸ cutM_idp _
 have hp : acts (star (jewelExcess bI x p r V)) A=0:=by
    unfold jewelExcess; split
    · rw [star_sub, star_smul,star_one,act_sub,act_smul,act_one,sandwichV (hall bI (roomW x r)) he (traffic bI x r) (mateK N) (tickB N),sub_self]
    rw [star_zero,act_zero]
 simp only [jewelO,jewelT,Pi.sub_apply,Pi.add_apply,star_sub,star_add,act_sub,act_add,Finset.sum_apply,star_sum,act_sum]
 change _=_-acts (star (jewelExcess bI x p r V)) A; rw [hp,sub_zero]; apply congrArg₂ (·+·) rfl; apply sum_congr rfl; intro e _
 unfold jewelJ jewelLeg preHalf liftHalf; simp only [star_sub,act_sub]; rw [bra_eq _ he _ (tickB N)]
-- better actual spelling
omit z in
private lemma preHalf_neg (A:Op I): preHalf w Λ (-A)= -preHalf w Λ A:=by unfold preHalf preJ; simp only [mul_neg, neg_mul,Matrix.trace_neg,dg_neg,neg_smul,smul_neg]; abel
lemma currentSeed_anti (y:Fields N)(e:FaceDir): jewelJ bI x E K p k w (axisFlip e) y= -jewelJ bI x E K p k w e y:=by
 let U:Orbit N:=(y.1,Classical.arbitrary _); unfold jewelJ centHat; rw [show live K p k x _ _=_ from show live K p k x (grantJ bI E (x,axisFlip e)) y.1= -live K p k x (grantJ bI E (x,e)) y.1 from by
   unfold grantJ; rw [live_at,live_at,show live K p k x _ y.1= _ from E.cabaret z x e U]; unfold hall; rw [mul_neg,neg_mul], preHalf_neg]; -- tune method
lemma physical_spelling (V:Fields N): Y V= (jewelY bI x E K p k) V+ ∑ i:Axis,((jewelJ bI (x+r • step i) E K p k w (i,false) V)-(jewelJ bI (x-r • step i) E K p k w (i,false) V)):=by
 unfold jewelO; rw [Pi.add_apply,Finset.sum_apply, Fintype.sum_prod_type]; refine congrArg _ (sum_congr rfl fun i _=> ?_); rw [Fintype.sum_bool, show (i,true)=axisFlip (i,false) from rfl,currentSeed_anti bI K p k w _ E z V]; simp [sub_eq_add_neg,destSite,strideD,Step.vec,axisFlip]; abel
omit z
lemma literal_current (x:Site N)(e:FaceDir)(V:Fields N):jewelJ bI x E K p k 0 e V=preJ Λ (centHat bI x E K p k e V.1):=by unfold jewelJ preHalf; rw [Complex.ofReal_zero,zero_smul,sub_zero]
include z
lemma surrogate_sector (l:ℕ)(h:p.B+2*r+12 ≤ l*p.B)(t:8*r≤p.B)(U:Fields N):
    Fock.Sector (modesIn N (grooveB l p (node x))) false (jewelT bI x E K p k w U):=by
 let M:=modesIn N (grooveB l p (node x))
 have hx(y:Site N)(v:inspectFoot p y⊆ tendril p r x): modesIn N (offsetMask p.B y) ⊆ M:= modes_monotone (((halo_foot p y).trans v).trans (words_fit p x l h)) -- syntax
 rw [jewelT, Pi.sub_apply,Pi.add_apply,Finset.sum_apply,sub_eq_add_neg]
 refine Fock.Sector.add (Fock.Sector.add (Fock.Sector.one.scale _) ?_) ?_ -- name
 · apply Fock.Sector.sumS; intro i v; let y:=destSite x r i; let F:=centHat bI y E K p k i; have ht:=pair_charge (modes_pass y (grantJ bI E (y,i)) z (E.moorJ (y,i)) (U.1,Classical.arbitrary _))
   change Fock.Sector M false (liftHalf w (F U.1)); rw [liftHalf,sub_eq_add_neg,← neg_one_smul ℂ]
   exact Fock.Sector.add (lift_v ht (hx y (fun x X=>mem_union_right _ (mem_biUnion.mpr ⟨i,v,X⟩)))) (((Sector.one.scale _).scale _).scale _)
 rw [←neg_one_smul ℂ]; apply Fock.Sector.scale; unfold jewelExcess; split
 · rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact Sector.add (lift_v (pair_charge (transparent bI x _ t)) (hx x subset_union_left)) ((Sector.one.scale _).scale _)
 exact Sector.zero _
end proof

open Salt
variable {bI:Division}{P T:SOp N}{p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
section travels
variable (bI:Division)(x:Site N)(E:Pattern P T r d a v)
variable (z:Checked p K t d a k q)(s:Sweep N)(U:Pane N)(i:FaceDir)
include z
lemma sky_roll: live K p k (pose s x) (grantA bI E (pose s x)) (flashA s U)=realR s true (live K p k x (grantA bI E x) U) :=by unfold grantA; rw [live_at,live_at, E.rollTax z x s U,travelR]
lemma cent_roll:live K p k (pose s x) (grantJ bI E (teamTravel s (x,i))) (flashA s U)= realR s false (live K p k x (grantJ bI E (x,i)) U):=by unfold grantJ; rw [live_at,live_at, E.rollCurrent z x i s U,travelR]
omit z
lemma room_Ξ (r:ℕ) (s:Sweep N):ech s (hall bI (roomW x r))=hall bI (roomW (pose s x) r):=by unfold hall; rw [echo_mult,echo_mult,travel,room_move]
end travels

variable (bI:Division)(x:Site N)(z:Checked p K t d a k q)(E:Pattern P T r d a v) (s:Sweep N)
local notation "R"=>det_S s
local notation "A"=>tickA N
local notation "O"=>lotB s.charge R (γS s)
local notation "g"=>flashA s
local notation "u1"=>pose s x
local notation "H‼"=>Scroll.hush R
variable (X Y:Fields N)(w:Y.1=flashA s X.1)

include z w
lemma poses_gauge : O (jewelY bI x E K p k X)=H‼ (jewelY bI u1 E K p k Y):=by
 unfold jewelY skyHat; rw [w,show live K p k u1 (grantA bI E u1) (flashA s X.1)=_ from (sky_roll bI x E z s X.1),visage,map_one, ← Sault.lune s.charge R (γS s)]
 let F:=live K p k x (grantA bI E x) X.1; change Matrix.trace (if R then star (ech s F) else ech s F) • 1=H‼ (Matrix.trace (Thera.jazz R (ech s F)) • 1); cases R <;> simp [Thera.jazz]
lemma poses_current (i:FaceDir): O (jewelJ bI x E K p k (1/2) i X)=H‼ (jewelJ bI u1 E K p k (1/2) (faceAt s i) Y):=by
 unfold jewelJ centHat; rw [w]; change _=H‼ (preHalf (1/2) A (live _ _ _ _ (grantJ bI E (teamTravel s (x,i))) _)); rw [cent_roll _ _ _ z]; exact carryPre _ _ _ _ _ _ (tick_travel s) (touchP N ▸ cutM_idp _)
lemma poses_fat (i:FaceDir): O (jewelLeg bI x E K p k (1/2) i X)= H‼ (jewelLeg bI u1 E K p k (1/2) (faceAt s i) Y):=by
 unfold jewelLeg centHat; rw [w]; change _=H‼ (liftHalf (1/2) (live _ _ _ _ (grantJ bI E (teamTravel s (x,i))) _)); rw [cent_roll _ _ _ z]; exact lotHalf ..
omit z w
lemma paints_room : doveL s.charge R (γS s) ((hall bI (roomW x r)))=(hall bI (roomW u1 r)):=by unfold doveL; rw [show sings _ _ _=_ from room_Ξ bI x r s,tStar,ite_self]
private lemma poses_s : let V:=(hall bI (roomW x r)); let Y:=(hall bI (roomW (pose s x) r))
    cSignX (s.charge.xor R) ((A*V).trace)= if R then Y.trace-(A*Y).trace else (A*Y).trace:=by
 intro v J; rw [← Sault.lune s.charge R (γS s)]; unfold doveL; rw [singm,show sings _ _ A=_ from tick_travel s,show sings _ _ v=J from room_Ξ bI x r s]; cases h:R; rfl
 simp only [ite_true,swapX,star_mul, show star J=J from tStar .., star_sub,star_one,tick_star]; rw [Matrix.trace_mul_comm J, sub_mul,one_mul,Matrix.trace_sub]
private lemma sign_real (b:Bool)(v:ℝ): cSignX b (v:ℂ)=(v:ℂ):=by cases b; rfl; simp [cSignX]
include w
lemma poses_excess (r:ℕ)(p:BudgetPoint): O (jewelExcess bI x p r X)=H‼ (jewelExcess bI u1 p r Y):=by
 unfold jewelExcess; rw [offset_pose,w]; let q:=p.threshold
 have hp:= glowA q (offsetMask p.B x) s X.1
 split; swap; next t=> rw [if_neg (mt hp.mp t),map_zero]; cases R<;>simp
 next u=>
 rw [if_pos (hp.mpr u)]; let T:= (hall bI (roomW x r)); let V:=(hall bI (roomW (pose s x) r)); have hx:modesIn N univ=modesIn N univ:=rfl
 have ht: O (liftHalf (1/2) T)= H‼ (liftHalf (1/2) V):=by rw [lotHalf,show Sault.doveL _ _ _ T= _ from Chamber.paints_room bI x s] -- syntax
 have hv(X:Op I):dg X= liftHalf (1/2) X+ (((1/2:ℝ):ℂ) • (X.trace • 1)):=by unfold liftHalf; abel
 have hL:Matrix.trace V=cSignX (s.charge.xor R) (Matrix.trace T):= by rw [←Sault.lune]; exact congrArg Matrix.trace (Chamber.paints_room bI x s|>.symm)
 change O (dg T- _) = H‼ (dg V-_)
 rw [hv T,hv V,map_sub,map_add,visage,visage,visage,map_one,ht,←hL,show cSignX _ ((A*T).trace)=_ from Chamber.poses_s bI x s, sign_real]
 cases R
 · simp
 simp only [ite_true,hush_true,sub_smul]; module
omit w
private lemma hush_sum {ι:Type*}[Fintype ι](F:ι→FC I) (q:Bool): Scroll.hush q (∑ i:ι,F i)=∑ i:ι, Scroll.hush q (F i) :=by cases q; rfl; simp
private lemma hush_add(F G:FC I): H‼ (F+G)=H‼ F+H‼ G:=by cases R; rfl; simp [add_comm]
private lemma hush_sub(F G:FC I): H‼ (F-G)=H‼ F-H‼ G:=by cases R; rfl; simp; abel
include z w
lemma posesY : O (jewelO bI x E K p k (1/2) X)=H‼ (jewelO bI u1 E K p k (1/2) Y):=by
 simp only [jewelO,Pi.add_apply,map_add,Finset.sum_apply,map_sum,hush_add,hush_sum,Chamber.poses_gauge bI x z E s X Y w]; refine congrArg _ ?_
 let W(i:FaceDir):= H‼ (jewelJ bI (destSite u1 r i) E K p k (1/2) i Y)
 refine Eq.trans (b:= ∑ i:FaceDir,W (bearings s i)) (sum_congr rfl fun i _=>?_) (Equiv.sum_comp (bearings s) W)
 unfold W; change _= H‼ (jewelJ bI (destSite u1 r (faceAt s i)) E K p k (1/2) (faceAt s i) Y); rw [←pose_hop]; exact poses_current bI _ z E _ _ _ w i
lemma poses_surrogate : O (jewelT bI x E K p k (1/2) X) =H‼ (jewelT bI u1 E K p k (1/2) Y):=by
 simp only [jewelT,Pi.sub_apply,Pi.add_apply,map_add,map_sub,Finset.sum_apply,map_sum,hush_sub,hush_add,hush_sum,Chamber.poses_gauge bI x z E s X Y w,Chamber.poses_excess bI x s X Y w]
 congr 2 -- tune
 let W(i:FaceDir):=H‼ (jewelLeg bI (destSite u1 r i) E K p k (1/2) i Y)
 refine Eq.trans (b:= ∑ i:FaceDir,W (bearings s i)) (sum_congr rfl fun i _=> ?_) (Equiv.sum_comp (bearings s) W)
 unfold W; change _= H‼ (jewelLeg bI (destSite u1 r (faceAt s i)) E K p k (1/2) (faceAt s i) Y); rw [←pose_hop]; exact poses_fat bI _ z E _ _ _ w i

#print axioms Chamber.posesY
end Chamber
end YM.CF.LitCurrent
