import GaugeFieldConstruction.Wigand
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
lemma corner_0 (M:Male)(b:Bool) : (pilotS M b).1= baseF b:=(kiosk_P M b).point.symm.trans (binBase ..)
section budget
variable {E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
set_option maxHeartbeats 60000 in
lemma pre_cost (P:Ole E F)(f:G→L[ℝ] E)(u:‖f‖≤1): CostOle (pre P f)≤CostOle P:=by
 rw [CostOle,Prod.norm_def,Prod.norm_def ((pre P f).2)] -- tune
 refine max_le (le_max_left ..) (max_le (le_trans ((ContinuousLinearMap.opNorm_comp_le _ f).trans (mul_le_of_le_one_right (norm_nonneg _) u)) ((le_max_left ..).trans (le_max_right ..))) ?_)
 let M:=pre P f
 apply ContinuousLinearMap.opNorm_le_bound M.2.2.val (norm_nonneg P); intro i; apply ContinuousLinearMap.opNorm_le_bound _ (M:=‖P‖*‖i‖) (by positivity); intro j; let T:=P.2.2.val
 have ht(k:G): ‖f k‖≤ ‖k‖:=(f.le_opNorm k).trans (mul_le_of_le_one_left (norm_nonneg _) u)
 let a:=T (f i); refine (a.le_opNorm (f j)).trans (mul_le_mul (le_trans (T.le_opNorm _) (mul_le_mul ((le_max_right ..).trans (le_max_right ..)|>.trans le_rfl : ‖T‖ ≤ ‖P‖) (ht _) (norm_nonneg _) (norm_nonneg P))) (ht _) (norm_nonneg _) (mul_nonneg (norm_nonneg P) (norm_nonneg _))) -- tune
set_option maxHeartbeats 150000 in
lemma oreP {V:Type}[NormedRing V][NormedAlgebra ℝ V](x y:Ole E V) : CostOle (cartF x y) ≤ 4*CostOle x*CostOle y:=by
 let A:=CostOle x; let B:=CostOle y; let X:=cartF x y; have hx:0≤A:= norm_nonneg x; have hv:0≤ B:=norm_nonneg y; let d:=4*A*B; have hd:0≤ d:=by positivity
 have j0(u:Ole E V): ‖u.1‖≤CostOle u:= le_max_left ..
 have j1(u:Ole E V)(a:E): ‖u.2.1 a‖ ≤ CostOle u*‖a‖:= (u.2.1.le_opNorm a).trans (mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (norm_nonneg _))
 have j2(u:Ole E V)(a b:E): ‖u.2.2.val a b‖≤ CostOle u*‖a‖*‖b‖:= (u.2.2.val a|>.le_opNorm _).trans (mul_le_mul_of_nonneg_right ((u.2.2.val.le_opNorm a).trans (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (norm_nonneg _))) (norm_nonneg _))
 unfold CostOle; rw [Prod.norm_def (cartF x y), Prod.norm_def ((cartF x y).2)]
 refine max_le ?_ (max_le ?_ ?_)
 · rw [cart_0]; exact (norm_mul_le ..).trans ((mul_le_mul (j0 x) (j0 y) (norm_nonneg _) hx).trans (by linarith only [mul_nonneg (norm_nonneg x) (norm_nonneg y)]))
 · refine ContinuousLinearMap.opNorm_le_bound X.2.1 hd fun i=>?_ ; change ‖(cartF x y).2.1 i‖ ≤ _; rw [cart_1]; apply (norm_add_le ..).trans; have hr:= add_le_add ((norm_mul_le ..).trans (mul_le_mul (j1 x i) (j0 y) (norm_nonneg _) (by unfold CostOle; positivity))) ((norm_mul_le ..).trans (mul_le_mul (j0 x) (j1 y i) (norm_nonneg _) hx)); apply hr.trans; change A* ‖i‖* B+A*(B*‖i‖)≤ d*‖i‖; unfold d; linarith only [mul_nonneg (mul_nonneg hx hv) (norm_nonneg i)]
 apply ContinuousLinearMap.opNorm_le_bound X.2.2.val hd; intro i; apply ContinuousLinearMap.opNorm_le_bound _ (M:=d*‖i‖) (by positivity); intro j; unfold X; rw [cart_2]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (j2 x i j) (j0 y) (norm_nonneg _) (by unfold CostOle; positivity))) ((norm_mul_le ..).trans (mul_le_mul (j0 x) (j2 y i j) (norm_nonneg _) hx)))) ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (j1 x i) (j1 y j) (norm_nonneg _) (by unfold CostOle; positivity))) ((norm_mul_le ..).trans (mul_le_mul (j1 x j) (j1 y i) (norm_nonneg _) (by unfold CostOle; positivity)))))).trans_eq ?_); unfold d A B; ring
end budget
variable (M:Male)(b:Bool)
-- projected PH-M. matrix motion. Jets & norm.
abbrev PalOne := Ole Views Pal
abbrev bladeL (b:Bool):PalOne:= (baseF b,0,0)
def wheelP : PalOne := pre (pilotS M b) (if b then ContinuousLinearMap.snd .. else ContinuousLinearMap.fst ..)
def fellP (x:Views):= binor M b (if b then x.2 else x.1)
def palCart (x y:PalOne):PalOne:= cartF x y
lemma cart_K {f g:Views→Pal}{u v:PalOne}(p:AptK f u)(h:AptK g v): AptK (fun x=> f x*g x) (palCart u v):= p.cart h
set_option maxHeartbeats 60000 in
lemma plankK:AptK (fellP M b) (wheelP M b):=by
 cases b
 · exact (kiosk_P M false).preC (ContinuousLinearMap.fst ℝ Plane Plane)
 exact (kiosk_P M true).preC (ContinuousLinearMap.snd ℝ Plane Plane)
lemma plan_o : (wheelP M b).1=baseF b:=corner_0 ..
lemma bladeSeal : IsStarProjection (baseF b) := by
 let M:Tulip.Male:=⟨1,odd_one⟩; exact binBase M b ▸ (show IsStarProjection (binor M b 0) from (palP M b).self_of_nhds)
-- costs pay def using global lemma; use NormedRing group Ambig ν.
set_option maxHeartbeats 60000 in
lemma wheel_C : CostOle (wheelP M b) ≤ BasePrice b:=by
 cases b
 · change CostOle (pre _ (ContinuousLinearMap.fst ℝ Plane Plane)) ≤ BasePrice false; exact (pre_cost (pilotS M false) (ContinuousLinearMap.fst ℝ Plane Plane) (ContinuousLinearMap.norm_fst_le ..)).trans (cost_pkt M _)
 exact (pre_cost (pilotS M true) (ContinuousLinearMap.snd ℝ Plane Plane) (ContinuousLinearMap.norm_snd_le ..)).trans (cost_pkt M _)
lemma pal_cost (x y:PalOne):CostOle (palCart x y) ≤ 4 *CostOle x*CostOle y:= oreP x y -- tune
abbrev winJ (o:Skye.Seat n)(M:Male)(h:ℝ)(Q: Op (Single n)):PalOne:=
 palCart (bladeL false) (palCart (wheelP M false) (palCart (markJet o Q h) (palCart (wheelP M true) (bladeL true))))
-- replace B(0) embedded. Actual projector. 
def TabX (o:Skye.Seat n)(M:Male)(h:ℝ)(Q: Op (Single n))(x:Views):Pal:= baseF false*(fellP M false x*(streamF o Q h x*(fellP M true x*baseF true)))
lemma tab (Q: Op (Single n)): AptK (TabX o M h Q) (winJ o M h Q):= cart_K (AptK.const _) (cart_K (plankK M false) (cart_K (K_pays o Q h) (cart_K (plankK M true) (AptK.const _))))
-- binned and constant-gauge assertions
lemma soak_X (Q:Op (Single n))(x:Views): baseF false* TabX o M h Q x * baseF true= TabX o M h Q x:=by
 let i:= (bladeSeal false); let a:= baseF false; let b:= baseF true; let A:=streamF o Q h x; let L:= fellP M false x*(A*fellP M true x); have he:TabX o M h Q x=a*(L*b):= by unfold TabX a b L A; simp only [mul_assoc]
 rw [he,←mul_assoc,i.1.eq,mul_assoc,mul_assoc,show b*baseF true=b from (bladeSeal true).1.eq]; try rfl -- tune multiply chain
lemma Pal_F (F:Op (Single n)):‖F‖=‖F‖:=rfl
end Lenten
end YM.CF.TableF
end
