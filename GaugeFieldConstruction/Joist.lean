import GaugeFieldConstruction.Kittles
import YM.CF.Roots.Seat
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
namespace Layout
open HushP ModuleB Pastry
-- entries in PH houses: both endpoints. not represented yet as Mark physical.
open Housing
variable (o:Skye.Seat n)
-- A1 frame: g star transport from root at x. B_F paid using transported O.
-- algebra of insertion indices (complex linear in G). prove on paid subspace.
open Flot
set_option maxRecDepth 2800
variable (M:Tulip.Male)
open scoped YM.CF.Mew
variable {T U V:InkD n}{F W:Waves}{a b:ℝ}(h)
-- linear tests (C*)
omit M
include M
lemma sectorθ (U:Op (Single n))(A:ℂ): (αxp M o h) (A • U)=A • ((αxp M o h) U):= sector_scale M U A
lemma orbit_π(U:Cipher n)(a:ℂ): orbitPH (a • U)= a • orbitPH U:=by
 ext i j; unfold Haro.orbitPH; simp only [Matrix.smul_apply,Matrix.of_apply, Prism.port_eq, show (true,i) ≠ (false,j) by simp,if_false]; rw [show crumb (a • U).val _= _ from (show _= a*crumb U.val (Haro.tray i j) from crumb_scale ..),smul_eq_mul,mul_left_comm]
lemma stream_plus (u v: Op (Single n))(x:Views): streamF o (u+v) h x= streamF o u h x+ streamF o v h x:=by unfold streamF; simp only [hill_Z,Matrix.add_apply,mul_add,map_add,sum_add_distrib]
lemma stream_c (u:Op (Single n))(a:ℂ)(x:Views): streamF o (a • u) h x=a • streamF o u h x:=by
 rw [streamS,streamS,Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [Finset.smul_sum]; apply sum_congr rfl; intro j _; rw [show matPH (a • u) i j=a • matPH u i j from rfl]; rw [smul_comm]
omit M
lemma muck (U:InkD n)(s:ℂ): term (s • U)= s • term U:= rfl
lemma life_zero (x:ℂ) : lifeH (0:InkD n) 1=0:=rfl -- tune
lemma life_add (X Y:InkD n): lifeH (X+Y)= lifeH X+lifeH Y:=rfl
lemma life_smul(X:InkD n)(s:ℂ): lifeH (s • X)=s • lifeH X:=rfl
lemma life_hz(z:ℂ):lifeH (fun _:Pane n=> hollow z)=fun _=>z:=funext fun i=>hullB _
lemma fees_Z (z:ℂ):PressB p (Zhub o) (fun _=> hollow z) h ‖z‖:= Moto.litho p (Zhub o) _ (L:=fun _=> z) (p:= fun _ _ _=>rfl) (s:=fun i j=>rfl) (q:= measurable_const) (norm_nonneg _) (fun U e=>Prism.hail le_rfl) -- tune
include M
variable {h}
set_option maxHeartbeats 150000 in
lemma linearHE (t:MetaB o M F T p h) (u: PressB p (Zhub o) T h a)(s:ℂ)(g:0≤h) : MetaB o M (s • F) (s • T) p h:=by
 let K:ℂ→L[ℝ]ℂ:= s • ContinuousLinearMap.id ℝ ℂ
 let he:= (eraF T _ u g 1 (ping_f p _)).paid
 have hv(i j:tangD n): ploy (s • T) i j= s • ploy T i j:=by rw [ploy_iter,muck T,show s • term T= K ∘ term T from rfl, K.iteratedFDeriv_comp_left (f:=term T) he (i:=2) (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge)),ploy_iter]; rfl
 constructor
 · change (s • (bF4 F).val) = _; rw [t.post]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hv _ _).symm
 · change s • bF5 F= _; rw [t.mast]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hv _ _).symm
 · let U:=orbitPH (T 1); let Z:= pawnC s
   rw [Pi.smul_apply, orbit_π M]; -- tune explicit
   have tX: (fun x=>TabX o M h (s • U) x)= fun x=> Z (TabX o M h U x):=by funext x; unfold TabX; rw [stream_c h o M U s x]; simp only [Matrix.smul_mul,Matrix.mul_smul]; rfl
   have hg: postF (chartF F) Z= chartF (s • F):=by
      apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun i=>?_) (dual_uni _ _ fun i=>?_))<;>rfl
   rw [←hg,t.port]; exact ((tab (o:=o) (h:=h) M U|>.geomF Z).equal (Eventually.of_forall fun i=>(congrFun tX i).symm)).unique (tab M _)
 · change s • (bm5 F).val=_; rw [t.mixed]; apply ContinuousLinearMap.ext; intro i;
   let L(t:ℝ):= increment 1 (t • gateC o p.threshold i); let Z:= pawnC s
   have ht: HasDerivAt (fun t=>sectorJ (orbitPH (s • T (L t))) M o h) (s • landA M o T p h i) 0:=by
       simp_rw [orbit_π M -- tune
         ,sector_scale]
       exact Z.hasFDerivAt.comp_hasDerivAt 0 (landR M (o:=o) u i)
   exact ht.unique (landR M (o:=o) (Roots.súe _ _ u s) i)
omit M
lemma ployP_add {q:InkD n} (U:PressB p X T h a)(V:PressB p X q h b)(z:0≤h)(x y:tangD n): ploy (T+q) x y=ploy T x y+ploy q x y:=by
 rw [ploy_iter,show term (T+q)=term T+term q from rfl, iteratedFDeriv_add_apply (f:=term T) (g:=term q) ((eraF _ _ U z 1 (ping_f p _)).paid.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge))) ((eraF _ _ V z 1 (ping_f p _)).paid.of_le (Nat.cast_le.mpr ((by decide:2≤6).trans p.order_ge))),ploy_iter,ploy_iter]; rfl
include M
set_option maxHeartbeats 150000 in
lemma linearHU (t:MetaB o M F T p h)(pX:MetaB o M W U p h)(g:0≤ h)(u:PressB p X T h a)(v:PressB p X U h b): MetaB o M (F+W) (T+U) p h:=by
 constructor
 · change (bF4 F).val+ (bF4 W).val=_; rw [t.post,pX.post]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (ployP_add u v g _ _).symm
 · change bF5 F+bF5 W=_; rw [t.mast,pX.mast]; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (ployP_add u v g _ _).symm
 · let Z:=orbitPH (T 1); let V:=orbitPH (U 1);
   rw [Pi.add_apply, plainPlus,show chartF (F+W)=oAdd (chartF F) (chartF W) from rfl,t.port,pX.port]; -- ABI
   have he(x:Views): TabX o M h (Z+V) x=TabX o M h Z x+TabX o M h V x:=by unfold TabX; rw [stream_plus h o M]; simp only [add_mul,mul_add]
   exact (((tab (o:=o) (h:=h) M Z).joinK (tab M V)).equal (Eventually.of_forall fun i=>(he i).symm)).unique (tab M _)
 change ((bm5 F).val+ (bm5 W).val)=_; rw [t.mixed,pX.mixed, landPlus M u v]
set_option maxHeartbeats 150000 in
lemma linearØ(z:ℂ) : MetaB o M (0:Waves) (fun _:Pane n=> hollow z) p h:=by
 let Q: InkD n:= fun _=>hollow z
 have hp:term Q=fun _=> z:= funext fun _=> hullB _
 have hd(x y: tangD n): ploy Q x y=0:=by rw [ploy_iter,hp, iteratedFDeriv_const_of_ne (by omega:(2:ℕ)≠0)]; rfl
 constructor
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hd ..).symm
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (hd ..).symm
 · rw [hol_l]; let T:= (0:Op (Single n)); have he:TabX o M h T=fun _=>0:= by funext i; simp [T,TabX,streamF,hill_Z]
   exact ((tab M T|>.equal (Eventually.of_forall fun i=>congrFun he i)).unique (AptK.const 0)).symm
 apply ContinuousLinearMap.ext; intro i; let v:=sectorJ (orbitPH (hollow z)) M o h; exact (show HasDerivAt (fun _:ℝ=>v) 0 0 from hasDerivAt_const 0 v).unique (landR M (o:=o) (fees_Z h o z) i) -- tune binder
end Layout
end Lenten
end YM.CF.TableF
end
