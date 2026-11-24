import GaugeFieldConstruction.Emerick
import GaugeFieldConstruction.Fetewave
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
lemma rays_u(W: Waves)(c:ℂ)(u:20<n.val)(w:0<h)(P:p.power≤3)(L:p.order≤6): bushMoon M o p h (c • W)= c • bushMoon M o p h W:=by
 unfold bushMoon; rw [← show Ť n • (c • ∑ i:Sweep n,CurveS M o p h W i)=_ from (smul_comm ..)]; apply congrArg (Ť n • ·); rw [smul_sum]; apply sum_congr rfl; intro i _; rw [CurveS,payY_a,bush_m _ _ _ u w P L, born_P,warX, mul_inv_cancel,ride_one]
lemma rays_a (V W: Waves)(u:20<n.val)(t:0<h)(x:p.power≤3)(l:p.order ≤6) : bushMoon M o p h (V+W)=bushMoon M o p h V+bushMoon M o p h W:=by
 unfold bushMoon; rw [←smul_add,←sum_add_distrib]; apply congrArg (Ť n • ·); apply sum_congr rfl; intro i _; rw [CurveS,show Mason i⁻¹ (V+W)=Mason i⁻¹ V+Mason i⁻¹ W from sheen_plus ..,bush_a M _ _ u t x l,born_Z] -- tune
-- fixed side.Prop bas.
def Reifier : Side:=⟨600,by norm_num⟩
lemma liquid : 300 < Reifier.val:=by norm_num [Reifier]
variable (p h)
def BushRoot (M:Male)(p:BudgetPoint)(h:ℝ)(x:Cover)(W:Waves): Psu x 24:=Pvi Reifier x 24 (bushMoon M (wrap (More Reifier) x) p h W)
variable {p h}
def bush_ℓ (x:Cover)(w:0<h)(P:p.power≤3)(L:p.order≤6): Waves→ₗ[ℂ] Psu x 24 where
 toFun:= BushRoot M p h x
 map_add' i j:=by funext s v; unfold BushRoot Pvi; rw [rays_a M _ _ (by norm_num [Reifier]) w P L]; rw [Pi.add_apply,Pi.add_apply,mul_add]; rfl
 map_smul' i j:=by funext s v; unfold BushRoot Pvi; rw [rays_u M _ _ (by norm_num [Reifier]) w P L]; simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul]; rw [mul_left_comm]
-- specific A1.est.Full.C. Book q post. All p
lemma straight_a (V:Psu x d)(n:Side)(b:ℂ): pR n (b • V)=b • pR n V:=by
 funext i z; rw [cone_p,Pi.smul_apply, Pi.smul_apply,cone_p,smul_eq_mul,mul_sum]; apply sum_congr rfl; intro j _; split_ifs; exact mul_left_comm ..; exact (mul_zero b).symm
lemma root_T (h₁:1≤h)(x: Cover)(P:p.power ≤3)(L:p.order ≤6)(V:Waves): let T:= BushRoot M p h x V; let q:= morgue*‖V‖
 (∀ i,LocalOn (cartO x 24) (T i)∧ (T i≠0→ inkB i)) ∧
 (∀ K:Calibration, InTest K true (cartO x 28) false (John T K p.threshold) ∧ Afterglow.Tower.pay (John T K p.threshold) q ∧ ∀ m:Side,Buffered.covariant (John T K p.threshold m)) ∧
 (∀ (n:Side)(a:ℝ), 300<n.val → Portage (pR n T,0) (wrap (More n) x) p h a V M q 0):=by
 intro T q; let n:= Reifier; let W:=wrap (More n) x; let S:= bushMoon M W p h V; let g:=liquid; have hh:=zero_lt_one.trans_le h₁; obtain ⟨h0,hG,hT⟩:= ray_B (o:=W) M V g hh P L 1; change TrackD p (knotX x 24 n) h S q at h0; have he:24+6<n.val:=by unfold n; omega
 have hx(i:jungle x 24):LocalOn (cartO x 24) (T i):= pvi_U _ (by omega) (fun i=> (h0.choose_spec.1 i).1.2.2.1) i; have hy:Tuned S:=ray_V M _ (by unfold n; omega) hh P L;
 have Hq(m): portable (pR m T):=pR_smir he S h0 hG m
 refine ⟨fun i=> ⟨hx i, Tune_p _ hy i⟩, fun K=>⟨philosophy he _ h0 K hy,payable_k he _ h0 h₁ K,fun i=>all_cov T _ K _ (Hq _)⟩, fun m a r=>?_⟩
 let Y:= wrap (More m) x; have ht: TrackD p (Pach Y) h (pR m T) q:=Tock_C he (by omega) h0; have hp: pR n T=S:=pR_morn he _ h0; have hV: PressB p (Zhub W) (AlphaY (pR n T)) h (crestP*q):= by rw [hp]; exact sprig W h0 P L hG
 have hm: MetaB W M V (AlphaY (pR n T)) p h:= by rw [hp]; exact hT.port
 refine ⟨⟨ht,trace_Z⟩,⟨Hq _,fun i=>port_Z⟩, salon M liquid r T hx hV (sprig Y ht P L (Hq _)) V hm hh.le,?_⟩
 change lifeH (AlphaY (pR m T)) 1= _; rw [life_S r T, show T none (onC m 1)=_ from (show T none (onC m 1)=T none (onC Reifier 1) from hx _ _ _ fun i _ _=> by rw [onC_spec,onC_spec]; rfl),←life_S liquid T,show pR Reifier T=S from hp]; exact hT.post
variable (x)
lemma Μsend (s: Shape)(q:Bool)(t:0<h)(P:p.power≤3)(L:p.order≤6)(W: Waves) (m:Side): let V:= Levier.ray q s (N:=m); pR m (BushRoot M p h x (Mason V W))= Barber V (pR m (BushRoot M p h (s.motion x) W)):=by
 intro V; let n:= Reifier; let a:= Levier.ray q s (N:=n); let X:= wrap (More n) x; let y:= s.motion x; let Y:=wrap (More n) y; let F:= bushMoon M X p h (Mason V W); let G:= bushMoon M Y p h W; let he:= liquid; let A:= ray_B (o:=X) M (Mason V W) he t P L 1; let K:= ray_B (o:=Y) M W he t P L 1
 have hA: TrackD p (knotX x 24 n) h F (morgue*‖Mason V W‖):= A.1; have hG: TrackD p (knotX y 24 n) h G (morgue*‖W‖):=K.1;
 apply aboard_k (n:=n) s q (show 24<n.val from lt_trans (by omega) liquid) m (pvi_U _ (lt_trans (by omega) liquid) fun i=>(hG.choose_spec.1 i).1.2.2.1) (pvi_U _ (lt_trans (by omega) liquid) fun i=>(hA.choose_spec.1 i).1.2.2.1)
 change pR n (Pvi n x 24 F)=Barber a (pR n (Pvi n y 24 G)); rw [pR_morn (show 24+6<n.val from lt_trans (by omega) liquid) _ hA,pR_morn (lt_trans (by omega) liquid) _ hG]; symm
 have hx: sh a Y=X:=sector_o ..; have h: Mason a W=Mason V W:=rfl
 exact (ray_send p M a Y _ W).trans (by rw [hx,h]) -- unfold
end ArtCart
end MastTin
end YM.CF.XGarden
end
