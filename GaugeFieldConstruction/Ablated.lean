import GaugeFieldConstruction.Ontic
import GaugeFieldConstruction.Gateveil
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
open TableF.Axon Siete Lenten.ModuleB MultiNext.SignedSource Lyre Banjo Analysis
variable {c f:Side}{M:Male}{Z:Scree.Hub f}{P:BudgetPoint}{d b a C s h:ℝ}{r k m:ℕ}{g: Finset (Dwell f)→ℝ}{Q H:Op (Single f)}{X:SM f→ℝ}{p:BudgetPoint}
variable {G:Ratio c f}{σ U B:Bool→ℝ}{T:Script Male}{e:Odd G.count.val}{o:Skye.Seat f}
variable (α:Silks σ U B m)(u:3 ≤ m)(he:Use 4 G.count T)(v:100 < f.val)(dT:h≠0)
lemma ablat (i:BudgetPoint) (x:i.power=3)(o:Skye.Seat f)(M:Male)(K:Op (Single f))(Y:SM f→ℝ)(U:ℝ)(Q:∀ j, ‖K j.1 j.2‖ ≤ Y j)(v:h^2*WhX 3 Y o≤ U):CostOle (winJ o M h K) ≤ mintPay ((caboose*16)*U):=by
 apply costmint; apply le_trans (weights_n _ _) _; let L:=caboose*16; have ht:L≥ 0:=mul_nonneg cab_pos.le (by positivity); apply le_trans (b:= (caboose*16)*( h^2*WhX 3 Y o)) _ (mul_le_mul_of_nonneg_left v ht); rw [← Wh_charge i x, Finset.mul_sum]; apply sum_le_sum; intro j _; apply (mast_ticks o K h j).trans; let q:=tray j.1 j.2; let a:ℝ:=endL o q; have hA:1 ≤1+a:=le_add_of_nonneg_right (Nat.cast_nonneg _); let T':=(1+a)^3 * h^2; unfold tariff; rw [show (Haro.tray j.1 j.2).card=2 by simp [Haro.tray],x]; have hy:= Q j; change _≤ L*(Y j*T'); unfold L T'; have hv: (4*(1+a))^2=(16:ℝ)*(1+a)^2:=by ring
 calc
    _ = (caboose*16)* (‖K j.1 j.2‖*((1+a)^2*h^2)):=by change caboose*((4*(1+a))^2*(h^2*_))=_; ring
    _ ≤ _ :=by gcongr; exact (norm_nonneg _).trans hy; omega -- tune
include α
lemma icings (i:ℕ)(G:Ratio c f):0 ≤ ScoreBB B G i:=by
    unfold ScoreBB wageX; have he:=α.real; have hp:= Thorn.wool_pos G.count []; have ht:= α_pos G.count; have hc:0≤γE_0 G B:=mul_nonneg (zero_le_one.trans (he false)) hp; have hx:0 ≤ γE_1 G B:=mul_nonneg (zero_le_one.trans (he true)) hp; positivity
include u he v dT
abbrev prices0 (G:Ratio c f)(B:Bool→ℝ) (i t:ℝ):ℝ:= mintPay ((caboose*16)* (i*ScoreBB B G 0*t))
include e
lemma milage (p:Rode o a X Q) (hx:0 ≤a)(hC:∀ i,0 ≤X i)(H:h^2*WhX 3 X o≤d)(P:BudgetPoint)(q:P.power=3)(M' M:Male): CostOle (winJ (downT G o) M' h (totF 4 G e T M Q)) ≤ prices0 G B a d :=by
 let X':=Γrep G M o X 0; let X₁(j):= a*X' j; have hv:= pull_one α u he v dT (e:=e) p (r:=0) (by decide) (M:=M) (show quote_B M Q _ _ 0 from ⟨fun h=>by omega,fun h=>by omega,fun h=>by omega⟩) hx hC; apply ablat P q _ _ _ X₁ _ hv; rw [show WhX 3 X₁ (downT G o)= a*WhX 3 X' (downT G o) from ?_]; swap; · unfold WhX X₁; rw [Finset.mul_sum]; exact sum_congr rfl fun i _=>by ring
 have hz:= MajorV α u e hC (r:=0) (by omega) o M; let L:=ScoreBB B G 0
 calc
 _ ≤ h^2 * (a*(L * WhX 3 X o)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz.2 hx) (sq_nonneg _)
 _= a*L*(h^2*WhX 3 X o):=by ring
 _≤ _:= mul_le_mul_of_nonneg_left H (mul_nonneg hx (icings α _ _))
omit e u he v dT α
lemma mintOrder {x y:ℝ}(h:x≤y):mintPay x≤ mintPay y:=by
 unfold mintPay; apply mul_le_mul_of_nonneg_left; rotate_left; · exact mul_nonneg (by positivity) (Ole_non _)
 apply mul_le_mul_of_nonneg_left; rotate_left; · exact mul_nonneg (by positivity) (BP_u _)
 exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity)) (mul_nonneg (mul_nonneg (by positivity) (BP_u _)) (Ole_non _))
lemma labelPos : 0 ≤ labelB:=by unfold labelB; have h:0 ≤ coinV 1:= c_nn _ _ zero_le_one; positivity -- potential norm opacity
include e α u he v dT
abbrev OriginPrice (c f:Side)(G:Ratio c f)(B:Bool→ℝ)(r:ℕ)(t D:ℝ):ℝ:= mintPay ((labelB*t*(ScoreBB B G r)*D)/(c.val:ℝ)) -- overcomp cost no factor vs true (10^3) already in Score
lemma ShotX (p:Rode o a X Q)(t:quote_B M Q o h r)(hx:0 ≤a)(hC:∀ i,0 ≤X i)(H:h^2*WhX 3 X o≤d)(v':r ≤2)(M':Male): ∃ V:PalOne, CostOle (winJ (downT G o) M' h (totF 4 G e T M Q)-V)≤ OriginPrice c f G B r a d∧ ∀ j≤r,∀ x:Views, PartT V j x=αN G.count^(3+j) • PartT (winJ o M h Q) j x:=by
 let K:=fun i=>a*X i; have he0:=p.sent; have he1:=p.cost
 obtain ⟨V,Z,g,b⟩:= (SpunE α u e he p.sent v t dT (show ∀ i,‖Q i.1 i.2‖ ≤ K i from p.cost) (by omega)).2.2.2 v' M'
 refine ⟨V,g.trans (mintOrder ?_),b⟩
 have ht:= sell_w (o:=o) (u:=K) (fun i=> mul_nonneg hx (hC i)); have hb:= show WhX 3 K o=a*WhX 3 X o from (by unfold WhX K; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; ring)
 have he:Lenten.caboose≥0:=cab_pos.le -- tune names
 unfold inkPay; apply div_le_div_of_nonneg_right _ (by positivity)
 let S:= ScoreBB B G r; have hz:0≤ S:= icings α _ _
 let Y:ℝ:= wageX G B r; have hY:0 ≤ Y:=nonneg_of_mul_nonneg_right hz (show 0 < (24:ℝ)^3 *10^3 from by positivity)
 apply le_trans (b:=labelB*h^2*(Y*((10:ℝ)^3*(a*WhX 3 X o)))) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ht.trans_eq (congrArg _ hb)) hY) (mul_nonneg labelPos (sq_nonneg _)))
 have hp:0 ≤WhX 3 X o:=sum_nonneg fun i _=> mul_nonneg (by positivity) (hC i)
 calc
 _= labelB*a*(10^3*Y)*(h^2*WhX 3 X o):=by ring
 _≤ labelB*a*(10^3*Y)*d:=mul_le_mul_of_nonneg_left H (by have h:=labelPos; positivity)
 _≤ _:=by change labelB*a*(10^3*Y)*d≤labelB*a*((24:ℝ)^3*10^3*Y)*d; have ht:0 ≤d:=(mul_nonneg (sq_nonneg _) hp).trans H; gcongr <;> first| apply mul_nonneg labelPos hx | norm_num
-- subtract forms
omit e α u he v dT
lemma winP_sub(o:Skye.Seat f)(M:Male)(h:ℝ)(U V:Op (Single f)):winJ o M h (U-V)= winJ o M h U-winJ o M h V:=by exact sub_eq_of_eq_add (a:=winJ o M h U) (b:=winJ o M h V) (c:=winJ o M h (U-V)) ((congrArg (fun x=>winJ o M h x) (sub_add_cancel U V).symm).trans (winP_add ..)) |>.symm
lemma tot_sub(G:Ratio c f)(e:Odd G.count.val) (T:Script Male)(M:Male)(U V:Op (Single f)): totF 4 G e T M (U-V)= totF 4 G e T M U- totF 4 G e T M V:=by unfold totF; rw [Matrix.mul_sub,Matrix.sub_mul]
lemma mT_non (C:ℝ)(v:0≤C):0≤ mintPay C:=by have h:=mintOrder v; refine le_trans ?_ h; simp [mintPay]
end Boom
end YM.CF.TableF
end
