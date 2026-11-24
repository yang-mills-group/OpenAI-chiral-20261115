import GaugeFieldConstruction.Apoala
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
abbrev Twing (b:Bool)(i:Axis):Views:= if b then (0,Pi.single i 1) else (Pi.single i 1,0)
abbrev axisCost (b:Bool):ℂ:=if b then -2*Complex.I else 2*Complex.I
abbrev wing (i:ArcK x)(k:Axis):ℝ:= ((nodeC i.1.val-x) k:ℤ)
lemma pointed (v:Cover)(d:Axis): rom v (Pi.single d 1)= (v d:ℝ):= by simp [rom_p,Pi.single_apply];
include w
lemma dockP (i j:ArcK x)(b:Bool)(k:Axis):let Y:=if b then wing x j k else wing x i k
 axisCost b * (Complex.I * (KnotΛ (n:=n) x i j (Twing b k):ℂ)) = ↑Y:=by
 intro Y
 have ht(i:ArcK x): pointF (Θk n x) (wrap n i.1.val) (Pi.single k 1)=(1/2)*wing x i k:=by
    let v:= i.1.val; change (1/2:ℝ) * rom (stem (Θk n x) (node _)) _ = _; rw [node_of, penC (x:=x) (show 24<n.val by omega) (nodeC v) ((ridge_spec v).1 i.1.property), pointed] -- tune cT
 cases b; · change 2*Complex.I*(Complex.I* (( -(pointF (Θk n x) (wrap n i.1.val) (Pi.single k 1))+pointF (Θk n x) (wrap n j.1.val) 0:ℝ):ℂ))=(wing x i k:ℂ); rw [ht,map_zero]; push_cast; simp; ring_nf; simp; ring
 change (-2:ℂ)*Complex.I*(Complex.I *((-(pointF (Θk n x) (wrap n i.1.val) 0)+ pointF (Θk n x) (wrap n j.1.val) (Pi.single k 1):ℝ):ℂ))=(wing x j k:ℂ); rw [map_zero,ht]; push_cast; simp; ring_nf; simp; ring
omit w
open StressFHeat
abbrev Rift (b:Bool)(r:ℕ)(i:ArcK x):= (YM.GaugeFieldConstruction.Wick.Yacht.tariff 1 r:ℂ) • boon (Phys.stride b) (primeF i.2) (Fuse x (Wry x i)) r
lemma Rift_0 (i:ArcK x)(b:Bool):Rift x b 0 i=primeF i.2:=by rw [Rift,B0]; simp [YM.GaugeFieldConstruction.Wick.Yacht.tariff]
-- `USD$​.Inc` moments. use unspecified SpecW mean.
def haze (p:Axis)(u:E4):ℝ:= 2*u p-1
def μCloud (p:Axis): ℂ:= ∫ v, (haze p v:ℂ)∂SpecW.μ
def pool (p q:Axis):ℂ:= ∫ v,(haze p v:ℂ)*(haze q v:ℂ)∂SpecW.μ
lemma haze_I (i:ArcK x)(a:E4)(p:Axis):billMark (off x) (off (Wry x i).1) 2 a p= wing x i p+ haze p a:=by
 change 2*((i.1.val p:ℝ)+a p)-(x p:ℝ)= ((((2:ℤ)*i.1.val p+1 - x p):ℤ):ℝ) + (2*a p-1); push_cast; ring
lemma HzS(i:Axis):Integrable (fun a:E4=>(haze i a:ℂ)) SpecW.μ:= span_c _ (by unfold haze; fun_prop)
lemma mulS(i j:Axis): Integrable (fun a:E4=>(haze i a:ℂ)*(haze j a:ℂ)) SpecW.μ:=span_c _ (by unfold haze; fun_prop)
lemma sellCloud (i:ArcK x)(p:Axis): ↑(meanH (Fuse x (Wry x i)) p) = (wing x i p:ℂ)+ μCloud p:=by
 let V:=Fuse x (Wry x i); rw [show ↑(meanH V p)= (∫ u:E4,(u p:ℂ) ∂V.μ) from (integral_ofReal (μ:=V.μ) (f:=fun u:E4=>u p)).symm]; unfold V Fuse diagram; rw [HopeC.rolled (v:= (show Continuous (fun x:E4=> (x p:ℂ)) from by fun_prop).continuousOn)]; simp_rw [haze_I, Complex.ofReal_add]; rw [integral_add (integrable_const _) (HzS p)]; unfold μCloud; simp -- tune haze_I reader
lemma sellPool (i:ArcK x)(p q:Axis): (∫ u:E4,(u p:ℂ)*(u q:ℂ)∂(Fuse x (Wry x i)).μ) =(wing x i p:ℂ)*(wing x i q:ℂ)+( (wing x i p:ℂ)*μCloud q+(wing x i q:ℂ)*μCloud p)+pool p q:=by
 let K(f:E4):=billMark (off x) (off i.1.val) 2 f; unfold Fuse diagram; rw [HopeC.rolled (v:=(show Continuous (fun x:E4=> (x p:ℂ)*(x q:ℂ)) from by fun_prop).continuousOn)]; simp_rw [haze_I, Complex.ofReal_add,add_mul,mul_add]; rw [integral_add (show Integrable (fun u:E4=> (wing x i p:ℂ)*(wing x i q:ℂ)+ (wing x i p:ℂ)*(haze q u:ℂ)) SpecW.μ from (integrable_const _).add ((HzS q).const_mul _)) (show Integrable (fun u:E4=> (haze p u:ℂ)*(wing x i q:ℂ)+(haze p u:ℂ)*(haze q u:ℂ)) SpecW.μ from ((HzS p).mul_const _).add (mulS p q))]; -- tune defeq
 rw [integral_add (integrable_const _) ((HzS q).const_mul _), integral_add ((HzS p).mul_const _) (mulS p q)]; simp_rw [integral_const_mul,integral_mul_const, integral_const]; unfold μCloud pool; simp only [probReal_univ,one_smul]; ring
lemma Rift_1 (i:ArcK x)(b:Bool): Rift x b 1 i= ∑ p:Axis, ((wing x i p:ℂ)+ μCloud p) • Phys.stride b p (primeF i.2):=by
 unfold Rift; rw [YM.GaugeFieldConstruction.Wick.Yacht.Vesper.boom, show (YM.GaugeFieldConstruction.Wick.Yacht.tariff 1 1:ℂ)=1 from by simp [YM.GaugeFieldConstruction.Wick.Yacht.tariff],one_smul]; simp_rw [sellCloud]
-- second
open StressFHeat
local notation "vC" a:max => (haze a)
def ρQ (i:ArcK x)(p q:Axis):ℂ:= ((1/2):ℂ)*((wing x i p:ℂ)*(wing x i q:ℂ)+( (wing x i p:ℂ)*μCloud q+(wing x i q:ℂ)*μCloud p)+pool p q)
private lemma boon2 {α:Type*}(X: StressFHeat.HopeC E4)(D:Axis→Module.End ℂ (Cauchy.J α))(A:Cauchy.J α):boon D A X 2=∑ i:Axis,∑ j:Axis, (∫ u:E4,(u i:ℂ)*(u j:ℂ)∂X.μ) • D i (D j A):=by
 let V:= Fin.consEquiv (fun _:Fin 2=>Axis); let P:= Fin.consEquiv (fun _:Fin 1=>Axis)
 let Uht (p:YM.GaugeFieldConstruction.Wick.Yacht.Φ 2):=(∫ u:E4, (YM.GaugeFieldConstruction.Wick.Yacht.dock u p:ℂ)∂X.μ) • YM.GaugeFieldConstruction.Wick.Yacht.tower D A 2 p; unfold boon; rw [←Equiv.sum_comp V Uht,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [← Equiv.sum_comp P (fun p:YM.GaugeFieldConstruction.Wick.Yacht.Φ 1=> Uht (V (i,p))), Fintype.sum_prod_type]; refine sum_congr rfl fun j _=>?_ ; rw [Fintype.sum_unique]; unfold Uht; simp only [YM.GaugeFieldConstruction.Wick.Yacht.tower,V,P,Fin.consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.cons_succ]; congr 1; simp [YM.GaugeFieldConstruction.Wick.Yacht.dock,YM.GaugeFieldConstruction.Wick.Yacht.Φ] -- tune `rw` rfl fail
lemma Rift_2 (i:ArcK x)(b:Bool): Rift x b 2 i=∑ p:Axis,∑ q:Axis,ρQ x i p q • (Phys.stride b p (Phys.stride b q (primeF i.2))):=by
 unfold Rift; rw [boon2, show (YM.GaugeFieldConstruction.Wick.Yacht.tariff 1 2:ℂ)=(1/2:ℂ) from (by norm_num [YM.GaugeFieldConstruction.Wick.Yacht.tariff])]; simp_rw [smul_sum, sellPool, smul_smul]; rfl -- tune
end YM.CF.XGarden.MastTin.ArtCart
end
