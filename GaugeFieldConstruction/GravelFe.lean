import GaugeFieldConstruction.MeterΛ
import GaugeFieldConstruction.GlitchFe
import GaugeFieldConstruction.PartyD
set_option autoImplicit false
set_option maxHeartbeats 280000
set_option maxRecDepth 5500
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
open BrentFe
open YM.GaugeFieldConstruction Flavor -- potential namespace collision
open BluffV BluffV.Fables
variable (g:Flavor)
abbrev δΔFe:UNI SU.Slot:=Ferr (chipUFe g)
lemma chip_realFe(h:GaugeFieldConstruction.proper3):cc (chipFe h)=chipFe h:=by ext a b; rw [cc_apply]; unfold chipFe; simp
lemma fob_fe : cc (δΔFe g).val=(δΔFe g).val:=by
 ext i j; rw [cc_apply]; change star (player (ΨsFe (chipUFe g)) i j)= _; change _=player (ΨsFe (chipUFe g)) i j; rw [player_v]; split_ifs; swap; · exact star_zero _
 exact Matrix.ext_iff.mpr (chip_realFe (g (tagged i.2))) i.1 j.1
lemma seal_fe(I:Type*)[Fintype I][DecidableEq I]:cc (RiseFe I (chipUFe g)).val=(RiseFe I (chipUFe g)).val:=by
 change cc ((1:Op I)⊗ₖ (δΔFe g).val)=_; rw [op_cc_kron,fob_fe,cc_one]; rfl
lemma radixFe(U:UNI SpinIdx)(b:Bool):twoU U b*palFe (chipUFe g)=palFe (chipUFe g)*twoU U b:=by
 apply Subtype.ext; change (U.val⊗ₖ (1:Op SU.Slot))*TkFe _ _=TkFe _ _*(U.val⊗ₖ (1:Op SU.Slot)); unfold TkFe; rw [op_kron_mul,op_kron_mul]; simp
lemma sector_fe(R:Signed)(b:Bool)(p:Pal): WingL R b (ageFe (chipUFe g) p)=ageFe (chipUFe g) (WingL R b p):=by
 let T:=R⁻¹; let X:= palFe (chipUFe g); let k:=detX T; let U:=spinU b T
 have he:sings b (twoU U b) (twist X p)=twist X (sings b (twoU U b) p):=by
    have hx:windX b (twist X p)=twist X (windX b p):=by
       cases b; · rfl
       change cc _=twist X _; rw [cc_twist,show ccU X=X from Subtype.ext (seal_fe ..)]; rfl
    rw [singT,hx,← Fock.twin, radixFe, Fock.twin, singT]
 change Thera.jazz k (sings b (twoU U b) (twist X p))=twist X (Thera.jazz k _); rw [he]; cases k<;>simp [Thera.jazz]<;>first|rfl|(change _=(twist X) (star ((twist (twoU U b)) (windX b p))); exact (map_star (twist X) _).symm)
lemma pressSpinFe (R:Signed)(b:Bool)(W: Waves):SpinFe (chipUFe g) (pressA R b W)=pressA R b (SpinFe (chipUFe g) W):=by
 let V:=pressA R b W; let H:=SpinFe (chipUFe g) W; let Z:= pressA R b H
 apply econUni
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; change (bF4 (pressA R b W)).val i j=(bF4 (pressA R b H)).val i j; rw [paintL_R,paintL_R]; rfl
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; exact (paintR_D ..).trans (paintR_D R b H i j).symm -- tune
 · apply grip_H; intro i j; apply congrArg (skim_L false true); change ageFe (chipUFe g) ((bm5 _).val (hem i j))=(bm5 (pressA R b H)).val (hem i j); rw [wind_V,wind_V,← sector_fe]; rfl
 apply Prod.ext _ (Prod.ext (ContinuousLinearMap.ext fun i=>?_) (dual_uni _ _ fun i=>?_)); · change ageFe _ (bV0 _).val=(bV0 Z).val; rw [κ0,show (bV0 Z).val= _ from κ0 ..,←sector_fe]; rfl
 · change ageFe _ ((bV1 V).val i)=(bV1 Z).val i; rw [show (bV1 Z).val _= _ from κ1 .., show (bV1 V).val i= _ from κ1 .., ←sector_fe]; rfl
 change ageFe _ ((bV2 V).val i i)=(bV2 Z).val i i; rw [show (bV2 Z).val i i= _ from κ2 .., show (bV2 V).val i i=_ from κ2 ..,←sector_fe]; rfl
lemma MasonFe(r:Sweep n)(W:Waves):Mason r (SpinFe (chipUFe g) W)=SpinFe (chipUFe g) (Mason r W):=by
 have h(X): Mason r X=pressA r.s⁻¹ r.charge X := by unfold Mason pressA; rw [inv_inv]
 rw [h,h,pressSpinFe]

lemma whitenFe (b:Bool): whiten b (TVfe n g)=TVfe n g:=by cases b; exact rfl; exact Subtype.ext (seal_fe ..)
lemma relaunchFe(r:Sweep n) : launchZ r*TVfe n g=TVfe n g*launchZ r:=by
 apply Subtype.ext; let S:=castX r; let X:=spinU r.charge r.s; let V:= mealU S X inert n; let Y:=coΛ n (chipUFe g)
 change love n V.val*(TVfe n g).val=(TVfe n g).val*love n V.val; rw [FieldPay,←map_mul,←map_mul]; apply congrArg
 change (jump _ (fun i:Site n=> (milU S X inert i).val))* (jump _ (fun _=> TkFe SpinIdx (δΔFe g).val))= _
 change _= (jump (Equiv.refl (Site n)) (fun _=> TkFe SpinIdx (δΔFe g).val))*(jump (Tofu S n) (fun i:Site n=> (milU S X inert i).val)); rw [jump_mul,jump_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; ext1 i
 change (S.payA i • (twoU X false).val)*(palFe (chipUFe g)).val=(palFe _).val*(S.payA i • (twoU X false).val); rw [Matrix.smul_mul,Matrix.mul_smul]; exact congrArg _ (show (twoU _ _).val*_ = _ * _ from congrArg Subtype.val (radixFe g X false))

-- Mark costs
abbrev TribePFe (A:Paper n): Paper n:= CardCraft (TVfe n g) false false id A
lemma Signet_barFe(r:Sweep n)(A: Paper n): Barber r (TribePFe g A)=TribePFe g (Barber r A):=by
 funext i U; let X:=flashA r⁻¹ U; let P:=αLines A X; change steerZ (launchZ r) _ _ (steerZ (TVfe n g) false false P) i = steerZ _ _ _ (steerZ (launchZ r) _ _ P) i; rw [convoyZ,convoyZ,whitenFe, relaunchFe]; simp only [Bool.false_xor,Bool.xor_false]; rfl
end YM.CF.XGarden.MastTin.ArtCart
end
