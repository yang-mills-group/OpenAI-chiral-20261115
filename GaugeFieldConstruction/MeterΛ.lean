import GaugeFieldConstruction.Pyrus
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
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
-- plen capital: anchor unweighted.White v
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
local instance : AddCommGroup ↥G3:= PackG.G.toAddCommGroup
local instance : Module ℂ ↥G3:= PackG.S.toModule
open Phys Row TableF.Lenten.Loden
open Matter (FlavorIndex)
open Raw Calibration
local instance : AddCommGroup Gκ:= PackH.G.toAddCommGroup
local instance : Module ℂ Gκ:= PackH.S.toModule
-- explicit comparison at transpositions; pin calculation as in Eager combo
open Matrix Scroll Mir
set_option maxHeartbeats 120000 in
lemma swap_stamp (i j: Axis)(h:i≠j): detX (unsigned (Equiv.swap i j))=true:=by
 let x:=gammaOp i - gammaOp j; let y:= x*grading; let c:= (Real.sqrt 2)⁻¹; have he:Commute y (1:Op SpinIdx):=Commute.one_right _
 have hs:c*c=(1/2:ℝ):=by rw [show c*c=(Real.sqrt 2*Real.sqrt 2)⁻¹ by rw [_root_.mul_inv_rev]]; rw [Real.mul_self_sqrt (by norm_num)]; simp
 have hx:x*x=1+(1:Op SpinIdx):=by unfold x; rw [sub_mul,mul_sub,mul_sub,gammaOne,gammaOne,gammaSwap i j h]; abel
 have hv:star x=x:= by unfold x; rw [star_sub,(gammaAdj i).star_eq,(gammaAdj j).star_eq]
 have hp: y*star y=1+(1:Op SpinIdx):=by unfold y; rw [star_mul,hv,gradingAdj.star_eq,←mul_assoc _ _ x,mul_assoc x, gradingOne,mul_one,hx]
 let U:UNI SpinIdx:=⟨c • y, Matrix.mem_unitaryGroup_iff.mpr (by change _ * star _= _; rw [star_smul,star_trivial, Matrix.smul_mul,Matrix.mul_smul, smul_smul,hp,smul_add,←add_smul,hs]; norm_num)⟩
 have hk(d):y*gammaOp d= -(x*gammaOp d*grading):=by unfold y; rw [mul_assoc,gradingSwap,mul_neg,←mul_assoc]
 apply mono_d _ false _ U; refine ⟨fun a=>twist_comm _ _ _ ?_,twist_comm _ _ _ ?_,?_⟩
 · change (c • y)*_=gammaOp a * _; rw [show U.val=c • y from rfl, Matrix.smul_mul, Matrix.mul_smul]; congr 1; change y*gammaOp ((Equiv.swap i j) a)= _; rw [hk]; by_cases t:a=i
   · subst a; rw [Equiv.swap_apply_left]; unfold y; rw [← mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show gammaOp i * gammaOp j-1= -(1-gammaOp i*gammaOp j) by abel,neg_mul,neg_neg]
   by_cases p:a=j
   · subst a; rw [Equiv.swap_apply_right]; unfold y; rw [←mul_assoc]; unfold x; rw [sub_mul,gammaOne,mul_sub,gammaOne, show 1-gammaOp j*gammaOp i= -(gammaOp j*gammaOp i-1) by abel,neg_mul,neg_neg]
   rw [Equiv.swap_apply_of_ne_of_ne t p]; unfold y; rw [←mul_assoc, show x*gammaOp a= -(gammaOp a*x) by unfold x; rw [sub_mul,mul_sub,gammaSwap i a (Ne.symm t),gammaSwap j a (Ne.symm p)]; abel,neg_mul,neg_neg]
 · change (c • y)*grading= -grading*(c • y); rw [Matrix.smul_mul, Matrix.mul_smul]; congr 1; unfold y; rw [← mul_assoc (-grading), neg_mul]; congr 1; unfold x; rw [sub_mul,mul_sub,gradingSwap,gradingSwap]; abel
 change (c • y)*_=spinJ*cc (c • y); rw [Matrix.smul_mul,cc_rsmul,Matrix.mul_smul]; congr 1; unfold y; rw [mul_assoc x,spinJ_grading,cc_mul,←mul_assoc spinJ,←mul_assoc x]; congr 1; unfold x; rw [sub_mul,cc_sub,mul_sub,spinJ_inter,spinJ_inter]
lemma met_stamp (R:Signed): detX R=signBit R:=by
 let T:(s: Signed)→Prop:=fun t=> detX t=signBit t; have ht(i j:Signed)(v:T i)(p:T j):T (i*j):=by unfold T; rw [det_p,signBit_mul,v,p] -- tune
 refine signed_induction (P:=T) (fun p=>?_) (fun i=> (det_t i).trans (signBit_mirror i).symm) ht R
 refine Equiv.Perm.swap_induction_on p ?_ ?_
 · exact (show T 1 from det_i.trans signBit_one.symm)
 intro S i j v p; rw [unsigned_mul]; apply ht _ _ _ p; exact (swap_stamp _ _ v).trans (signBit_swap _ _ v).symm
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
