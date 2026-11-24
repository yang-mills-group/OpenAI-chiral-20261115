import GaugeFieldConstruction.Frango
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
namespace BluffV
open Cauchy
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open TableF.Lenten.Loden Phys
variable {b:Bool}
abbrev Fees(b:Bool):=GroundK b b
def wedgeJ (i:Axis)(v: ↥(Fees b)):↥P03:= by
 cases b; · exact ⟨ v.val* ΓV i,GroundV ▸ (boltL v.property (Γκ i))⟩ -- ▸ direction?
 exact ⟨ΓV i*v.val,GroundV ▸ (boltL (Γκ i) v.property)⟩
abbrev TipO(b:Bool)(i:Axis):FactIx:= (!b,i)
def taxW (v:↥(Fees b)):P14:=∑ i:Axis,spikeV (TipO b i) (wedgeJ i v)
def taxΘ(t:FactIx)(v:↥(Fees b)): P25:=∑ i:Axis,peakV t (TipO b i) (wedgeJ i v)
-- normalized coefficient momentum
lemma tivCost(b:Bool): (axisCost b)⁻¹=if b then Complex.I / 2 else -(Complex.I/2):=by
 have ht: axisCost b≠0:=heel_v (b,0); have he(z:ℂ)(p:axisCost b*z=1): (axisCost b)⁻¹=z:=by
    calc (axisCost b)⁻¹= (axisCost b)⁻¹ * (axisCost b*z) := by rw [p,mul_one]
         _= _ := by rw [← mul_assoc,inv_mul_cancel₀ ht, one_mul]
 cases b <;> apply he <;> simp [axisCost] <;> ring_nf <;> simp -- tune
lemma tips_pay (a:FactIx)(V:P03)(x:Views) : (spikeV a V).val x= (((tipK a x: ℝ):ℂ)*(heelC a)⁻¹) • V.val:=by unfold spikeV; change (_:ℝ) • _=( _*_) • V.val; rw [← Complex.coe_smul, mul_smul]; try rfl
lemma slowκ (i:FactIx)(x y:Views)(j:FactIx)(q:P03): (peakV i j q).val x y= ((tipK i x:ℂ)*(heelC i)⁻¹) • ((spikeV j q).val y)+((tipK i y:ℂ)*(heelC i)⁻¹) • ((spikeV j q).val x):=by
 rw [soldΦ,tips_pay,tips_pay]; simp only [Submodule.coe_smul,← Complex.coe_smul,smul_smul, mul_inv]; apply congrArg₂ (·+·); all_goals apply congrArg (fun v:ℂ=> v • _); ring
lemma ascentR (v:Fees false)(x:Views):(taxW v).val x=v.val*uroS x.2:=by
 rw [taxW, Submodule.coe_sum, ContinuousLinearMap.sum_apply,GammaS]
 simp_rw [Matrix.mul_smul,Matrix.mul_sum, smul_sum]; apply sum_congr rfl; intro i _; rw [tips_pay]; let X:=TipO false i; rw [show (heelC X)⁻¹=Complex.I/2 from tivCost true, mul_smul]; change ((tipK X x:ℂ) • ((Complex.I/2) • (v.val*ΓV i)))=_; rw [smul_comm, Complex.coe_smul, Matrix.mul_smul]; try rfl
lemma ascentL(v:Fees true)(x:Views): (taxW v).val x=(-uroS x.1)*v.val:=by
 rw [taxW,Submodule.coe_sum,ContinuousLinearMap.sum_apply, GammaS]; rw [← neg_smul]; simp_rw [Matrix.smul_mul,Matrix.sum_mul, smul_sum]; apply sum_congr rfl; intro i _; rw [tips_pay]; let X:=TipO true i; rw [show (heelC X)⁻¹= -(Complex.I/2) from tivCost false,mul_smul]; change (tipK X x:ℂ) • (-(Complex.I/2) • ((ΓV i)*v.val))=_; rw [smul_comm,Complex.coe_smul, Matrix.smul_mul]; try rfl -- tune neg_smul
lemma sprint_L1 (u:Fees true)(i:FactIx)(x:Views): (taxΘ i u).val x x= let Y:= ((tipK i x:ℂ)*(heelC i)⁻¹) • u.val; -uroS x.1 *Y+ -uroS x.1 *Y:=by
 let K:Pal:= -uroS x.1; let V:ℂ:= (tipK i x:ℂ)*(heelC i)⁻¹; change _=K*(V • u.val)+ K*(V • u.val); rw [Matrix.mul_smul]; rw [← show (taxW u).val x=K*_ from ascentL u x]; simp_rw [taxW,taxΘ, Submodule.coe_sum,ContinuousLinearMap.sum_apply,slowκ,smul_sum, ← sum_add_distrib]; rfl -- tune slowκ x used?
lemma sprint_R1(u:Fees false)(i:FactIx)(x:Views): (taxΘ i u).val x x= let Y:= ((tipK i x:ℂ)*(heelC i)⁻¹) • u.val; Y*uroS x.2 +Y*uroS x.2:=by
 let K:Pal:=uroS x.2; let V:ℂ:=(tipK i x:ℂ)*(heelC i)⁻¹; change _=(V • u.val)*K+(V • u.val)*K; rw [Matrix.smul_mul, ← show (taxW u).val x= _*K from ascentR u x]; simp_rw [taxW,taxΘ,Submodule.coe_sum,ContinuousLinearMap.sum_apply,slowκ, smul_sum, ←sum_add_distrib]; rfl -- tune
private lemma do_s (b:Bool)(a:Fees b)(i:FactIx):∃ W:PalOne, Oneκ b W∧ W.1=0∧∀ x:Views, W.2.1 x= ((tipK i x:ℂ)*(heelC i)⁻¹) • a.val:=by
 let y(x:Views):=(tipK i x:ℂ)*(heelC i)⁻¹; let Z:OneF Views Pal:=(tipK i).smulRight ((heelC i)⁻¹ • a.val); let W:PalOne:=(0,Z,0)
 have he(x): W.2.1 x= y x • a.val:=by change (tipK i x:ℝ) • ((heelC i)⁻¹ • a.val)=_; rw [← Complex.coe_smul]; exact (mul_smul ..).symm
 refine ⟨W,⟨nilκ,fun i=>?_⟩,rfl,he⟩; rw [he]; exact Qsm (SootΘ a) _
abbrev SuiteF(a:P03)(b:P14)(c:P25):Waves:= (a,(0,b),0,c,0)
lemma pleftW (W:↥(Fees b)): PH15 b (SuiteF 0 (taxW W) 0) (W.val,0,0):=by
 cases b
 · exact ⟨rfl,rfl,rfl, fun i=> ⟨rfl,ascentR W i, by change (0:Pal)=0*_+ 0*_; rw [zero_mul,add_zero]⟩⟩ -- one rw
 exact ⟨rfl,rfl,rfl, fun i=>⟨rfl,ascentL W i, by change (0:Pal)=_*0+_*0; rw [mul_zero,add_zero]⟩⟩
lemma pleftX(W:↥(Fees b))(i:FactIx): ∃ p:PalOne,Oneκ b p∧ PH15 b (SuiteF 0 0 (taxΘ i W)) p:=by
 obtain ⟨K,u,c,h⟩:= do_s b W i; refine ⟨K,u,?_⟩; cases b
 · refine ⟨rfl,rfl,rfl, fun x=>⟨rfl,?_,?_⟩⟩
   · rw [c,zero_mul]; rfl
   rw [h]; exact sprint_R1 .. -- tune he unification
 refine ⟨rfl,rfl,rfl, fun x=> ⟨rfl,?_,?_⟩⟩
 · rw [c,mul_zero]; rfl
 rw [h]; exact sprint_L1 ..
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
