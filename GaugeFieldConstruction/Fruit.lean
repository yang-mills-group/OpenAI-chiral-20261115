import GaugeFieldConstruction.Freckle
import GaugeFieldConstruction.Fresco
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option maxRecDepth 4600
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
-- combinator prices
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open Phys
abbrev sunX(x:FactIx):=rayK x.1 x.2
local notation "sun" => J Spair
def heelY : ↥P03→ₗ[ℂ] sun:= goldΦ.comp P03.subtype
def heelA (x:FactIx):P14→ₗ[ℂ] sun:= heelC x • ((sunX x).comp (heelY.comp (μ₁ x)))
def heelP(x y:FactIx):P25→ₗ[ℂ] sun:= (sunX x).comp ((sunX y).comp ((heelC x*heelC y) • (heelY.comp (μ₂ x y))))
lemma hc_move(x y:Axis)(v: CJet)(b:Bool): Cder b x (Cder b y v)= Cder b y (Cder b x v):=Row.commuting (Row.skin b) (fun (i:Row.Pol)=>i.val.mom x) (fun (i:Row.Pol)=>i.val.mom y) (fun i=>(Chart.fermi i.val b).frequency x) (fun i=>(Chart.fermi i.val b).frequency y) _ -- tune
lemma piv_move(x y:Axis)(b:Bool)(m:J Mode): stride b x (stride b y m)=stride b y (stride b x m):=by
 let V:=stride b; have h: (V x).comp (V y)=(V y).comp (V x):= crossing fun i j=> by simp only [V, LinearMap.comp_apply,Phys.stride,Cauchy.first]; rw [hc_move]
 exact LinearMap.congr_fun h m
lemma payX(i j:FactIx)(u:sun): sunX i (sunX j u)=sunX j (sunX i u):=by
 have he: (sunX i).comp (sunX j)=(sunX j).comp (sunX i):=by
    rcases i with ⟨b,i⟩; rcases j with ⟨c,j⟩; apply crossing; intro p x; simp only [sunX, rayK,LinearMap.comp_apply]; cases b<;> cases c <;> simp only [↓reduceIte,Bool.false_eq_true,Cauchy.first,Cauchy.second]; all_goals rw [piv_move] -- tune
 exact LinearMap.congr_fun he u
lemma peak_M(x y:FactIx)(p:P25):heelP x y p= heelP y x p:=by
 rw [heelP,heelP]; let a:=heelC x*heelC y; let q:=heelY (μ₂ x y p); simp only [LinearMap.comp_apply,LinearMap.smul_apply]; rw [mul_comm (heelC x),show μ₂ x y p=μ₂ y x p from Subtype.ext (p.property _ _).2,payX]
def μPhi4: P14 →ₗ[ℂ] sun:=∑ i:FactIx, heelA i
def μPhi5: P25→ₗ[ℂ] sun:= (1/2:ℂ) • ∑ i:FactIx,∑ j:FactIx,heelP i j
lemma loam (p:P14): μPhi4 p=InPhi false p.val+InPhi true p.val:=by
 rw [μPhi4,Fintype.sum_prod_type,Fintype.sum_bool,add_comm,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.sum_apply] -- tune add_comm swapped? use trace_state
 apply congrArg₂ (·+·) <;> refine sum_congr rfl ?_
 · intro i _; unfold heelA FacV; simp only [LinearMap.comp_apply, LinearMap.smul_apply]; apply congrArg (axisCost _ • ·); apply congrArg (rayK _ _); try rfl
 intro i _; unfold heelA FacV; simp only [LinearMap.comp_apply,LinearMap.smul_apply]; apply congrArg (axisCost _ • ·); apply congrArg (rayK _ _); try rfl
lemma payΩ (a b:Bool)(x y:Axis)(p:P25): heelP (a,x) (b,y) p=R2Θ x y a b p.val:=by unfold R2Θ heelP; simp only [LinearMap.comp_apply,LinearMap.smul_apply]; apply congrArg (rayK _ _); apply congrArg (rayK _ _); apply congrArg ((axisCost a*axisCost b) • ·); try rfl
lemma magΩ (p:P25): μPhi5 p=InPowΦ false p.val+InPowΦ true p.val+ InSugar p.val:=by
 let F(a b:Bool):sun:= ∑ i:Axis,∑ j:Axis,heelP (a,i) (b,j) p
 have he(a b c:Bool)(i:Axis): (∑ j:FactIx,heelP (a,i) j p)= (∑ j:Axis,heelP (a,i) (true,j) p)+(∑ j:Axis,heelP (a,i) (false,j) p):=by rw [Fintype.sum_prod_type,Fintype.sum_bool] -- unused c
 have hp: μPhi5 p=(1/2:ℂ) • ((F true true+ F true false)+(F false true+F false false)):=by rw [μPhi5, LinearMap.smul_apply,LinearMap.sum_apply]; simp_rw [LinearMap.sum_apply, he _ true false]; rw [Fintype.sum_prod_type,Fintype.sum_bool,sum_add_distrib,sum_add_distrib]; try rfl
 have hv(a b): F a b = F b a:=by unfold F; rw [sum_comm]; exact sum_congr rfl (fun i _=>sum_congr rfl fun j _=> peak_M _ _ _)
 have hz(a:Bool) : (1/2:ℂ) • F a a = InPowΦ a p.val:=by unfold F InPowΦ; simp_rw [Finset.smul_sum,payΩ]
 have ht: F false true= InSugar p.val:= sum_congr rfl fun i _=>sum_congr rfl fun j _=> payΩ ..
 rw [hp,hv true false]; simp only [smul_add,hz]; -- prove abel half
 let Z:=F false true; have hx:(1/2:ℂ) • Z +(1/2:ℂ) • Z=InSugar p.val:=by rw [← add_smul,show (1/2:ℂ)+1/2=1 from by norm_num,one_smul]; exact ht
 rw [← hx]; abel -- tune Z.
lemma scaleG (x:FactIx)(p : P03): μPhi4 (spikeV x p) = sunX x (heelY p):=by
 rw [μPhi4,LinearMap.sum_apply,sum_eq_single x]; · simp only [heelA,LinearMap.smul_apply,LinearMap.comp_apply,spike_I,if_true,map_smul]; rw [smul_inv_smul₀ (heel_v _)]
 · intro v _ g; rw [heelA, LinearMap.smul_apply]; simp only [LinearMap.comp_apply, spike_I, if_neg (Ne.symm g),map_zero,smul_zero]
 simp
lemma scaleK (x y:FactIx)(p:P03) : μPhi5 (peakV x y p) = sunX x (sunX y (heelY p)):=by
 let Z:=sunX x (sunX y (heelY p)); have he(v w:FactIx): heelP v w (peakV x y p)=(if (x,y)=(v,w) then Z else 0)+(if (y,x)=(v,w) then Z else 0):=by
    simp only [heelP,LinearMap.comp_apply,LinearMap.smul_apply,peak_I,map_add,smul_add]; apply congrArg₂ (·+·)
    · split_ifs with q
      · obtain ⟨rfl,rfl⟩:= Prod.mk.inj q; rw [map_smul heelY,smul_inv_smul₀ (mul_ne_zero (heel_v _) (heel_v _))]
      simp only [map_zero,smul_zero]
    split_ifs with q
    · obtain ⟨rfl,rfl⟩:=Prod.mk.inj q; rw [map_smul heelY,mul_comm (heelC x) (heelC y),smul_inv_smul₀ (mul_ne_zero (heel_v _) (heel_v _)),payX]; try rfl
    simp only [map_zero,smul_zero]
 unfold μPhi5; simp_rw [LinearMap.smul_apply,LinearMap.sum_apply,he,sum_add_distrib];
 have hx(v w:FactIx): (∑ i:FactIx,∑ j:FactIx, if (v,w)=(i,j) then Z else 0)=Z:=by
    rw [sum_eq_single v]
    · rw [sum_eq_single w]
      · simp
      · intro i _ g; rw [if_neg (fun p=> g (Prod.mk.inj p).2.symm)]
      simp
    · intro i _ g; exact sum_eq_zero fun j _=> if_neg (fun p=>g (Prod.mk.inj p).1.symm)
    simp
 rw [hx,hx,smul_add,← add_smul,show (1/2:ℂ)+1/2=1 from by norm_num,one_smul]
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
