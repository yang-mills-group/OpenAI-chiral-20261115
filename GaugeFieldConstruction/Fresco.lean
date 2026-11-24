import GaugeFieldConstruction.Avatara
set_option autoImplicit false
set_option maxHeartbeats 250000
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
-- analytic prices from engineering dimensions
open Phys
abbrev FactIx := Bool × Axis
abbrev tipΘ (i:FactIx): Views:= Twing i.1 i.2
def tipK (i:FactIx):Views→L[ℝ]ℝ:= ((LinearMap.proj i.2).comp (if i.1 then LinearMap.snd ℝ (Axis→ℝ) (Axis→ℝ) else LinearMap.fst ℝ (Axis→ℝ) (Axis→ℝ))).toContinuousLinearMap
lemma tipR (i j:FactIx): tipK i (tipΘ j) = if i=j then 1 else 0:=by
 rcases i with ⟨i,a⟩; rcases j with ⟨b,c⟩; unfold tipK tipΘ; cases i <;> cases b <;> simp [Twing,Pi.single_apply,eq_comm] -- tune
lemma shellΦ(x:Views): x=∑ i:FactIx, tipK i x • tipΘ i:=by
 rw [Fintype.sum_prod_type,Fintype.sum_bool]; apply Prod.ext
 · rw [Prod.fst_add,Prod.fst_sum,Prod.fst_sum]; simp_rw [show ∀ i:Axis,(tipK (true,i) x • tipΘ (true,i)).1=0 from fun i=> (smul_zero _ : _), sum_const_zero,zero_add]; ext i; rw [Finset.sum_apply]; let w:=x.1; change _=∑ j:Axis, w j*(Pi.single j (1:ℝ):Axis→ℝ) i; simp [w,Pi.single_apply]
 rw [Prod.snd_add,Prod.snd_sum,Prod.snd_sum]; simp_rw [show ∀ i:Axis,(tipK (false,i) x • tipΘ (false,i)).2=0 from fun i=>(smul_zero _ : _), sum_const_zero, add_zero]; ext i; rw [Finset.sum_apply]; let w:=x.2; change _=∑ j:Axis,w j*(Pi.single j (1:ℝ):Axis→ℝ) i; simp [w,Pi.single_apply]
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
def μ₁(x:FactIx):P14 →ₗ[ℂ] P03 where
 toFun A:=⟨A.val (tipΘ x),A.property _⟩
 map_add' _ _:= rfl
 map_smul' _ _:= rfl
def μ₂(x y:FactIx): P25→ₗ[ℂ]P03 where
 toFun A:=⟨A.val (tipΘ x) (tipΘ y),(A.property _ _).1⟩
 map_add' _ _:= rfl
 map_smul' _ _:=rfl
lemma price1 (a b:P14)(u:∀ i, μ₁ i a=μ₁ i b): a=b:=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; rw [shellΦ i, map_sum,map_sum]; apply sum_congr rfl; intro j _; rw [map_smul,map_smul]; exact congrArg (tipK j i • ·) (congrArg (fun i:P03=> i.val) (u j))
lemma price2 (a b:P25)(u:∀ i j,μ₂ i j a=μ₂ i j b): a=b:=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; rw [shellΦ i,shellΦ j,map_sum a.val,map_sum b.val]; simp_rw [ContinuousLinearMap.sum_apply]; apply sum_congr rfl; intro k _; simp_rw [map_sum]; apply sum_congr rfl; intro p _; simp only [map_smul, ContinuousLinearMap.smul_apply]; rw [show a.val (tipΘ k) (tipΘ p)=b.val (tipΘ k) (tipΘ p) from congrArg (fun i:P03=>i.val) (u k p)] -- tune
abbrev heelC (i:FactIx): ℂ:= axisCost i.1
lemma heel_v (i:FactIx): heelC i ≠ 0:=by unfold heelC axisCost; split <;> norm_num
-- unnormalized.K use normalized ads
private lemma stepV (p:P03)(c:ℝ): SheetQ (c • p.val):= by rw [← Complex.coe_smul]; exact P03.smul_mem _ p.property
def spikeV (i:FactIx)(A:P03): P14:= by let X:= (heelC i)⁻¹ • A; exact ⟨(tipK i).smulRight X.val, fun v=> stepV X (tipK i v)⟩
lemma spike_I (A:P03)(i j:FactIx): μ₁ j (spikeV i A)= if (i=j) then (heelC i)⁻¹ • A else 0:=by
 apply Subtype.ext; change tipK i (tipΘ j) • (((heelC i)⁻¹ • A).val)=_; rw [tipR]; split_ifs <;> first|rw [one_smul]|rw [zero_smul]
 all_goals try rfl
def tipSpike(i:FactIx) : P03 →ₗ[ℂ]P14 where
 toFun:=spikeV i
 map_add' A B:= price1 _ _ fun j=>by rw [map_add,spike_I,spike_I,spike_I]; split_ifs <;> simp [smul_add]
 map_smul' a b:=price1 _ _ fun j=>by rw [map_smul,spike_I,spike_I]; split_ifs <;> simp [smul_comm a]
def peakV (i j:FactIx)(A:P03) : P25:=by
 let Z:= (heelC i*heelC j)⁻¹ • A; let Y:TwoF Views Pal:= (tipK i).smulRight ((tipK j).smulRight Z.val); have hv(a b:Views):SheetQ (Y a b):=by change SheetQ (tipK i a • (tipK j b • Z.val)); rw [smul_smul]; exact stepV ..
 exact ⟨Y+Y.flip, fun a b=> ⟨ SheetQ.plus (hv a b) (hv b a), add_comm ..⟩⟩
lemma soldΦ(i j:FactIx)(A:P03)(x y: Views):(peakV i j A).val x y= tipK i x • tipK j y • (((heelC i*heelC j)⁻¹ • A).val)+ tipK i y • tipK j x • (((heelC i*heelC j)⁻¹ • A).val):=rfl
lemma peak_I (A:P03)(i j x y:FactIx):μ₂ x y (peakV i j A)= ((if (i,j)=(x,y) then (heelC i*heelC j)⁻¹ • A else 0) + if (j,i)=(x,y) then (heelC i*heelC j)⁻¹ • A else 0):=by
 apply Subtype.ext; change (peakV i j A).val _ _=_; rw [soldΦ,tipR,tipR,tipR,tipR]; by_cases e:i=x<;> by_cases b:j=y<;> by_cases c:j=x<;>by_cases p:i=y<;> simp_all -- tune
lemma peak_H (A:P03)(i j:FactIx):peakV i j A= peakV j i A:=price2 _ _ fun x y=>by rw [peak_I,peak_I, mul_comm (heelC j) (heelC i), add_comm]
def tipPeak (i j:FactIx): P03 →ₗ[ℂ] P25 where
 toFun:=peakV i j
 map_add' A B:= price2 _ _ (fun x y=> by rw [map_add,peak_I,peak_I,peak_I]; split_ifs <;> simp [smul_add, add_add_add_comm]) -- tune
 map_smul' a b:=price2 _ _ (fun x y=> by rw [map_smul,peak_I,peak_I]; split_ifs <;> simp [smul_add,smul_comm a])
lemma spikeBus(A:P14): A=∑ i:FactIx,spikeV i (heelC i • μ₁ i A):=by
 apply price1; intro i; rw [map_sum]; simp_rw [spike_I]; rw [sum_ite_eq',if_pos (mem_univ _),inv_smul_smul₀ (heel_v i)] -- tune
lemma peakBus(A:P25):A=∑ i:FactIx×FactIx, (1/2:ℂ) • peakV i.1 i.2 ((heelC i.1*heelC i.2) • μ₂ i.1 i.2 A):=by
 apply price2; intro x y; have he: μ₂ y x A= μ₂ x y A:=Subtype.ext <| (A.property _ _).2
 rw [map_sum]; simp_rw [map_smul,peak_I, inv_smul_smul₀ (mul_ne_zero (heel_v _) (heel_v _)), Prod.eta, smul_add,sum_add_distrib];
 rw [sum_eq_single (x,y)]; swap; · intro i _ p; rw [if_neg p,smul_zero]
 swap; · simp
 rw [sum_eq_single (y,x)]; swap; · rintro ⟨i,j⟩ _ p; rw [if_neg (fun e=>p (Prod.ext (Prod.mk.inj e).2 (Prod.mk.inj e).1)),smul_zero]
 swap; · simp
 simp only [ite_true,he]; rw [← add_smul,show (1/2:ℂ)+1/2=1 from by norm_num,one_smul] -- tune
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
