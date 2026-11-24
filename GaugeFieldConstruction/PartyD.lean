import GaugeFieldConstruction.Váls
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
namespace Fables
open Conj
variable (R: Signed)(b:Bool)
lemma paintL_R (p: Waves)(f g:Gem): let v:=pressA R b p; (bF4 v).val f g=Dye R⁻¹ b ((bF4 p).val (gird R f) (gird R g)):=by intro v; rw [←(sheen_v R⁻¹ b p).life,gird_flip,gird_flip]; try rfl
lemma paintR_D (p:Waves)(i:Gem)(j:Sut):bF5 (pressA R b p) i j= Dye R⁻¹ b (bF5 p (gird R i) (girdS R j)):=by rw [←(sheen_v ..).bond,gird_flip,girdS_rev]; try rfl
lemma dye_real (R:Signed)(p q:ℂ)(u:star p=p) (h:p=q): Dye R b p=q:=by
 unfold Dye; rw [castT]; unfold cSignX; split<;> simp_all -- tune
-- k3 ordered emitter maps
abbrev γQ (i:G4):G3:= k3 i.val.1 i.val.2
abbrev γ5 (i:G5): Gκ:= k5 i.1 (i.2.2,i.2.1)
lemma span_w (A:G3): A ∈ Submodule.span ℂ (Set.range γQ):=by
 let Y:=Submodule.span ℂ (Set.range γQ); obtain ⟨c,v⟩:= basinG A; rw [v]; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; apply Submodule.smul_mem; apply Submodule.subset_span; refine ⟨ordered i j,?_⟩; unfold ordered; split; · -- k3 symmetric
    apply Subtype.ext; apply ContinuousLinearMap.ext; intro t; apply ContinuousLinearMap.ext; intro u; unfold γQ; rw [landsC,landsC,kite_h,kite_h,kite_h,kite_h]; dsimp only; ring
 rfl
lemma span_d(A:Gκ): A∈Submodule.span ℂ (Set.range γ5):=by obtain ⟨c,v⟩:= basinD A; rw [v]; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; apply Submodule.smul_mem; exact Submodule.subset_span ⟨(i,j.2,j.1),rfl⟩
lemma valveγ(x y:Gem)(k:G4): Dye R⁻¹ b ((γQ k).val (gird R x) (gird R y))=(pay ((Wb R k.val.1).xor (Wb R k.val.2)) (k3 (Waℓ R k.val.1) (Waℓ R k.val.2))).val x y:=by
 apply dye_real -- tune binder q unused
 · unfold γQ; simp [landsC,kite_h] -- complex? 
 unfold γQ; rw [landsC,kite_h,kite_h,blue_A,blue_A,blue_A,blue_A]; cases Wb R k.val.1<;> cases Wb R k.val.2<;>simp only [Bool.false_xor,Bool.true_xor,pay_false,pay_true,Bool.not_false,Bool.not_true,show ∀ x: G3, (-x).val = -x.val from fun _=> rfl,_root_.neg_apply, landsC] <;> simp [kite_h, add_comm] -- `;` scope all tune
lemma valveD (x:Gem)(y:Sut)(k:G5):let p:= (k.2.2,k.2.1); Dye R⁻¹ b (γ5 k (gird R x) (girdS R y))=(pay ((Wb R k.1).xor (Wδ R p)) (k5 (Waℓ R k.1) (Aδ R p))) x y:=by
 intro p; apply dye_real; · unfold γ5 k5; simp [kite_h] -- tune
 unfold γ5 k5; rw [kite_h,blue_A,blue_H]; change (((pay (Wb R k.1) _ :ℝ): ℂ)*((pay (Wδ R p) _ :ℝ):ℂ))= _; cases Wb R k.1 <;> cases Wδ R p <;> simp [kite_h,p]
lemma evalγ(k:G4): μG (γQ k)=evalTg k:= boltP ..
lemma evalΔ(k:G5):μD (γ5 k)=evalG k:=boltW ..
lemma κsort_G(i j:Wed): k3 i j=γQ (ordered i j):=by
 unfold ordered; split; · apply Subtype.ext; apply ContinuousLinearMap.ext; intro t; apply ContinuousLinearMap.ext; intro u; unfold γQ; rw [landsC,landsC,kite_h,kite_h,kite_h,kite_h]; dsimp only; ring
 rfl
lemma reprice_Ω(p:Waves)(k:G4)(e:bF4 p=γQ k): bF4 (pressA R b p)=pay (g4Act.cost R k) (γQ (g4Act.move R k)):=by
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; let a:=Waℓ R k.val.1; let d:=Waℓ R k.val.2; let x:=paintL_R R b p i j; change _= (pay ((Wb R k.val.1).xor (Wb R k.val.2)) (γQ (ordered a d))).val i j; rw [← κsort_G a d, paintL_R,e,valveγ]
lemma reprice_H(p:Waves)(k:G5)(e:bF5 p=γ5 k): bF5 (pressA R b p)=pay (g5Act.cost R k) (γ5 (g5Act.move R k)):=by
 apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; rw [paintR_D,e,valveD]; rw [show g5Act.cost R k = _ from (show _=(Wb R k.1).xor (Wδ R (k.2.2,k.2.1)) from (by dsimp only [g5Act,Labels.tensorProd,Wb,Wδ,v_cost]; simp only [Bool.xor_comm (R.flip k.2.2)] ; try rfl))]; try rfl
-- align when any grade.
variable (d:Floor)
lemma payM {X Y: Type}[AddCommGroup X][AddCommGroup Y][Module ℂ X][Module ℂ Y] (f:X→ₗ[ℂ]Y)(x:X)(p:Bool) : f (pay p x)= pay p (f x):=by cases p; rfl; simp
private def γissue : ↥G3 →ₗ[ℂ] Waves := LinearMap.prod 0 (LinearMap.prod (LinearMap.prod LinearMap.id 0) (LinearMap.prod 0 (LinearMap.prod 0 0)))
lemma bill_G (v:Waves): Align R b (gauge d) (μG (bF4 v)) (μG (bF4 (pressA R b v))):=by
 let A(z:G3):=μG (bF4 (pressA R b (γissue z))); let i:=bF4 v; have he:bF4 (pressA R b v)= bF4 (pressA R b (γissue i)):=by apply Subtype.ext; apply ContinuousLinearMap.ext; intro x; apply ContinuousLinearMap.ext; intro y; rw [paintL_R,paintL_R]; try rfl
 rw [he]; apply moment R b μG A ?_ ?_ γQ _ i (span_w _)
 · intro a p; unfold A; rw [map_add,press_a]; exact map_add μG _ _ -- tune order
 · intro a p; unfold A; rw [map_smul,press_c]; exact map_smul μG _ _
 intro i; unfold A; rw [reprice_Ω _ _ _ i rfl, payM,evalγ,evalγ]; exact align_γ R b _ _ _ (Conj.g_tr i) (fun w u p=> readingTg.moving R w u p i)
lemma bill_U(p:Waves): Align R b (gauge d) (μD (bF5 p)) (μD (bF5 (pressA R b p))):=by
 let A(z:Gκ):=μD (bF5 (pressA R b (onD_C z))); let i:=bF5 p; have he:bF5 (pressA R b p)= bF5 (pressA R b (onD_C i)):=by apply ContinuousLinearMap.ext; intro x; apply ContinuousLinearMap.ext; intro y; rw [paintR_D,paintR_D]; try rfl
 rw [he]; apply moment R b μD A ?_ ?_ γ5 _ i (span_d _)
 · intro a p; unfold A; rw [map_add,press_a]; exact map_add μD _ _
 · intro a p; unfold A; rw [map_smul,press_c]; exact map_smul μD _ _
 intro i; unfold A; rw [reprice_H _ _ _ i rfl,payM,evalΔ,evalΔ]; exact align_γ R b _ _ _ (Conj.g5_tr i) (fun w u p=>readingG.moving R w u p i)
end Fables
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
