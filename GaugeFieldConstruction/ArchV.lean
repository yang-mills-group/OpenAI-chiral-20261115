import GaugeFieldConstruction.Antares
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option maxRecDepth 4300
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
local instance : AddCommGroup ↥G15:= PackS.G.toAddCommGroup
local instance : Module ℂ ↥G15:= PackS.S.toModule
open Phys Row
open Matter (FlavorIndex)
open Raw
local notation "Gemidx"=> J Row.x
local notation "FPlumb"=> FlavorIndex → Gemidx
private lemma μMaker {X Y:Type}[AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y](f:X→Y)(h:∀ x y,f (x+y)=f x+f y)(u:∀ (r:ℂ) x,f (r • x)=r • f x):∃ V:X→ₗ[ℂ]Y,∀ x,V x=f x:= ⟨⟨⟨f,h⟩,u⟩, fun _=>rfl⟩
lemma BuildsΦ : ∃ W:G15 →ₗ[ℂ] FPlumb, ∀ x,W x= (symxG x).choose:=by
 refine μMaker (fun x:G15=>(symxG x).choose) (fun x y=>?_) (fun a x=>?_)
 · apply xfaith; apply Finsupp.ext; rintro ⟨p,r⟩; let Y(F:G15):= graph_x (symxG F).choose; change test (p,r) (Y _) =test (p,r) (graph_x _); rw [(show test _ (Y (x+y))= _ from (symxG (x+y)).choose_spec.2 p r),map_add graph_x,map_add (test (p,r)),(symxG x).choose_spec.2,(symxG y).choose_spec.2]; simp only [Submodule.coe_add,_root_.add_apply,map_add]
 apply xfaith; apply Finsupp.ext; rintro ⟨p,r⟩; let Y(F:G15):=graph_x (symxG F).choose; change test (p,r) (Y _) =test (p,r) (graph_x _); rw [show test _ (Y (a • x))= _ from (symxG (a • x)).choose_spec.2 p r,map_smul graph_x,map_smul (test (p,r)),(symxG x).choose_spec.2]; simp only [Submodule.coe_smul, ContinuousLinearMap.smul_apply,RingHom.id_apply,map_smul]
noncomputable def task_M:= BuildsΦ.choose
lemma taskEarn (x:G15)(p:Pen)(u:Spair): test (u,p) (graph_x (task_M x))=test u (goldΦ (x.val (hem (E_G p.1) (dye p.2)))):=by unfold task_M; rw [BuildsΦ.choose_spec]; exact (symxG x).choose_spec.2 u p
lemma Tearn_X (f:FlavorIndex)(p:Wed)(b:Axis): task_M (affK f p b)=single_x f (evalX (b,p)):=by
 apply xfaith; ext1 ⟨m,j⟩; change test (m,j) (graph_x (task_M _))= test (m,j) (graph_x (single_x _ _)); rw [taskEarn,voiceX,τprice]; -- tune
lemma task_range : LinearMap.range task_M= Submodule.pi Set.univ (fun _=>Record.space evalX):=by
 let X:=LinearMap.range task_M; refine le_antisymm (fun i ⟨j,h⟩ y _=> by rw [←h]; unfold task_M; rw [BuildsΦ.choose_spec]; exact (symxG j).choose_spec.1 y) ?_
 intro v e; have hx(i:FlavorIndex):single_x i (v i)∈ X:=by
    let L:= X.comap (single_x i); apply (show Record.space evalX ≤ L from ?_) (e _ (Set.mem_univ _)); unfold Record.space; rw [Fintype.range_linearCombination]; apply Submodule.span_le.mpr; rintro z ⟨p,rfl⟩; exact (show single_x i (evalX p)∈ X from ⟨_,Tearn_X ..⟩)
 rw [show v= ∑ i:FlavorIndex, single_x i (v i) from (by ext1 j; rw [Finset.sum_apply]; simp [single_x,Pi.single_apply])]; exact Submodule.sum_mem _ fun i _=> hx i
-- Mixed inject.Uses all P grid.B.via Wish.Zero Pin.Can't commute here. helper gold test extraction
lemma shooM (A:Pal)(b c:Tagφ): test (pick_l b c (0,0)) (goldΦ A)=skim_L false true A b c:=by
 let z:= test (pick_l b c (0,0)); let V(i j:Tagφ):= A (fisc false i) (fisc true j); unfold goldΦ; simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum,map_smul]; have he(i j:Tagφ): z (wedgeCR i j)= if (b=i∧c=j) then (1:ℂ) else 0:=by
    unfold wedgeCR; rw [fogC,fogC,Cauchy.takes]; change Finsupp.single (pick_l i j (0,0)) (1:ℂ) (pick_l b c (0,0))= _; rw [Finsupp.single_apply]; simp only [songs, true_and,and_true]; by_cases h:i=b<;>by_cases s:j=c<;> simp_all [eq_comm] -- tune
 unfold z at he; simp_rw [he]; rw [sum_eq_single b]
 · rw [sum_eq_single c]
   · rw [if_pos ⟨rfl,rfl⟩,smul_eq_mul, mul_one]; try rfl
   · intro j _ e; rw [if_neg (fun p=> e p.2.symm),smul_zero]
   simp
 · intro i _ e; apply sum_eq_zero; intro j _; rw [if_neg (fun p=>e p.1.symm), smul_zero]
 simp
lemma task_ker (A:G15): task_M A=0 ↔ A=0:=by
 refine ⟨fun h=>?_,fun p=> by rw [p,map_zero]⟩; have hp(i:GIndex)(p:Pig) : goldΦ (A.val (hem (E_G i) (dye p)))=0:=by
    ext1 j; rw [Finsupp.zero_apply]; change test j (goldΦ (A.val _))=0; rw [show hem (E_G i) (dye p)= hem (E_G (i,p).1) (dye (i,p).2) from rfl, ←taskEarn A (i,p) j,h,map_zero,map_zero] -- tune
 have he(i:GIndex)(p:Pig): skim_L false true (A.val (hem (E_G i) (dye p)))=0:=by
    ext b c; rw [← shooM,hp,map_zero]; rfl
 have hx(i:GIndex)(t:Pig): A.val (hem (E_G i) (dye t))=0:= swan ((bladeV _).binned _) (show salvo false true 0 from by simp [salvo]) ((he _ _).trans (map_zero _).symm)
 apply Subtype.ext; apply ContinuousLinearMap.ext; intro p; change A.val p=0; rw [trade_Z p,map_sum]; apply sum_eq_zero; intro j _; change A.val (grayC (dye j) _)= _; rw [bead_g (locusC j p),map_sum,map_sum]; apply sum_eq_zero; intro k _; rw [map_smul (grayC _),map_smul,show A.val (grayC (dye j) (E_G (winkL k.1 k.2)))=0 from hx _ _,smul_zero]
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
