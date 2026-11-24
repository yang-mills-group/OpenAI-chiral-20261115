import GaugeFieldConstruction.Arabic
import GaugeFieldConstruction.Fanfare
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
abbrev single_x(i:FlavorIndex): Gemidx→ₗ[ℂ] FPlumb:= LinearMap.single ℂ (fun _=> Gemidx) i
lemma voiceX (i:FlavorIndex)(x:Gemidx): graph_x (single_x i x)= tuap i x:=by 
 rw [graph_x,LinearMap.sum_apply,sum_eq_single i]; · rw [LinearMap.comp_apply]; congr 1; simp only [single_x,LinearMap.single_apply,LinearMap.proj_apply,Pi.single_eq_same]
 · intro k _ p; rw [LinearMap.comp_apply]; simp only [single_x,LinearMap.proj_apply, LinearMap.single_apply, Pi.single_eq_of_ne p, map_zero]
 simp -- tune sum_ite
lemma wrapt (A:Pal) (k:Axis)(X:Op SU.Slot)(p:skim_L false true A=cliff k ⊗ₖ X):goldΦ A= (∑ i:SU.Slot,∑ j:SU.Slot,X i j • sD i j : J Row.f→ₗ[ℂ] J Spair) (Row.B k):=by
 let Q: J Row.f→ₗ[ℂ] J Spair:=∑ i:SU.Slot,∑ j:SU.Slot,X i j • sD i j; unfold goldΦ; change ∑ i:Tagφ,∑ j:Tagφ,A (fisc false i) (fisc true j) • wedgeCR i j=Q (Row.B k); rw [Fintype.sum_prod_type (α₁:=Spin) (α₂:=SU.Slot)]; unfold Row.B; rw [map_sum]; apply sum_congr rfl; intro i _; simp_rw [Fintype.sum_prod_type (α₁:=Spin) (α₂:=SU.Slot)]
 rw [map_sum,sum_comm]; apply sum_congr rfl; intro j _; rw [map_smul]; unfold Q; rw [LinearMap.sum_apply,smul_sum]; apply sum_congr rfl; intro x _; rw [LinearMap.sum_apply,smul_sum]; apply sum_congr rfl; intro y _; rw [show A _ _ = Hij k i j* X x y from Matrix.ext_iff.mpr p (i,x) (j,y)]; simp_rw [mul_smul]; congr 1; rw [LinearMap.smul_apply]; apply congrArg; unfold sD; rw [straps]; rfl
lemma P_ram (A:Pal)(k:Axis)(X:Op SU.Slot)(p:skim_L false true A=cliff k⊗ₖ X)(a b:FIndex)(x y:SU.Slot): test ((a,x),(b,y)) (goldΦ A)=X x y*test (a,b) (Row.B k):=by
 rw [wrapt A k X p]; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.smul_apply,map_smul,bank_f]; simp [ite_and, Finset.sum_ite_irrel] -- tune bank ambiguity
-- direct basis.Wi.Payload. test φ matter coordinates.
lemma τprice (k:FlavorIndex)(f:Wed)(a:Axis)(m:Pen)(u:Spair): let Q:=tuap k (evalX (a,f)); let W:=hem (E_G m.1) (dye m.2); test (u,m) Q=test u (goldΦ ((affK k f a).val W)):=by
 intro Q W; rcases u with ⟨⟨p,i⟩,j,l⟩; rcases m with ⟨t,c⟩
 rw [show test (((p,i),(j,l)),(t,c)) Q=_ from income_x ..]
 let X:= (affK k f a).val W; let g:= goldΦ X; have hp: skim_L false true X=cliff a⊗ₖ Λshade k (blueL f (E_G t) • dye c):=growX ..
 let T:=Λshade k (blueL f (E_G t) • dye c); let Z:=evalX (a,f); have ht:test ((p,j),t) Z=test (p,j) (Row.B a)*test t (arc f):= tested ..
 have hz:test t (arc f)=↑(blueL f (E_G t)):=portal ..
 rw [ht,hz]; let d:=blueL f (E_G t)
 have he: T i l=(d:ℂ)*beta k c i l:=by unfold T; rw [map_smul, Matrix.smul_apply,Complex.real_smul]; try rfl
 rw [P_ram X a T hp, he]; ring
-- Recover.Book.Pay
lemma symxG (A: G15):∃ X:FPlumb,(∀ i,X i∈ Record.space evalX) ∧∀ u:Spair,∀ p:Pen, test (u,p) (graph_x X)=test u (goldΦ (A.val (hem (E_G p.1) (dye p.2)))):=by
 let K(F:G15):Prop:=∃ X:FPlumb,(∀ i,X i∈Record.space evalX) ∧∀ u:Spair,∀ p:Pen,test (u,p) (graph_x X)=test u (goldΦ (F.val (hem (E_G p.1) (dye p.2))))
 apply Submodule.span_induction (p:=fun x _=> K x) _ _ _ _ (σshelfV A)
 · rintro x ⟨⟨h,m,s⟩,rfl⟩; refine ⟨single_x h (evalX (s,m)),fun i=>?_,fun u p=>?_⟩
   · by_cases t:h=i; · subst i; rw [show single_x h _ h=_ from Pi.single_eq_same h (evalX (s,m))]; unfold Record.space; rw [Fintype.range_linearCombination]; exact Submodule.subset_span ⟨_,rfl⟩ -- tune
     rw [show single_x h (evalX (s,m)) i=0 from Pi.single_eq_of_ne (Ne.symm t) _]; exact (Record.space _).zero_mem
   rw [voiceX,τprice]; try rfl
 · refine ⟨0,fun i=>(Record.space _).zero_mem,fun u p=>?_⟩; rw [map_zero,map_zero, show (0:G15).val _=0 from rfl,map_zero,map_zero]
 · rintro i j _ _ ⟨x,p,e⟩ ⟨y,s,q⟩; refine ⟨x+y,fun i=>(Record.space evalX).add_mem (p i) (s i),fun u w=>?_⟩; rw [map_add,map_add,e,q,Submodule.coe_add,_root_.add_apply,map_add,map_add]
 rintro a x _ ⟨y,h,g⟩; refine ⟨a • y,fun i=> (Record.space _).smul_mem _ (h i),fun u w=>?_⟩; rw [map_smul,map_smul,g,Submodule.coe_smul, ContinuousLinearMap.smul_apply,map_smul,map_smul]
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
