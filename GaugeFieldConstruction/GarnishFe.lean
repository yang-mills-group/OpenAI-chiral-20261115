import GaugeFieldConstruction.SpritaFe
import GaugeFieldConstruction.Merise
import GaugeFieldConstruction.Emerick
set_option autoImplicit false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open HushP ModuleB Pastry
open Housing Flot
set_option maxRecDepth 3000
open scoped YM.CF.Mew
open BrentFe
open YM.GaugeFieldConstruction.Flavor
variable (v:BigFe)
abbrev palFe := RiseFe SpinIdx v
def τoneFe : Pal→L[ℝ]Pal:= LinearMap.toContinuousLinearMap {toFun:=twist (palFe v),map_add':=fun _ _=>map_add _ _ _,map_smul':=fun _ _=>map_smul _ _ _}
abbrev ageFe:=twist (palFe v)
lemma τoneFe_p(Z:Pal):τoneFe v Z=ageFe v Z:= rfl
lemma spot_F (g:SU.E):ageFe v (KinX g)=KinX g:=by
 apply twistFE; change ((1:Op _) ⊗ₖ (Ferr v).val)*_= _*((1:Op _)⊗ₖ (Ferr v).val); unfold KinX; rw [op_kron_mul,op_kron_mul,matFe]
lemma standBFe (b:Bool):ageFe v (baseF b)=baseF b:=by
 have ht:ageFe v (Ember.bins SU.Slot)=Ember.bins SU.Slot:=by
   apply twistFE; change ((1:Op _)⊗ₖ _)*_=_*((1:Op _) ⊗ₖ (Ferr v).val); unfold Ember.bins; rw [op_kron_mul,op_kron_mul]; simp
 cases b
 · exact ht
 change ageFe v (1-Ember.bins _) = _; rw [map_sub,map_one,ht]; rfl
lemma SheetQ.Fe (X:Pal)(p:SheetQ X):SheetQ (ageFe v X):=by
 constructor
 · calc
     _=ageFe v (baseF false*X*baseF true):=by rw [map_mul,map_mul,standBFe,standBFe]
     _=ageFe v X:=by rw [p.bin]
 intro g; have ht:=(p.tax g).map (ageFe v); rw [spot_F] at ht; exact ht
lemma ViewsM.Fe_ (f:ComG→L[ℝ]Pal)(p:ViewsM f):ViewsM ((τoneFe v).comp f):=by
 constructor
 · intro i; calc
     _=ageFe v (baseF false*f i*baseF true):=by rw [map_mul,map_mul,standBFe,standBFe]; rfl
     _= _:=by rw[p.binned]; rfl
 intro g a i; simp only [ContinuousLinearMap.comp_apply,τoneFe_p]
 have he:=p.main g a i; have hv:=congrArg (ageFe v) he; simp only [map_mul,spot_F] at hv; exact hv
-- actually Pack uniform
abbrev ΦFeP (p:PalOne):= postF p (τoneFe v)
def SpinFe (x:Waves): Waves:=by
 let P:= chartF x; let A:= ΦFeP v P
 refine (⟨A.1,SheetQ.Fe v P.1 (chart_j x).1⟩,(bF4 x,⟨A.2.1,?_⟩),bF5 x,⟨A.2.2.val,?_⟩,⟨(τoneFe v).comp (bm5 x).val,ViewsM.Fe_ v _ (bm5 x).property⟩)
 · exact fun i=>SheetQ.Fe v _ ((chart_j x).2.1 i)
 · exact fun i j=> ⟨SheetQ.Fe v _ ((chart_j x).2.2 i j), A.2.2.property i j⟩
lemma SpinFe_chart (x:Waves): chartF (SpinFe v x)=ΦFeP v (chartF x):=rfl
lemma SpinFe_m (x:Waves): (bm5 (SpinFe v x)).val=(τoneFe v).comp (bm5 x).val:= rfl
lemma poleFe (i j:Site n): matPH (FieldFe n v).val i j= if i=j then (palFe v).val else 0:=by
 ext a b; change ((1:Op (Site n ×SpinIdx)) ⊗ₖ (Ferr v).val) ((i,a.1),a.2) ((j,b.1),b.2)= _; by_cases h:i=j <;>simp only [h, ↓reduceIte,Matrix.kronecker_apply] <;> first
 | (change _ = ((1:Op SpinIdx) ⊗ₖ (Ferr v).val) a b; rw[Matrix.kronecker_apply]; simp [Matrix.one_apply])
 | simp [Matrix.one_apply,h]
lemma mastFe (Q:Op (Single n))(x y:Site n): matPH (twist (FieldFe n v) Q) x y=ageFe v (matPH Q x y):=by
 rw [twist_formula,twist_formula, matDot]; simp_rw [matStar,poleFe,matDot,poleFe]
 simp [apply_ite] -- tune mul
variable (o)
lemma opticFe(Q:Op (Single n))(u:Views): streamF o (twist (FieldFe n v) Q) h u=ageFe v (streamF o Q h u):=by rw [streamS,streamS]; simp only [map_sum,mastFe,twist_scalar,ageFe]
variable (M:Tulip.Male)
lemma fellFe (b:Bool)(x:Views): ageFe v (fellP M b x)=fellP M b x:=by
 have he(p): ageFe v (Tap.boot 4 M p)=Tap.boot 4 M p:=by -- inspect j
    apply twistFE; unfold Tap.boot; change ((1:Op _)⊗ₖ _)*_= _* ((1:Op _)⊗ₖ (Ferr v).val); rw [op_kron_mul,op_kron_mul]; simp
 unfold fellP binor; cases b <;> simp only [ite_true,Bool.false_eq_true,ite_false, map_sub,map_one,he] -- tune
lemma imageJFe (Z:Op (Single n)):winJ o M h (twist (FieldFe n v) Z)=ΦFeP v (winJ o M h Z):=by
 apply (tab (o:=o) (h:=h) M (twist (FieldFe n v) Z)).unique; apply ((tab M Z).geomF (τoneFe v)).equal (Eventually.of_forall fun i=>?_)
 unfold TabX; dsimp only [Function.comp_apply]; simp only [τoneFe_p,opticFe,map_mul, standBFe, fellFe]
end Layout
end Lenten
end YM.CF.TableF
end
