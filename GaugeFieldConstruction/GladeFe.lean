import GaugeFieldConstruction.SpritaFe
import GaugeFieldConstruction.GarnishFe
import GaugeFieldConstruction.Emerick
set_option autoImplicit false
set_option maxHeartbeats 30000
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
lemma FestFe_eq(x y:Waves)(P:bF4 x=bF4 y)(Q:bF5 x=bF5 y)(U:(bV0 x).val=(bV0 y).val)
 (H:∀ i,(bV1 x).val i=(bV1 y).val i)(A:∀ i,(bV2 x).val i i=(bV2 y).val i i)
 (B:∀ i,(bm5 x).val i=(bm5 y).val i):x=y:=XGarden.MastTin.econUni _ _ P Q (Subtype.ext (ContinuousLinearMap.ext B)) (Prod.ext U (Prod.ext (ContinuousLinearMap.ext H) (dual_uni _ _ A)))
lemma QbV0T(v:BigFe)(x:Waves):(bV0 (SpinFe v x)).val= ageFe v ((bV0 (x)).val):=rfl
lemma QbV0A(x y: Waves):(bV0 (x+y)).val=(bV0 (x)).val+(bV0 (y)).val:=rfl
lemma QbV0B(x:Waves)(c:ℂ):(bV0 (c • x)).val=c • ((bV0 (x)).val):=rfl
lemma QbV1T(v:BigFe)(x:Waves)(i:Views):(bV1 (SpinFe v x)).val i= ageFe v ((bV1 (x)).val i):=rfl
lemma QbV1A(x y: Waves)(i:Views):(bV1 (x+y)).val i=(bV1 (x)).val i+(bV1 (y)).val i:=rfl
lemma QbV1B(x:Waves)(c:ℂ)(i:Views):(bV1 (c • x)).val i=c • ((bV1 (x)).val i):=rfl
lemma QbV2T(v:BigFe)(x:Waves)(i:Views):(bV2 (SpinFe v x)).val i i= ageFe v ((bV2 (x)).val i i):=rfl
lemma QbV2A(x y: Waves)(i:Views):(bV2 (x+y)).val i i=(bV2 (x)).val i i+(bV2 (y)).val i i:=rfl
lemma QbV2B(x:Waves)(c:ℂ)(i:Views):(bV2 (c • x)).val i i=c • ((bV2 (x)).val i i):=rfl
lemma Qbm5T(v:BigFe)(x:Waves)(i:ComG):(bm5 (SpinFe v x)).val i= ageFe v ((bm5 (x)).val i):=rfl
lemma Qbm5A(x y: Waves)(i:ComG):(bm5 (x+y)).val i=(bm5 (x)).val i+(bm5 (y)).val i:=rfl
lemma Qbm5B(x:Waves)(c:ℂ)(i:ComG):(bm5 (c • x)).val i=c • ((bm5 (x)).val i):=rfl
lemma QbF5T(v:BigFe)(x:Waves):bF5 (SpinFe v x)=bF5 x:=rfl
lemma QbF4T(v:BigFe)(x:Waves):bF4 (SpinFe v x)=bF4 x:=rfl
lemma QbF4H(v:BigFe)(x:Waves)(i j:Gem): (bF4 (SpinFe v x)).val i j=(bF4 (x)).val i j:=rfl
lemma QbF4A(x y:Waves)(i j:Gem): (bF4 (x+y)).val i j=(bF4 (x)).val i j+(bF4 (y)).val i j:=rfl
lemma QbF4B(x:Waves)(c:ℂ)(i j:Gem): (bF4 (c • x)).val i j=c • (bF4 (x)).val i j:=rfl
lemma QbF5H(v:BigFe)(x:Waves)(i:Gem)(j:Sut): bF5 (SpinFe v x) i j=bF5 (x) i j:=rfl
lemma QbF5A(x y:Waves)(i:Gem)(j:Sut): bF5 (x+y) i j=bF5 (x) i j+bF5 (y) i j:=rfl
lemma QbF5B(x:Waves)(c:ℂ)(i:Gem)(j:Sut): bF5 (c • x) i j=c • bF5 (x) i j:=rfl

lemma Spin_UFe (v:BigFe)(x y:Waves): SpinFe v (x+y)= SpinFe v x+SpinFe v y:=by
 apply FestFe_eq
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF4H,QbF4A]
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF5H,QbF5A]
 · simp only [QbV0T,QbV0A,map_add]
 · intro i; simp only [QbV1T,QbV1A,map_add]
 · intro i; simp only [QbV2T,QbV2A,map_add]
 · intro i; simp only [Qbm5T,Qbm5A,map_add]
lemma Spin_qFe (v:BigFe)(a:ℂ)(x:Waves): SpinFe v (a • x)=a • SpinFe v x:=by
 apply FestFe_eq
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF4H,QbF4B]
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF5H,QbF5B]
 · simp only [QbV0T,QbV0B, ageFe,twist_scalar]
 · intro i; simp only [QbV1T,QbV1B, ageFe,twist_scalar]
 · intro i; simp only [QbV2T,QbV2B, ageFe,twist_scalar]
 · intro i; simp only [Qbm5T,Qbm5B, ageFe,twist_scalar]
lemma SpinFe_U (W: Waves):SpinFe 1 W=W:=by
 let p:= palFe 1; have h:p=1:=map_one (RiseFe SpinIdx); have he(z:Pal):ageFe 1 z=z:=by change twist p z=z; rw[h,one_des]
 apply FestFe_eq
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF4H]
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF5H]
 · simp only [QbV0T,he]
 · intro i; simp only [QbV1T,he]
 · intro i; simp only [QbV2T,he]
 · intro i; simp only [Qbm5T,he]
lemma SpinFe_joint (u v:BigFe)(W:Waves): SpinFe (u*v) W=SpinFe u (SpinFe v W):=by
 have he(z:Pal):ageFe (u*v) z=ageFe u (ageFe v z):=by unfold ageFe palFe; rw[map_mul,Fock.twin]
 apply FestFe_eq
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF4H]
 · apply ContinuousLinearMap.ext; intro i; apply ContinuousLinearMap.ext; intro j; simp only [QbF5H]
 · simp only [QbV0T,he]
 · intro i; simp only [QbV1T,he]
 · intro i; simp only [QbV2T,he]
 · intro i; simp only [Qbm5T,he]
#print axioms SpinFe_joint
end Layout
end Lenten
end YM.CF.TableF
end
