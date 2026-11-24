import ZecaInk
import ZecaNib
import YM.SU5.Aria.Stagehand
import YM.SU5.Aria.Silhouette
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric

open Hierarchy.Seld Hierarchy.Seld.Zeca
local notation "G" => P.ManyF j x
local notation "Ω"=> P.heaven j x
local notation "S"=>P.seasons j x
local notation "E"=> (P.seasons j x).E


def nv : Bench (P.seasons j x):=⟨P.heaven j x,hail (P.seasons j x) _ (P.heaven_hot j x)⟩

lemma prepaid : saucer (P.seasons j x) (P.heaven j x)=P.heaven j x:=
 still S Ω (P.heaven_hot j x)

abbrev poseSp (p:Vantage):OS.Cross j:= transverse j (fun i=>p i.val)
lemma cart_m (p:Vantage): P.cartage j x p= M (P.seasons j x) (poseSp j p).val:=by
 rw [P.uses_cart,laneslot]
lemma nova (y:E4):M S y (nv P j x).val=Ω:= by
 let L:=OS.Semigroup.SEP j y
 show ((S).edge (y j)) ((S).U L (Ω))=_
 have h:(S).U L= P.cartage j x (fun i=> L.val i):=by
    rw [P.uses_cart,(eyes_toFace j L).symm]
 rw [h,P.cart_empty]
 let n:= S
 let w:G:=Ω
 have e:saucer n w=w:= P.prepaid j x
 open OS.Semigroup in
 exact (congrArg (n.edge (y j)) (P.heaven_hot j x 1).symm).trans
   ((n.high (y j) w).trans (heatO n w e _ (length.mpr zero_lt_one)))

lemma dazzle_m (p:Vantage)(D:(G).Op):
 P.dazzle j x p D=optx S D (poseSp j p).val:=by
 rw [show P.dazzle j x p D=P.cartage j x p * D * P.cartage j x (-p) from rfl,
       P.cart_m,P.cart_m,show (poseSp j (-p)).val=-(poseSp j p).val by
        ext i; by_cases h:i=j
        · subst i; change (poseSp j (-p)).val j=-(poseSp j p).val j; rw [show (poseSp j p).val j=0 from (poseSp j p).property, show (poseSp j (-p)).val j=0 from (poseSp j (-p)).property, neg_zero]
        exact (transverse_eyes j _ ⟨i,h⟩).trans ((congrArg (Neg.neg ·) (transverse_eyes j (fun i=>p i.val) ⟨i,h⟩)).symm)]

abbrev penny (F:P.Nib j x):ℝ≥0→ℝ≥0→(G).Op:=fun t u=> F t u
structure Truth (F:P.Nib j x)(D:Zeca.Moment G):Prop where
 translation (a b:ℝ≥0)(i:0<a)(r:0<b):F a b=D.cost (P.seasons j x) a b

lemma sticks_n {F:P.Nib j x}(f:P.Bottle j x F):sticks S (P.penny j x F):=by
 intro t u n m e w
 unfold penny
 have s:0<(t:ℝ):=n
 have r:0<(u:ℝ):=m
 rw [NNReal.coe_add,NNReal.coe_add,f.prop s r (le_add_of_nonneg_left e.coe_nonneg) (le_add_of_nonneg_right w.coe_nonneg),
  add_sub_cancel_right, add_sub_cancel_left]
 change (E (e:ℝ).toNNReal) * F t u * (E (w:ℝ).toNNReal) =_
 simp

lemma bottles_m (F:P.Nib j x)(f:P.Bottle j x F):
 ∃ D:Zeca.Moment G,P.Truth j x F D:=by
 obtain ⟨B,n,r,y⟩:= f.pay
 have m:Earn S (P.penny j x F) (n+1):=
   ⟨⟨n,Nat.lt_succ_self _,B,r, fun t i w=>y t i w⟩, P.sticks_n j x f⟩
 obtain ⟨D,g⟩:=earn_q S _ _ m
 exact ⟨⟨n+1,D⟩,⟨fun a b i m=>(rec_pay S _ _ g i m).symm⟩⟩

def Bought (D:Zeca.Moment G)(Y:ℕ→P.Apron):Prop:=
 ∃ F, P.NibLine j x F Y 1 ∧ P.Truth j x F D

#print axioms bottles_m
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
