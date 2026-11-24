import GaugeFieldConstruction.«BlastΘ3»
import GaugeFieldConstruction.IrenaK3
import GaugeFieldConstruction.Plush
import GaugeFieldConstruction.GibraltarA
import GaugeFieldConstruction.Barrera4
import GaugeFieldConstruction.Photon3
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
namespace Argos
open XGarden.MastTin
set_option linter.unusedTactic false
open Rio Iona Isle Py Ione Urn Broc Levier Salt
section
open XGarden XGarden.Shield SliceRoof Nacre
variable {n:Side}{d a a' c c' t:ℝ}(k:ℕ)(R:Loom n)(F:Elm n Unit d a c)(H:Elm n Unit d a' c')(Y:Orbit n)(V:Sweep n)
variable {I J Λζ:Type}[Fintype I][LinearOrder I][Fintype J][LinearOrder J][Fintype Λζ][LinearOrder Λζ]
variable (P:BudgetPoint)(o:Seat n)(σ:I→Seat n)(ι:J→Seat n)(A:I→Paper n)(B:J→Paper n)
variable (X:KK I (Copy n) n)(W0:Finset I→Pax n)(Q0:Finset I→Cusp n)(X':KK J (Copy n) n)(W1:Finset J→Pax n)(Q1:Finset J→Cusp n)
variable (g: Seat n→Λζ)(v:Injective g)(h:pure_Rim F)(d0:groupShape F)(d':groupShape H)(hp:Roof n t d k R)(cV:0<d)(hu:Injective (priorP Y.2))
variable (L:ℕ)(S T:Ids n)(p l:List I)(q m:List J)(x:Key I)(y:Key J)
local notation "G"=> orbit4 V
local notation "O"=> arm4 V
local notation "δ"=> (boxA V).symm
local notation "Z"=> g ∘ (boxA V).symm
local notation "Λ"=> twistW' V Y
local notation "Θ"=>lotR3 V
local notation "θ"=>suit_Y V
local notation "Kρ"=>Season_i F R k t
-- lanes Q.F Book cast.
local notation "X0"=> FrameGrow3 R F H P σ A X W0 Q0 L S k t p
local notation "X1"=> FrameGrow3 R F H P ι B X' W1 Q1 L T k t q
local notation "D0" m:max=>FrameGrow3 R F H P σ A X W0 Q0 L S k t m
local notation "D1" m:max=>FrameGrow3 R F H P ι B X' W1 Q1 L T k t m
local notation "PuχQ"=>West3 V σ g x
local notation "PuχR"=> East3 ι g y
variable (ψ:Found3 Y V σ ι X W0 Q0 X' W1 Q1 g x y)
variable (W:∀ i∈realm_C σ, Bake.Turf (W0 i))(U:∀ i∈realm_C ι,Bake.Turf (W1 i))(hB:∀ i:KI I n,X i≠0→ i.1∈realm_C σ)(qB:∀ i:KI J n,X' i≠0→ i.1∈realm_C ι)
-- e forces all ζ-equipped pairs chart.P.Clock order.
inductive Tide3 : List I→ List J→ Prop where
 | nil:Tide3 [] []
 | stanza {l:List I}{p:List J} : Tide3 l p→∀ (x':List I)(y':List J)(o:Seat n),(∀ i∈x',σ i=o)→(∀ i∈y',ι i=(boxA V).symm o)→ ShiftL V (Latζ A x' x) (Latζ B y' y) Y.1 → Tide3 (l++x') (p++y') -- σ syntax implicit args. all Y.
include v h d0 d' hp cV hu ψ W U hB qB
lemma compass (A0:Tide3 (Y:=Y) (V:=V) (σ:=σ) (ι:=ι) (A:=A) (B:=B) (x:=x) (y:=y) p q) :∀ i:Key Λζ,Mosaic3 Y V σ ι (West3 V σ g x i) (East3 ι g y i) (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q) :=by
 induction A0 with
 | nil =>
    intro i
    have z:pureX (D0 [])=0:=zero_add _
    have v:pureX (D1 [])=0:=zero_add _
    constructor
    · intro u; rw[z,v]; unfold Canz; simp only [Pi.zero_apply,smul_zero,sum_const_zero,map_zero]
    intro u; rw [show (D0 []).B=0 from rfl,show (D1 []).B=0 from rfl]; unfold Canz; simp only [Pi.zero_apply,smul_zero,sum_const_zero,map_zero]
 | @stanza l p t Xo Yo o x' y' h ih=>
    intro s; refine ⟨?_,?_⟩
    · exact Lantern k R F H Y V P o σ ι A B X W0 Q0 X' W1 Q1 g v ‹pure_Rim F› d0 d' hp cV hu L S T l Xo p Yo x y ψ ih x' y' h W U s
    exact Northern k R F H Y V P o σ ι A B X W0 Q0 X' W1 Q1 g v ‹pure_Rim F› d0 d' hp cV hu L S T l Xo p Yo x y ψ ih x' y' h W U hB qB s
lemma NorthernWay (p0: Tide3 (Y:=Y) (V:=V) (σ:=σ) (ι:=ι) (A:=A) (B:=B) (x:=x) (y:=y) p q) : Mosaic3 Y V σ ι x y (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q) :=by
 have hh:= compass k R F H Y V P σ ι A B X W0 Q0 X' W1 Q1 g v h d0 d' hp cV hu L S T p q x y ψ W U hB qB p0 1
 have hp: East3 ι g y 1=y:= funext fun i=>mul_one _
 have ht: West3 V σ g x 1=x:= funext fun i=> by unfold West3 Reflect3; rw [Pi.one_apply]; rw[sign3,map_one,mul_one]
 rwa[ht,hp] at hh
-- skipping blocks
omit W U ψ hB qB v h d0 d' hp cV hu
section
variable (g0:Tide3 (Y:=Y) (V:=V) (σ:=σ) (ι:=ι) (A:=A) (B:=B) (x:=x) (y:=y) p q)
include g0
lemma p_skip3 (k:I)(u:x k=0): Tide3 (Y:=Y) (V:=V) (σ:=σ) (ι:=ι) (A:=A) (B:=B) (x:=x) (y:=y) (p++[k]) q:=by
 rw [show q=q++[] from (List.append_nil ..).symm]; -- q duplicate? use
 refine Tide3.stanza g0 _ _ (σ k) (fun i h=>by simp at h; rw[h]) (fun i t=>by simp at t) ?_
 unfold ShiftL; have v':Latζ A [k] x=0:= by unfold Latζ; simp [u]; -- multilinear ζ
 rw [v']; funext i; rw[stripeQ]; simp [αLines,cSignX,Latζ]
lemma q_skip3(k:J)(u:y k=0): Tide3 (Y:=Y) (V:=V) (σ:=σ) (ι:=ι) (A:=A) (B:=B) (x:=x) (y:=y) p (q++[k]):=by
 rw [show p=p++[] from (List.append_nil ..).symm];
 refine Tide3.stanza g0 _ _ (boxA V (ι k)) (fun i t=>by simp at t) (fun i h=>by simpa [(by simp at h; exact h : i=k)]) ?_
 unfold ShiftL; have h:Latζ B [k] y=0:=by unfold Latζ; simp [u]; -- guard
 rw[h]; funext i; rw[stripeQ]; simp [αLines,Latζ,cSignX]
#print axioms NorthernWay
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
