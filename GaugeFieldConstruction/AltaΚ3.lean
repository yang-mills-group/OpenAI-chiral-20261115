import GaugeFieldConstruction.PanzaP3
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
abbrev FrameGrow3 (k:ℕ)(t:ℝ) := Book3 P σ X W0 Q0 (MealD H R k t) L (Season_i F R k t σ P A) S
-- p.Art.City.Up.Explicit.t
abbrev West3 (i:Key Λζ):= Reflect3 σ (g ∘ (boxA V).symm) (flipΘ V) x i
abbrev East3 (i:Key Λζ):Key J:= Reflect3 ι g false y i
local notation "X0"=> FrameGrow3 R F H P σ A X W0 Q0 L S k t p
local notation "X1"=> FrameGrow3 R F H P ι B X' W1 Q1 L T k t q
local notation "D0" m:max=>FrameGrow3 R F H P σ A X W0 Q0 L S k t m
local notation "D1" m:max=>FrameGrow3 R F H P ι B X' W1 Q1 L T k t m
local notation "F0"=>West3 V σ g x
local notation "F1"=> East3 ι g y
-- Original data orientation at single key X. ∃ exact list scope.
structure Mosaic3 (σ:I→Seat n)(ι:J→Seat n)(e:Key I)(f:Key J)(R:Rio I n)(G':Rio J n): Prop where
 rise(i:Hub n): suit_Y V (Canz σ _ (pureX R) e i Y.1)=Canz ι _ (pureX G') f (orbit4 V i) (twistW' V Y).1
 boat(i:Force n): suit_Y V (Canz σ _ R.B e i Y)=Canz ι _ G'.B f (arm4 V i) (twistW' V Y)
structure Found3 :Prop where
 dawn(i:Key Λζ)(D:Aura n):suit_Y V (WritV σ W0 (West3 V σ g x i) D Y)= WritV ι W1 (East3 ι g y i) (moldA V D) (twistW' V Y)
 turn(i:Key Λζ)(D:Aura n)(L:Support (More n))(s:L.Nonempty)(l:L⊆D.val):suit_Y V (WritV σ Q0 (West3 V σ g x i) D L Y)= WritV ι Q1 (East3 ι g y i) (moldA V D) (actY V L) (twistW' V Y)
 known(i:Key Λζ)(D:Force n):suit_Y V (Canz σ _ X (West3 V σ g x i) D Y)= Canz ι _ X' (East3 ι g y i) (arm4 V D) (twistW' V Y)
variable (ψ:Found3 Y V σ ι X W0 Q0 X' W1 Q1 g x y)
variable (u:∀ s:Key Λζ, Mosaic3 Y V σ ι (West3 V σ g x s) (East3 ι g y s) (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q))
section
include v
lemma lunarK (b:Bool)(Qc:Key Λζ):(Reflect3 σ g b x (dune (g o) Qc))=blank3 σ o (Reflect3 σ g b x Qc):=by
 funext i; unfold Reflect3 blank3; change x i*cSignX b (Function.update Qc (g o) 0 (g _))= _; split_ifs with t; · rw [t,update_self]; cases b<;>simp[cSignX]
 rw [update_of_ne (v.ne t)]; -- tune αAE update_of_ne argument
local notation "χG"=> ΛLine σ W0 Q0 Y
local notation "χV"=> ΛLine ι W1 Q1 (twistW' V Y)
include ψ u
lemma paper_ζ (i:Key Λζ)(M:Support (More n))(j: Vox3 n) :ΛLine ι W1 Q1 (twistW' V Y) (blank3 ι ((boxA V).symm o) (East3 ι g y i)) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q) (actY V M) (VoxFit V j)= suit_Y V (ΛLine σ W0 Q0 Y (blank3 σ o (West3 V σ g x i)) (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) M j):=by
 let s:= dune (Z o) i
 let A₀:= WritV σ W0 (West3 V σ g x s); let Z₁:= WritV σ Q0 (West3 V σ g x s)
 rw [show blank3 σ o (West3 V σ g x i)= F0 s from (lunarK o σ Z (v.comp ((boxA V).symm.injective)) x _ i).symm, show blank3 ι (δ o) (East3 ι g y i)= East3 ι g y s from (lunarK (δ o) ι g v y _ i).symm] -- order tune
 unfold ΛLine DropW; rcases j with i|i
 · change (if Disjoint (actY V M) (actY V i.val) then _ else _)= θ (if Disjoint M i.val then _ else _)
   simp_rw [joint_m]; split_ifs with t; exact (ψ.dawn _ _).symm
   have hp:(M ∩ i.val).Nonempty:=not_disjoint_iff_nonempty_inter.mp t
   rw[map_neg]; change - _= - _; congr 1
   rw[show (actY V M∩ (moldA V i).val)=_ from (show _=actY V (M∩ i.val) from (Finset.map_inter ..).symm)]
   exact (ψ.turn s i _ hp inter_subset_right).symm
 change (if Disjoint (actY V M) (actY V i.val.2) then _ else _)= θ (if Disjoint M i.val.2 then _ else _)
 simp_rw[joint_m]; split_ifs; exact (u s|>.rise i).symm; exact (map_zero _).symm
lemma paper_φ (i:Key Λζ)(j:Force n) : ReefB ι X' (twistW' V Y) (blank3 ι ((boxA V).symm o) (East3 ι g y i)) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q) (arm4 V j)=suit_Y V (ReefB σ X Y (blank3 σ o (West3 V σ g x i)) (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) j):=by
 let s:= dune (Z o) i; rw[show blank3 σ o (West3 V σ g x i)= West3 V σ g x s from (lunarK o σ Z (v.comp (boxA V).symm.injective) x _ i).symm, show blank3 ι (δ o) (East3 ι g y i)=East3 ι g y s from (lunarK (δ o) ι g v y _ i).symm]; unfold ReefB; rw [puff_add,puff_add, Pi.add_apply,Pi.add_apply,map_add]; exact congrArg₂ (·+·) (ψ.known s j).symm ((u s).boat j).symm
#print axioms paper_φ
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
