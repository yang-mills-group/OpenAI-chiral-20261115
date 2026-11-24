import GaugeFieldConstruction.AltaΚ3
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
variable (u:∀ s:Key Λζ, Mosaic3 Y V σ ι (West3 V σ g x s) (East3 ι g y s) (FrameGrow3 R F H P σ A X W0 Q0 L S k t p) (FrameGrow3 R F H P ι B X' W1 Q1 L T k t q))
section
variable (e:∀ i∈l, σ i=o)(w:∀ i∈m,ι i=(boxA V).symm o)
variable (ts:ShiftL V (Latζ A l x) (Latζ B m y) Y.1)
-- glyph premise Lane.PD.
variable (W:∀ i∈realm_C σ, Bake.Turf (W0 i))(U:∀ i∈realm_C ι,Bake.Turf (W1 i))(hB:∀ i:KI I n,X i≠0→ i.1∈realm_C σ)(qB:∀ i:KI J n,X' i≠0→ i.1∈realm_C ι)
private lemma Lat_ζ (b:Bool)(K:I→Paper n)(u:∀ i∈l,σ i=o)(z:Key Λζ) : Latζ K l (Reflect3 σ g b x z)= (ρ3 b (z (g o))) • Latζ K l x:=by
 induction l with
 | nil=> exact (smul_zero _).symm
 | cons i l ih=> change (Reflect3 σ g b x z i) • K i+ _= _ • (x i • K i+ _); rw [show Reflect3 σ g b x z i= x i*(ρ3 b (z (g o))) from (by unfold Reflect3; rw [u i List.mem_cons_self,sign3]), mul_comm, mul_smul,smul_add]; apply congrArg; exact ih (fun i h=>u i (List.mem_cons_of_mem _ h)) -- tune. match RHS reducible Lat!
include ts e w
lemma Lat_l (z:Key Λζ): ShiftL V (Latζ A l (West3 V σ g x z)) (Latζ B m (East3 ι g y z)) Y.1:=by
 let k:= flipΘ V; let t:= z (g ((boxA V).symm o)); unfold West3 East3; rw [Lat_ζ o σ Z l x k A e, Lat_ζ (δ o) ι g m y false B w] -- tune order
 change t • αLines (Latζ B m y) (flashA V Y.1)= steerZ _ _ _ ((ρ3 k t) • (αLines (Latζ A l x) Y.1))
 rw[scaleCκ,show αLines _ _= _ from ts,sign3, sigh] -- tune
local notation "Lκ"=> MealD H R k t
local notation "Bκ"=> Season_i F R k t σ P A
local notation "Dκ"=> Season_i F R k t ι P B
local notation "PS" s:max=> ΛLine σ W0 Q0 Y (blank3 σ o (PuχQ s)) X0
local notation "QT" s:max=> ΛLine ι W1 Q1 (twistW' V Y) (blank3 ι (δ o) (East3 ι g y s)) X1
include hu h d0 d' v hp cV W U ψ u
set_option maxHeartbeats 350000 in
lemma Lantern (s:Key Λζ)(z:Hub n) :suit_Y V (Canz σ _ (pureX (FrameGrow3 R F H P σ A X W0 Q0 L S k t (p++l))) (West3 V σ g x s) z Y.1)= Canz ι _ (pureX (FrameGrow3 R F H P ι B X' W1 Q1 L T k t (q++m))) (East3 ι g y s) (orbit4 V z) (twistW' V Y).1:=by
 let f(s:Key Λζ):= (suit_Y V (Canz σ _ (pureX (D0 (p++l))) (PuχQ s) z Y.1)).val
 let r(s:Key Λζ):= (Canz ι _ (pureX (D1 (q++m))) (PuχR s) (G z) (Λ).1).val
 let t0:= (Θ).toAddMonoidHom; let r0:= AddMonoidHom.id (FC (Dwell n))
 let Vp:= axle_P t0 Y.1; let Va:= axle_P r0 (Λ).1
 let s0 := fun s:ℂ=> lot_SC V s
 have zv: Injective (Z):= v.comp (boxA V).symm.injective
 have ht:= StrideW P σ X W0 Q0 Lκ L Bκ S Y o p l e Z zv x (flipΘ V) t0 s0 (fun j _ i D=>vWhite ..) (fun j _ i=>aptP0 k R F hp cV Y (σ j) P (A j) i) (fun i=>pave_q0 k R H hp cV Y i) W z -- args/ type λ vWhite infer t macro
 have hk:= StrideW P ι X' W1 Q1 Lκ L Dκ T Λ (δ o) q m w g v y false r0 (fun _ _=>rfl) (fun j _ i D=>vWhite ..) (fun j _ i=>aptP0 k R F hp cV _ (ι j) P (B j) i) (fun i=> pave_q0 k R H hp cV Λ i) U (G z)
 apply Subtype.ext; change f s=r s; suffices h:f=r from congrFun h s
 let Wt(s:Key Λζ):= (θ (Canz σ _ (pureX X0) (PuχQ s) z Y.1)).val
 let U0(s:Key Λζ):=(Canz ι _ (pureX X1) (East3 ι g y s) (orbit4 V z) (Λ).1).val
 have eq:U0=Wt:=funext fun s=>congrArg Subtype.val ((u s).rise z|>.symm) -- tune args. Local W0 shadow risk.M
 let Hx(s:Key Λζ):= Θ (rite3 P Lκ L Bκ Y l (PuχQ s) (PS s) z)
 let Yx(s:Key Λζ):= rite3 P Lκ L Dκ Λ m (PuχR s) (QT s) (orbit4 V z)
 have he:Hx=Yx:=funext fun s=>by
    unfold Hx Yx; rw[←Stir3 k R F Y o P _ L Lκ z σ A l e, ←Stir3 k R F Λ (δ o) P _ L Lκ (G z) ι B m w]; -- tune
    apply InkV3 k R F Y o P _ _ _ L z V H h d0 hp d' cV hu (Lat_l Y V o σ ι A B g _ _ x y e w ts s) _ _ -- require names.Tweak
    exact paper_ζ k R F H Y V P o σ ι A B X _ _ X' W1 Q1 g v L S T p q x y ψ u s
 change Kin (id:Λζ→Λζ) f (Wt+Hx) at ht; change Kin (id:Λζ→Λζ) r (U0+Yx) at hk; rw[eq,←he] at hk
 exact stemEq (canH σ Z zv x (flipΘ V) Vp (ax_s _ t0 Y.1 s0) z _) (canH ι g v y false Va (ax_s _ r0 (Λ).1 (fun _ _=>rfl)) (G z) _) (ht.trans hk.symm)
#print axioms Lantern
include hB qB
set_option maxHeartbeats 350000 in
lemma Northern (s:Key Λζ)(z:Force n) :suit_Y V (Canz σ _ (FrameGrow3 R F H P σ A X W0 Q0 L S k t (p++l)).B (West3 V σ g x s) z Y)= Canz ι _ (FrameGrow3 R F H P ι B X' W1 Q1 L T k t (q++m)).B (East3 ι g y s) (arm4 V z) (twistW' V Y):=by
 let f(s:Key Λζ):= (suit_Y V (Canz σ _ (D0 (p++l)).B (PuχQ s) z Y)).val
 let r(s:Key Λζ):= (Canz ι _ (D1 (q++m)).B (PuχR s) (O z) Λ).val
 let t0:= (Θ).toAddMonoidHom; let r0:= AddMonoidHom.id (FC (Dwell n))
 let Vp:= axle_P t0 Y; let Va:= axle_P r0 Λ
 let s0 := fun s:ℂ=> lot_SC V s
 have zv: Injective (Z):= v.comp (boxA V).symm.injective
 have ht:= StrideB P σ X W0 Q0 Lκ L Bκ S Y o p l e Z zv x (flipΘ V) t0 s0 (fun j _ i D=>vWhite ..) (fun j _ i=>aptP0 k R F hp cV Y (σ j) P (A j) i) (fun i=>pave_q0 k R H hp cV Y i) W hB z -- args/ type λ vWhite infer t macro
 have hk:= StrideB P ι X' W1 Q1 Lκ L Dκ T Λ (δ o) q m w g v y false r0 (fun _ _=>rfl) (fun j _ i D=>vWhite ..) (fun j _ i=>aptP0 k R F hp cV _ (ι j) P (B j) i) (fun i=> pave_q0 k R H hp cV Λ i) U qB (O z)
 apply Subtype.ext; change f s=r s; suffices h:f=r from congrFun h s
 let Wt(s:Key Λζ):= (θ (Canz σ _ (X0).B (PuχQ s) z Y)).val
 let U0(s:Key Λζ):=(Canz ι _ (X1).B (East3 ι g y s) (arm4 V z) Λ).val
 have eq:U0=Wt:=funext fun s=>congrArg Subtype.val ((u s).boat z|>.symm) -- tune args. Local W0 shadow risk.M
 let Hx(s:Key Λζ):= Θ (rime3 P Lκ L Bκ Y l (PuχQ s) (PS s) (ReefB σ X Y (blank3 σ o (West3 V σ g x s)) X0) z)
 let Yx(s:Key Λζ):= rime3 P Lκ L Dκ Λ m (PuχR s) (QT s) (ReefB ι X' (twistW' V Y) (blank3 ι (δ o) (East3 ι g y s)) X1) (arm4 V z)
 have he:Hx=Yx:=funext fun s=>by
    unfold Hx Yx; rw[←StirB3 k R F Y o P _ _ L Lκ z σ A l e, ←StirB3 k R F Λ (δ o) P _ _ L Lκ (O z) ι B m w]; -- tune
    refine InkB3 k R F Y o P _ _ _ _ L z V H h d0 hp d' cV hu (Lat_l Y V o σ ι A B g _ _ x y e w ts s) _ _ ?_ ?_ -- require names.Tweak
    exact paper_ζ k R F H Y V P o σ ι A B X _ _ X' W1 Q1 g v L S T p q x y ψ u s
    exact paper_φ k R F H Y V P o σ ι A B X W0 Q0 X' W1 Q1 g v L S T p q x y ψ u s
 change Kin (id:Λζ→Λζ) f (Wt+Hx) at ht; change Kin (id:Λζ→Λζ) r (U0+Yx) at hk; rw[eq,←he] at hk
 exact stemEq (canH σ Z zv x (flipΘ V) Vp (ax_s _ t0 Y s0) z _) (canH ι g v y false Va (ax_s _ r0 Λ (fun _ _=>rfl)) (O z) _) (ht.trans hk.symm)
#print axioms Northern
end
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
