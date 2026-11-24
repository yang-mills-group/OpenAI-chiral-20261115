import GaugeFieldConstruction.«PessoaΘ3»
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
variable {n:Side}{M N α β:Type}[Fintype M][Fintype N][Fintype α][Fintype β]
variable (V:Sweep n)
local notation "φ"=> orbit4 V
local notation "Ω"=> arm4 V
local notation "Φ"=> actY V
local notation "Θ"=> lotR3 V
local notation "Ωb"=>suit_Y V
variable (R:LeaseQ α n)(S:LeaseQ β n)(A A':Support (More n)→ FC (Dwell n))(K:Support (More n) → M → Cipher n)(K':Support (More n)→N→ Cipher n)(X:M→ Support (More n))(Y:N→Support (More n))
variable (f:α ≃ β)(Fg:M ≃ N)(U U':Orbit n)(p:Hub n)(d e:ℕ)(t:Fin d→α)
variable (H:∀ i,X i= X i) (L:∀ i,Y (Fg i)=actY V (X i))(P:∀ i:α,∀ D:Support (More n), S.issue (f i) (actY V D) U'=suit_Y V (R.issue i D U))
variable (κ:∀ D:Support (More n),∀ i:M,K' (actY V D) (Fg i)=suit_Y V (K D i))(μ:∀ D:Support (More n), A' (actY V D) = lotR3 V (A D))
variable (v w:Force n→ Cipher n)(z:∀ i,w (arm4 V i)=suit_Y V (v i))
lemma Ζmove(q:FC (Dwell n))(l:List (Cipher n)):lotR3 V (scar q l)= scar (lotR3 V q) (l.map (suit_Y V)):=by
 induction l with|nil=>simp[scar]|cons i l ih=>rw[List.map_cons,scar,scar]; unfold bump; rw [map_sub,map_mul,map_mul,ih]; rfl
include P κ μ
lemma body_e (i: Fin e→M)(D:Support (More n)):lotR3 V (BodyX R d e t i D U (A D) (K D))=BodyX S d e (f ∘ t) (Fg ∘ i) (actY V D) U' (A' (actY V D)) (K' (actY V D)):=by
 unfold BodyX; rw[lot_SC]; rw [show ρ3 (flipΘ V) (discount d e)= discount d e from (by simp [discount]),Ζmove]; rw[List.map_append,List.map_ofFn,List.map_ofFn, μ]; apply congrArg; apply congrArg -- map cast ring.
 congr 1
 · congr 1; funext y; exact (κ D _).symm
 congr 1; funext y; exact (P _ _).symm
include L
variable (Pα:Hub n)(pV:orbit4 V p=Pα)
include pV
lemma capR (x:Hub n) : lotR3 V (rippleR R X U d e p t x A K)=rippleR S Y U' d e Pα (f∘ t) (orbit4 V x) A' K':=by
 unfold rippleR; let X':= progressL3 V X Y Fg p Pα e pV L; rw [map_sum]; symm; refine Eq.trans (Equiv.sum_comp X' _).symm ?_; apply sum_congr rfl; intro i _
 rw [innerG V X Y Fg p Pα e pV L i]; simp only [Equiv.apply_eq_iff_eq]; split; next h=>
    let E:= i.val; let E':= Fg ∘ i.val
    change Sault.rind _= lotR3 V (Sault.rind _); have he:=body_e V R S A A' K K' f Fg U U' d e t P κ μ i.val ∅; rw[show actY V ∅= ∅ from Finset.map_empty _] at he; rw [lot_rind]; exact congrArg Sault.rind he.symm
 rw [map_zero]
omit pV P L κ
include z
lemma RopeB_v (t:Force n): lotR3 V (ponyB v p t A)=ponyB w (orbit4 V p) (arm4 V t) A':=by
 unfold ponyB; let H':= BasisRide V p (φ p) true rfl; rw [map_sum]; symm; refine Eq.trans (Equiv.sum_comp H' _).symm ?_; apply sum_congr rfl; intro i _
 rw [← ride_loc V p (φ p) true rfl i]; simp only [Equiv.apply_eq_iff_eq]; split; next g=>
    have hp: (∏ j∈(H' i).val,w j)=Ωb (∏ j∈ i.val,v j):=by
       rw [show (H' i).val=image Ω i.val from tilt_img .., prod_image,map_prod]; apply prod_congr rfl; intro x _; rw[z]; exact Equiv.injective _ |>.injOn -- tune Ω
    unfold CGrant; rw[unit_m, μ, z_spec, hp]; rw [map_sub, lot_rind,map_mul]; simp_rw [joint_m]; split; next g=>
       have he:A' ∅=Θ (A ∅):= (show actY V ∅=∅ from Finset.map_empty _) ▸ μ ∅ -- tune arrow
       rw[he,map_mul,lot_rind]; rfl
    rw[map_zero]; rfl
 rw [map_zero]
include pV P L κ
lemma capB(z':Force n): lotR3 V (rippleB R X U d e p t z' A K v)=rippleB S Y U' d e Pα (f ∘ t) (arm4 V z') A' K' w:=by -- typo east z'
 unfold rippleB; let X':= progressL3 V X Y Fg p Pα e pV L; rw[map_sum]; symm; refine Eq.trans (Equiv.sum_comp X' _).symm ?_; apply sum_congr rfl; intro i _
 rw[innerG V X Y Fg p Pα e pV L i]; symm; refine RopeB_v V _ _ (Legist p X e i) ?_ v w z z'; intro D; exact (body_e V R S A A' K K' f Fg U U' d e t P κ μ i.val D).symm
#print axioms capB
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
