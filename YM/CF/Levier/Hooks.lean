import YM.CF.Levier.Crest
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable (U:UNI SpinIdx) (N)
abbrev siteU(s:Shape)(p:Bool)(U:UNI SpinIdx)(N:Side):=prepU s U (xtra p) N
lemma site_ui : siteU a b U N= prepU a U inert N:=rfl -- v always 1
lemma white_p:whiten b (prepU a U inert N)=prepU a (whiten b U) inert N:=by
 cases b; rfl
 apply Subtype.ext; ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩; change star ((mealU a U inert N).val (x,i,j) (y,k,l))=(mealU ..).val (x,i,j) (y,k,l)
 unfold mealU portX; dsimp only; rw [jump_apply,jump_apply]; split; next h=>
   have hp : cc (milU a U inert x).val=(milU a (whiten true U) inert x).val:=by change cc (a.payA x • _) =a.payA x • _; rw [cc_smul, Shape.real_payA]; congr 1; change cc (U.val ⊗ₖ (1:Op Slot))=_; rw [op_cc_kron,cc_one]; rfl
   exact Matrix.ext_iff.mpr hp _ _
 rw [star_zero]
lemma turns(W:UNI SpinIdx)(x:Shape)(t:Bool): siteU x t W N * whiten t (siteU a b U N)=siteU (joinX a x) (b.xor t) (W*whiten t U) N:=by rw [site_ui,site_ui,site_ui,white_p,kio]
-- representation phase via periods
lemma pays_eq(s:Signed)(p q:Cover)(X:Site N)(h:wrap N p=wrap N q):let t:=fee (periods N p - periods N q); (Shape.mk s p).payA X=t * (Shape.mk s q).payA X:=by
 intro t; suffices hx: (Shape.mk s p).rent X=periods N p-periods N q+(Shape.mk s q).rent X by rw [Shape.payA,hx, dues]; rfl -- tune
 apply nsmul_right_injective (M:=Cover) N.property.ne'; let Y:= Shape.mk s p; let Z:=Shape.mk s q; have he : Y.mills N X= Z.mills N X:=by
    unfold Y Z Shape.mills Shape.flee; simp only [map_add,h]; rfl -- dune def depends s only
 have hp:=Shape.vibes Y X; have hx:=Shape.vibes Z X; rw [he] at hp; have ht:=carrying N p; rw [h] at ht
 have hk: Y.flee (natural X)- Z.flee (natural X)=p-q:=by
    apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide); change (2:ℕ) • _= (2:ℕ) • _; have hl:=Y.mote (natural X); have hm:= Z.mote (natural X); unfold Shape.motion at hl hm; change _+ 2 • p=_ at hl; change s.act _+2 • q = _ at hm; change s.act _+ _=_ at hl; rw [smul_sub,smul_sub]; linear_combination (norm:=abel) hm-hl
 change N.val • Y.rent X = N.val • (_+Z.rent X); rw [smul_add, smul_sub]; linear_combination (norm:=abel) hp - hx - ht + (carrying N q) + hk -- signs
lemma utu(s:Signed)(p q:Cover)(h: wrap N p=wrap N q): (siteU (Shape.mk s p) b U N).val= fee (periods N p-periods N q) • (siteU (Shape.mk s q) b U N).val:=by
 ext ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩; rw [Matrix.smul_apply]; let Y:= Shape.mk s p; let Z:= Shape.mk s q; change (mealU Y U _ N).val (x,i,j) (y,k,l)=_ • (mealU Z U _ N).val (x,i,j) (y,k,l)
 have he : Y.mills N x= Z.mills N x:=by unfold Y Z Shape.mills Shape.flee; simp only [map_add,h]; rfl
 unfold mealU portX; dsimp only; rw [jump_apply,jump_apply,show Tofu Y _ x=Tofu Z _ x from he]; split; next hp=> change (Y.payA x • (spinQ U (xtra b)).val) (i,j) (k,l)= _ • (Z.payA x • (spinQ U (xtra b)).val) (i,j) (k,l); rw [show Y.payA x= _ from pays_eq N s p q x h]; simp [Z, ←mul_assoc]
 simp
end YM.CF.Levier
