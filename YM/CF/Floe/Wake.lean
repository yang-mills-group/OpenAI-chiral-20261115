import YM.CF.Drapes.Open
import YM.CF.Phase.LocalBills
/-! Continuation. Reflection startup synergy. Analytic neighborhoods of tenant slots.
    Beware requirement own uniform & same CAB on periods later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
abbrev S0:= SpinIdx × Slot
abbrev H0:=Op S0
abbrev UnitS:=UNI S0
abbrev Ra (N:Side) (H:Type*):= Edges (More N)→ Bool→ H
abbrev Rb (N:Side) (H:Type*):= Bool → Site N→ Bool → H
abbrev BayP(N:Side):=Ra N H0 × Rb N H0
variable{N:Side}{a b d:ℝ}
abbrev αp(x:E):UnitS:=⟨color matter x,color_mem ..⟩
def vow (x:H0)(b:Bool):H0:=if b then x else star x
def skin(i: Tenant.Input N):BayP N:=(fun x=> vow (color matter (i.1 x)), fun b c=>vow (localPair (i.2 b c)))
-- gauge/copy rotations
def γL (U V:UnitS)(M: Bool →H0)(p:Bool):= if p then U.val*M p*star V.val else V.val*M p*star U.val
lemma shift_γ (U V:UnitS)(X:H0):γL U V (vow X)=vow (U.val*X*star V.val):=funext fun b=>by cases b <;>simp [γL,vow,mul_assoc]
lemma polar_γ (U V:UnitS)(X Y:Bool→H0)(b:Bool):‖γL U V X b-γL U V Y b‖=‖X b-Y b‖:=by
 have he(U V:UNI S0): ‖U.val * X b*star V.val-U.val*Y b*star V.val‖= ‖X b-Y b‖:=by rw [←sub_mul,←mul_sub]; exact Eq.trans (CStarRing.norm_mul_coe_unitary (U.val* (X b-Y b)) (star V)) (CStarRing.norm_coe_unitary_mul ..)
 cases b<;> exact he ..
def carryP(g:Geometry N)(x: BayP N):BayP N:=(fun i=> γL (αp (g i.1)) (αp (g (i.1+ step i.2))) (x.1 i),fun b c=>γL (αp (g (node c))) (ccU (αp (g (node c)))) (x.2 b c)) -- ccU maybe expects val
lemma scene (g: Geometry N)(u: Tenant.Input N): carryP g (skin u)=skin (flipR g u):=by
 refine Prod.ext ?_ ?_
 · change (fun i=>_)=(fun x=>_); ext i : 1; dsimp only [carryP,skin,flipR]; rw [shift_γ]; rw [Lattice.gauge,color_mul,color_mul,color_inv]
 change (fun b c=>_)=(fun b c=>_); ext b c : 2; dsimp only [carryP,skin,flipR,turnX]; rw [shift_γ,localPair_turn]; rw [show star (ccU (αp (g (node c)))).val= Matrix.transpose ((αp (g (node c))).val) from by generalize αp (g (node c))=V; ext i j; change star (star (V.val j i)) = _; rw [star_star]; rfl]; rfl
lemma pne {I:Type*}[Fintype I]{F:Type*}[NormedAddCommGroup F]{x y:I→F}(h:∀ i, ‖x i‖=‖y i‖): ‖x‖=‖y‖:=by
 apply le_antisymm <;> apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
 · exact fun i=>(h i).trans_le (norm_le_pi_norm y i)
 exact fun i=>(h i).symm.trans_le (norm_le_pi_norm x i)
lemma thinP (g: Geometry N)(x y:BayP N):‖carryP g x-carryP g y‖=‖x-y‖:=by
 rw [Prod.norm_def,Prod.norm_def]
 refine congrArg₂ max ?_ ?_; exact pne fun i=> pne fun b=>polar_γ _ _ _ _ _
 exact pne fun b=>pne fun j=>pne fun d=>polar_γ _ _ _ _ _
end YM.CF.Floe
