import YM.CF.Cadre.Dash
import YM.CF.Sault.Cider
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
open Fock Pastry Sault PowerSeries
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I](W: leaf A→ Finset I)(K: leaf A→ FC I)(R: Palot.leaf A→ PowerSeries (Dough I))
local notation "ℊ"=>PowerSeries (Dough I)
variable (C:Palot.leaf A→ Palot.leaf A→ Finset (Palot.leaf A)→ PowerSeries (Dough I))(e:∀ X:leaf A,derivative (Dough I) (R X)=∑ Y:leaf A,∑ F∈ drum X Y (O∩X.val), C X Y F)
variable (η:∀ X Y:leaf A,∀ G∈drum X Y (O∩X.val),∀ i:ℕ,(coeff i (C X Y G)).val=Sault.rind (K Y * (coeff i (∏ t∈G,R t)).val))
variable (ω:∀ X:leaf A,Fock.Sector (W X) false (K X)) (t:∀ X Y:leaf A,Disjoint X.val Y.val→ Disjoint (W X) (W Y))(hU:∀ X i, Flour (W X) (coeff i (R X)).val)
abbrev gal (U:Finset ΣA)(P:ΣA→ℊ):=∏ j∈U,P j
lemma handle {ι:Type*}(S:Finset ι)(U:ι→Dough I): (∑ i∈S,U i).val=∑ i∈S,(U i).val:=map_sum (Subalgebra.val (Dough I)) ..
lemma span_v {T:Finset I}{F:Finset ΣA}(Z:ΣA→ Dough I)(g:∀ i∈F,Flour T (Z i).val):Flour T (∏ i∈F,Z i).val:=by induction F using Finset.induction_on with| empty=>rw [prod_empty]; exact Flour.grainE|insert i F h ih=>rw [prod_insert h]; exact (g i (mem_insert_self ..)).mul (ih fun j q=> g j (mem_insert_of_mem q))
include hU
lemma crest(n:ℕ): Flour ((farR Y F).biUnion W) (coeff n (gal (farR Y F) R)).val:=by
 unfold gal; rw [coeff_prod,handle]; apply Flour.sum; intro i _; exact span_v (fun j=> coeff (i j) (R j)) fun j t=>(hU j _).lift (subset_biUnion_of_mem W t)
include η ω t
lemma lantern (g:F∈stream O)(i:ℕ):let G:=grab Y F; let T:=farR Y F
 (coeff i (C (glueV Y G) Y G*gal T R)).val=Sault.rind (K Y*(coeff i (gal F R)).val):=by
 intro G T; have he:Disjoint (W Y) (T.biUnion W):= Finset.disjoint_left.mpr fun {i} l p=>by obtain ⟨x,h,u⟩:=mem_biUnion.mp p; exact Finset.disjoint_left.mp (t Y x ((pact Y F x).mp h).2) l u
 have hv:gal F R=gal T R*gal G R:=by
    unfold gal; nth_rw 1 [←race Y F]; rw [prod_union (caddy ..),mul_comm]
 rw [mul_comm _ (gal T R),coeff_mul,hv,coeff_mul,handle,handle,mul_sum,Sault.rind,map_sum]; apply sum_congr rfl; intro j _; let a:= (coeff j.1 (gal T R)).val; let b:=(coeff j.2 (gal G R)).val
 change a*(coeff j.2 (C (glueV Y G) Y G)).val=Sault.rind (K Y * (a*b)); rw [η _ _ _ (drive Y O F g).1]; exact (Sault.pert (ω Y) (crest Y F W R hU j.1) he b).symm
abbrev pose(Z:ℊ)(i:ℕ):= acts (coeff i Z).val (vacuum I)
include e
lemma scion (i:ℕ):let U:= hGas O R; pose (derivative (Dough I) U) i=acts (∑ Y:ΣA,K Y) (pose U i):=by
 intro U; have he:derivative (Dough I) U= _:= hymn O R C e; let F(X:ΣA)(P:ΣG):=C (glueV X (grab X P)) X (grab X P)* gal (farR X P) R
 unfold pose; rw [he,map_sum,handle,act_sum,act_sum]; refine sum_congr rfl fun i' _=>?_ ; rw [show U=∑ T∈stream O, gal T R from rfl,map_sum, map_sum,handle, handle,act_sum,act_sum, map_sum]; apply sum_congr rfl; intro G g
 change acts (coeff _ (F i' G)).val (vacuum _)= _; rw [show (coeff _ (F _ _)).val= _ from lantern i' O G W K R C η ω t hU g i,tileL,act_mul]
end YM.CF.Cadre
