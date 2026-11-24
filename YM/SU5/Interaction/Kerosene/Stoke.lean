import YM.CF.Cadre.Pawn
import YM.CF.Cadre.Grain

/- Single step (sequential Rinse at one seat); in disconnected gas. -/
set_option autoImplicit false
set_option maxHeartbeats 780000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- flow.C root only
variable (x:A) (X:Palot.leaf A)
section
variable {B:Type*}[CommSemiring B]
def Stoke (K:Rinse A B)(Z:leaf A→ Finset A→B)(X:leaf A)(D:Finset A) : B:= ∑ Y:leaf A,∑ G∈drum X Y D,K X D Y (∏ i∈G,Z i (D∩i.val))
lemma stoke_zero (K:Rinse A B)(Z:leaf A→Finset A→B)(C: Finset A)(h:∀ (X Y:leaf A) U v, ¬ C⊆ Y.val→ K X U Y v=0)(p:¬ C⊆X.val) : Stoke K Z X D=0:= by unfold Stoke; apply sum_eq_zero; intro Y _; refine sum_eq_zero fun P w=> h _ _ _ _ (fun v=>p (subset_trans v ((drum_p ..|>.mp w).2.2 ▸ subset_union_left)))
/- first installment vs. exactly all hooks. Ring.For Q H expansion. -/
lemma stoke_energy (K:Rinse A B)(Z:leaf A→Finset A→B) : Stoke K Z X D=(if D.Nonempty then 0 else K X ∅ X 1)+∑ Y:leaf A,∑ P∈drum X Y D∩farW A,K X D Y (∏ i∈P,Z i (D∩i.val)):=by
 -- adapts pingT
 have he(Y:ΣA):∅∈drum X Y D ↔ X=Y∧D=∅:=by rw [drum_p]; simp [flow,robe, Subtype.ext_iff,and_comm]
 have hv(Y:ΣA):drum X Y D∩ farW A=(drum X Y D).erase ∅:= by
    ext i; rw [mem_inter,mem_erase]; change _∧_ ↔ _∧_; unfold farW; rw [show (i∈ univ.filter (fun G:ΣG=>G.Nonempty)) ↔_ from mem_filter]; simp only [mem_univ,true_and,Finset.nonempty_iff_ne_empty,and_comm]
 let U(Y:ΣA)(G:ΣG):= K X D Y (∏ i∈G,Z i (D∩i.val))
 unfold Stoke; simp_rw [hv]; by_cases t:D.Nonempty
 · rw [if_pos t,zero_add]; apply sum_congr rfl; intro i _; rw [erase_eq_of_notMem (fun q=>t.ne_empty ((he _).mp q).2)]
 rw [if_neg t]; have h:D=∅:= Finset.not_nonempty_iff_eq_empty.mp t
 have ht(Y:ΣA): (∑ G∈drum X Y D, U Y G)= (if Y=X then K X ∅ X 1 else 0)+ ∑ G∈(drum X Y D).erase ∅, U Y G:=by
    split_ifs with p; · rw [←add_sum_erase _ _ ((he _).mpr ⟨p.symm,h⟩)]; unfold U; rw [prod_empty,p,h] -- tune
    rw [erase_eq_of_notMem fun t=>p (((he Y).mp t).1.symm),zero_add]
 change (∑ Y:ΣA,∑ G∈drum X Y D,U Y G)= K X ∅ X 1+∑ Y:ΣA,∑ G∈(drum X Y D).erase ∅, U Y G; simp_rw [ht,sum_add_distrib]; simp -- tune
lemma stokingProd (V K:Palot.leaf A→B)(hz:∀ (X Y:Palot.leaf A), Disjoint X.val Y.val → K X * K Y=0) (H:flow A F):∏ j∈F,(V j+K j)= (∏ j∈F,V j)+∑ X∈F,K X *∏ j∈F.erase X,V j:=by
 induction F using Finset.induction_on with
 |empty=> simp
 |insert i S h ih=>
    rw [prod_insert h,ih (flow_m H (subset_insert _ _)),prod_insert h,sum_insert h,erase_insert h]
    let U(X:leaf A):= K X *∏ j∈ S.erase X,V j
    let T:=∑ X∈S,U X
    have hp:K i*T=0:=by unfold T; rw [mul_sum]; refine sum_eq_zero fun j v=>?_ ; unfold U; rw [←mul_assoc,hz i j (H i (mem_insert_self ..) j (mem_insert_of_mem v) (ne_of_mem_of_not_mem v h).symm),zero_mul] -- orientation
    have he: V i*T=∑ X∈S,K X* ∏ j∈ (insert i S).erase X,V j:=by unfold T U; rw [mul_sum]; refine sum_congr rfl fun j v=>?_ ; rw [erase_insert_of_ne (ne_of_mem_of_not_mem v h).symm, prod_insert (fun a=>h (mem_erase.mp a).2)]; ring
    rw [←he]; change (V i+K i) * (_+T) = _; rw [add_mul,mul_add,mul_add,hp,add_zero]; ring -- zero simplify
lemma rankOne (Z K:Palot.leaf A→B)(V:Palot.leaf A→Palot.leaf A→Finset (Palot.leaf A)→ B) (p:∀ X:Palot.leaf A,K X=∑ Y:Palot.leaf A, ∑ F∈ drum X Y (O∩X.val),V X Y F) (hp:∀ (X Y:Palot.leaf A), Disjoint X.val Y.val → K X * K Y=0) : hGas O (Z+K)= hGas O Z+∑ Y:ΣA,∑ G∈ stream O,V (glueV Y (grab Y G)) Y (grab Y G)* ∏ j∈farR Y G,Z j:=by
 let u(F:ΣG)(X Y:ΣA):=(∑ T∈drum X Y (O∩X.val),V X Y T)*∏ j∈F.erase X,Z j
 have he(F:ΣG)(v:F∈stream O):(∏ j∈F,(Z+K) j)=(∏ j∈F,Z j)+ ∑ Y:ΣA,∑ X∈F,u F X Y:=by
    rw [show (∏ j∈F,(Z+K) j)=_ from stokingProd F Z K hp (mem_filter.mp v).2.1]; rw [sum_comm (s:=Finset.univ)]; apply congrArg (_+·); exact sum_congr rfl fun i _=> by rw [p,sum_mul]
 change (∑ F∈stream O,_)=(∑ F∈stream O,_) + _; rw [sum_congr rfl he,sum_add_distrib,sum_comm (s:=stream O) (t:=univ)]; apply congrArg (_+·); refine sum_congr rfl fun i _=>?_ ; exact yul i O (fun X G=>V X i G) (fun H=>∏ j∈H,Z j)
lemma stoke_pair (K:Palot.leaf A→B)(hz:∀ Y:Palot.leaf A,x∉ Y.val→K Y=0)(H:Disjoint X.val Y.val):K X*K Y=0:= by
 by_cases h:x∈ X.val;
 · rw [hz Y (disjoint_left.mp H h),mul_zero]
 rw [hz X h,zero_mul]
end
open Fock Pastry Sault
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I](W: Palot.leaf A→ Finset I)(M: Palot.leaf A→ FC I)(R Z: Palot.leaf A→ Dough I)
variable (C:Palot.leaf A→ Palot.leaf A→ Finset (Palot.leaf A)→ Dough I)(e:∀ X:leaf A,Z X=∑ Y:leaf A,∑ F∈ drum X Y (O∩X.val), C X Y F)
variable (η:∀ X Y:leaf A,∀ G∈drum X Y (O∩X.val),(C X Y G).val=Sault.rind (M Y * (∏ t∈G,R t).val))
variable (ω:∀ X:leaf A,Fock.Sector (W X) false (M X)) (t:∀ X Y:leaf A,Disjoint X.val Y.val→ Disjoint (W X) (W Y))(hU:∀ X, Flour (W X) (R X).val)
local notation "gale" S:max=> ∏ i∈S,R i
include η ω t hU
private lemma wakening (g:F∈stream O):let G:=grab Y F; let T:=farR Y F
 (C (glueV Y G) Y G* (gale T)).val=Sault.rind (M Y*(gale F).val):=by
 intro G T; have he:Disjoint (W Y) (T.biUnion W):= Finset.disjoint_left.mpr fun {i} l p=>by obtain ⟨x,h,u⟩:=mem_biUnion.mp p; exact Finset.disjoint_left.mp (t Y x ((pact Y F x).mp h).2) l u
 let A0:=gale T; let B0:=gale G
 have hx:(gale F)=A0* B0:=by nth_rw 1 [←race Y F]; rw [prod_union (caddy ..),mul_comm] -- tune includes R
 rw [mul_comm (C ..),hx]; change A0.val*_=Sault.rind (M Y*(A0.val*B0.val)); rw [η _ _ _ (drive Y O F g).1]
 exact (Sault.pert (ω Y) (span_v R (F:=T) (fun j v=> (hU j).lift (subset_biUnion_of_mem W v))) he B0.val).symm -- signature param
include e
lemma stoke_hGas (u:∀ X:leaf A,x∉X.val→Z X=0) : acts (hGas O (R+Z)).val (vacuum I)=acts (1+ ∑ Y:Palot.leaf A,M Y) (acts (hGas O R).val (vacuum I)):=by
 rw [rankOne O R Z C e (fun X Y=> stoke_pair Y x X Z u),Subalgebra.coe_add, handle, act_add,act_add,act_one] -- tune
 apply congrArg (acts (hGas O R).val (vacuum I)+·)
 rw [act_sum,act_sum]; apply sum_congr rfl; intro i _; rw [handle,act_sum]; change _= acts (M i) (acts (∑ G∈stream O,(gale G)).val _); rw [handle,act_sum,map_sum]; refine sum_congr rfl fun g v=>?_ ; rw [wakening i O g W M R C η ω t hU v,tileL,act_mul]
end YM.CF.Cadre
#print axioms YM.CF.Cadre.stoke_hGas
