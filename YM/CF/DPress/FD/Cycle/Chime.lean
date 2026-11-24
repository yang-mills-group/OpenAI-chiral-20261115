import YM.CF.DPress.FD.Cycle.Pane
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD.Cycle
open List Filter Set
open scoped Topology BigOperators ENNReal Classical
open Function
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] (S:Equiv.Perm I) (W:Equiv.Perm J)(h:∀ i:I,S i≠ i)
variable {x y:Skin I}{P Q: I→Finset C}
abbrev field(U:Finset (Coil I)):= U.biUnion cave
abbrev ΔP(U:Finset (Coil I))(u:Skin I):ℝ := ∏ i∈U,coilW i u
def mass(S:Equiv.Perm I)(x:Skin I):=ΔP (loops S) x
lemma burst {u:Coil I}(v:u∈loops S) (P:I→ Finset C)(x : Skin I): ∑ j∈Fill (cave u) P x, coilW u j= worth u P:=by
 obtain ⟨i,h,rfl⟩:=Finset.mem_image.mp v; rw [vote,cave,_root_.Cycle.coe_toFinset]; exact (stamp P x _ (viewP S i) θ).symm
lemma boot_E {u:Coil I}(v:u∈loops S) (p:∀ i∈ cave u,x i=y i): coilW u x=coilW u y:=by obtain ⟨i,t,rfl⟩:=Finset.mem_image.mp v; rw [← coilW_C x _ (vote S i).symm,← coilW_C y _ (vote S i).symm]; refine congrArg θ (List.map_congr_left ?_); exact fun i' v=> p i' (by rw [vote,cave,_root_.Cycle.coe_toFinset]; exact mem_toFinset.mpr v)
lemma scan (U:Finset (Coil I))(v:U⊆ loops S)(z:Skin I) : ∑ i∈ Fill (field U) P z,ΔP U i= ∏ i∈U,worth i P:=by
 induction U using Finset.induction_on generalizing z with
 |empty=> simp [field,ΔP]
 |@insert i U hi ih=>
    let V:=field U; let D:=cave i; have ht:U⊆ loops S:= Finset.Subset.trans (Finset.subset_insert i U) v; have hx:= v (Finset.mem_insert_self i U); have hz: Disjoint D V:=by
       refine Finset.disjoint_left.mpr fun j t y=>?_ ; obtain ⟨i',q,h⟩:= Finset.mem_biUnion.mp y; exact Finset.disjoint_left.mp (pairwise S hx (ht q) (fun f=>hi (f ▸ q))) t h -- hm
    have he(y:Skin I):∑ j∈Fill V P y,ΔP (Insert.insert i U) j= coilW i y * ∏ i∈U,worth i P:=by
       rw [←ih ht (z:=y),Finset.mul_sum]; exact Finset.sum_congr rfl fun j t=>by rw [ΔP,Finset.prod_insert hi, boot_E S hx (x:=j) (y:=y) (fun k v=> ((report ..).1 t).2 k (Finset.disjoint_left.mp hz v))] -- Read order
    rw [field,Finset.biUnion_insert,block P z hz, (show (fun y:Skin I=>∑ j∈Fill V P y,ΔP (Insert.insert i U) j)=_ from funext he),←Finset.sum_mul,Finset.prod_insert hi, burst S hx] -- rw pattern `field` vs V.
local notation "A_"=>Finset.univ
lemma sphere : field (loops S)=Finset.univ:= Finset.eq_univ_of_forall fun i=> Finset.mem_biUnion.mpr ⟨visit S i, lands S i,(patron _ (lands S i)).mpr rfl⟩
lemma mask(P:I→Finset C)(S':Equiv.Perm I) : (∑ x:Skin I with (∀ i, x i∈ P i), mass S' x)=∏ i∈loops S',worth i P:=by
 let q:=scan (P:=P) S' (loops S') (Finset.Subset.refl _) (fun _=>0); rw [sphere, Fill] at q; simpa only [mass,Finset.mem_univ,not_true, false_implies, implies_true,and_true,true_implies] using q -- defeq mass
include h
lemma unit : ∑ x:Skin I, mass S x=1:=by
 have hp:=mask N S; simp only [N,Finset.mem_univ,implies_true,Finset.filter_true] at hp; rw [hp]; apply Finset.prod_eq_one; intro i t; obtain ⟨v,p,rfl⟩:=Finset.mem_image.mp t; have he:= hefty S v (h v); change 1<(view S v).length at he; exact cycle_one _ he
variable (P Q)
local notation "fP"=>EmptyP
lemma merit_F (u:∀ i:I,EmptyP P i ∨ EmptyP Q i)(v:∀ i:I,(EmptyP P i∨EmptyP Q (S i))∧(EmptyP Q i ∨ EmptyP P (S i))) :(∑ x:Skin I with (∀ i, x i∈ joint P Q i), mass S x)=(∑ x: Skin I with (∀ i,x i∈P i),mass S x)*(∑ x:Skin I with (∀ i,x i∈Q i),mass S x):=by
 simp_rw [mask,←Finset.prod_mul_distrib]; refine Finset.prod_congr rfl ?_; intro j m; obtain ⟨j,t,rfl⟩:= Finset.mem_image.mp m
 let T:=visit S j; let g:= view S j; let E(i k:I):Prop:=(EmptyP P i∨EmptyP Q k)∧ (EmptyP Q i∨EmptyP P k); have he: T.Chain E:=(periodicOrbit_chain _).2 (fun i p=>by rw [Function.iterate_succ_apply']; exact v (S^[i] j))
 apply budgets P Q g (hefty S j (h j)) (fun i _=> u i); intro y z h; apply chain_lineB T he; rw [show T=(g:Coil I) from vote .., show g=y++z from h]; exact _root_.Cycle.coe_eq_coe.mpr List.isRotated_append
omit h
lemma positive : 0≤ mass S x:=by
 refine Finset.prod_nonneg fun i v=>?_ ; obtain ⟨i,v,rfl⟩:=Finset.mem_image.mp v; rw [←coilW_C x _ (vote S i).symm]; exact div_nonneg (tall_nonneg true _) (mul_nonneg (by positivity) (pBank _).le) -- Nat cast issue
-- support proper coloring. read first edge x,Sx at i. needed. 
include h
lemma born (p: mass S x≠0)(i:I): x i≠ x (S i):=by
 let g:= view S i; have he: coilW (visit S i) x ≠ 0:=by intro v; exact p (Finset.prod_eq_zero (lands S i) v)
 rw [←coilW_C x _ (vote S i).symm] at he
 have hp: 1< minimalPeriod S i:=periodicOrbit_length ▸ hefty S i (h i); by_contra U; apply he; unfold θ cP; rw [free]; exact zero_div _
 intro k; have hh:= (clean_line _ k); let Y:=g.map x; have hY: 0+1<Y.length:=by unfold Y g view; simp [hp]
 have e: Y[0]≠Y[0+1]:= hh.getElem 0 hY; exact e (by simpa [Y,g,view] using U) -- cont
end YM.CF.DPress.FD.Cycle
