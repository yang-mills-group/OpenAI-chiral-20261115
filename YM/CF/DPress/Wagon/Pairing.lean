import YM.CF.DPress.Wagon.Earn
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Race.Ribbon
variable {T:Race n L}(X:Ribbon T){b c:Bool}{n0 k:ℕ}(p: X.Frame k)(q:X.Frame (k+k))
open Credit
local notation "Xf"=> Fixed.Test n
local notation "P"=> X.stripe p
local notation "W"=> X.stripe q
variable {a:ℤ}
-- Reflect-cost bound duplication step.Style Loom throughput.HPol.Book
lemma fold_time : X.Γtime (k+k)=X.Γtime k+X.Γtime k:=by unfold Γtime runB mulT; ring
lemma fold_arc {U V:Xf}(h:(X.stripe p).part a b (!b) U)(v:(X.stripe p).part (a+X.Γtime k) (!b) (!b) V): X.arc (a+X.mulT k) (k+k) (U* V):=by
 have he:= X.straightR p h; have hz:= X.straightL p v; apply X.compound he; rw [show (a+ (X.mulT k:ℤ))+(X.runB k:ℤ)=a+ X.Γtime k from (by unfold Γtime; omega)]; exact hz
lemma gleeful(r:ℕ)(m:Bool){H:Xf} (v:Credit (P) a b (List.replicate (r+r) (!b)) H):∃ F:List Bool,F.length=r∧ Credit (W) (a+X.mulT k) m F H:=by
 induction r generalizing a H m with
 | zero=> rw [show H=1 from nil_p.mp v]; exact ⟨[],rfl,zero _ _⟩
 | succ i ih=>
    rw [show i+1+(i+1)= (i+i)+1+1 from (by omega)] at v; obtain ⟨A,B,vK,h,rfl⟩:=pick (show Credit _ _ _ ((!b)::List.replicate (i+i+1) (!b)) _ from v); obtain ⟨Y,Z,Hq,H,rfl⟩:=pick (show Credit _ _ _ ((!b)::List.replicate (i+i) (!b)) _ from h); change Credit (P) (a+ (X.Γtime k:ℤ)+(X.Γtime k:ℤ)) _ _ Z at H; rw [Bool.not_not] at H; obtain ⟨Q,V,t⟩:= ih (!m) H;
    refine ⟨m::Q,?_,?_⟩; · rw [List.length_cons,V]
    rw [← mul_assoc]; refine Credit.next (X.pinL q _ m (X.fold_arc p vK Hq)) ?_; change Credit (W) (_ +(X.Γtime (k+k):ℤ)) _ _ _; rw [X.fold_time,Nat.cast_add]; exact ((by convert t using 1; abel))
-- rotate homogeneous to a right-first mark when facing out rather than in.
lemma forecast (r:ℕ)(t:(r+r)*X.Γtime k=T.η)(F:Xf)(h:Credit (P) a b (List.replicate (r+r) c) F):∃ (u:List Bool)(a:ℤ)(d:Bool),u.length=r∧ Credit (W) a d u F:=by
 by_cases i:c=!b; · subst c; obtain ⟨v,t,h⟩:= X.gleeful p q r b h; exact ⟨v,_,b,t,h⟩
 have he:c=b:=by cases b<;>cases c<;>simp_all
 have hp:0<r:=by by_contra! e; have hp:T.η>0:= T.height_p; have ht:r+r=0:= (by omega); rw [ht,zero_mul] at t; omega -- parse
 subst c; let B':= List.replicate (r+r-1) b; have hz:[b]++B'= List.replicate (r+r) b:=by
    rw [←show r+r-1+1=r+r from (by omega)] -- maybe pattern
    rfl
 have hv: Credit (P) (blockP (P) a [b]) (!b) (B'++[b]) F:= rotate_Q (s:=[b]) (t:=B') (hz.symm ▸ h) (by rw [hz,blockP,List.length_replicate]; rw [show (P).w=X.Γtime k from rfl,t]) (by rw [hz,List.length_replicate]; exact ⟨r,rfl⟩)
 have hv': B'++[b]=[b]++ B' :=by -- rewrite via replicate_add
    unfold B'; rw [show [b] = List.replicate 1 b from rfl, ← List.replicate_add,← List.replicate_add]; rw [Nat.add_comm]
 rw [hv',hz] at hv; obtain ⟨v,t,h⟩:= X.gleeful p q r (!b) (show Credit _ _ (!b) (List.replicate (r+r) (!!b)) F from (by rw [Bool.not_not]; exact hv)); exact ⟨_,_,_,t,h⟩
end Race.Ribbon
end YM.CF.DPress.Wagon
