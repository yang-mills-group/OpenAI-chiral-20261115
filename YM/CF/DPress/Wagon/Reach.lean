import YM.CF.DPress.Wagon.Post
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
namespace Buses
variable {N P:Side}{S:BandWidth}{k r:ℕ}(A:Bands (More N) S)(p:Sign S L k r) {c:ℝ}(u:1≤c)
open Race Race.Ribbon Race.Credit
local notation "Ψ"=> mint A p
local notation "Uq"=> sharp A p u
local notation "Sq"=> stripe (sharp A p u) (sit_T A p u)
def bill (i:ℕ) : List A.Index:= (List.range i).map Nat.cast
lemma size_bill(i:ℕ): (bill A i).length=i:=by simp [bill]
lemma bill_add(i:ℕ):bill A (i+1)=bill A i ++[(i:A.Index)]:=by simp [bill,List.range_succ]
lemma positions : (bill A A.Q.val).Nodup ∧∀ i:A.Index,i∈bill A A.Q.val:=by
 refine ⟨List.Nodup.map_on ?_ List.nodup_range,?_⟩ -- lemma tune
 · intro x i y j p; change ((x:A.Index))=(y:A.Index) at p; exact (ZMod.val_natCast_of_lt (List.mem_range.mp i)).symm.trans ((congrArg ZMod.val p).trans (ZMod.val_natCast_of_lt (List.mem_range.mp j))) -- inspect
 intro i; exact List.mem_map.mpr ⟨i.val,List.mem_range.mpr (ZMod.val_lt i),ZMod.natCast_zmod_val _⟩
variable {P':A.Index→ Fixed.Test N}(f: ∀ i, IsMark (A.band i) (P' i) c)
include f
lemma shout (i:ℕ)(h:i ≤ A.Q.val): ∃ s:List Bool,s.length=i∧ Credit (Sq) 0 false s ((bill A i).map P').prod :=by
 induction i with
 | zero=> exact ⟨[],rfl,.zero ..⟩
 | succ i ih=>
    obtain ⟨s,g,v⟩:= ih (Nat.le_trans (Nat.le_succ _) h); have hp:i<A.Q.val:=h; let w:=turned s.length false; refine ⟨s++[w],by simp [g],?_⟩; rw [bill_add,List.map_append,List.prod_append]; apply companion v; rw [show blockP (Sq) 0 s=lexp k (i:A.Index).val from (by unfold lexp blockP; change _+ (↑(s.length*(1*k+1*1)):ℤ)= _; rw [ZMod.val_natCast_of_lt hp,g]; push_cast; ring_nf)]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; apply pin (tape A p u _ _ w (f _)) -- tune HP
lemma peak {ℒ:Fixed.Test N→ℝ}(E:(mint A p).Bound ℒ){q:ℕ}{x y:ℝ}(w:2^q=k)(v1:2^(q+1)∣ A.Q.val) (v:0<x)(h:0<y)(g:ℒ 1≤ x^(mint A p).η)(t:(sharp A p u).allE y ℒ): ℒ (((bill A A.Q.val).map P').prod) ≤ (x*y^k)^A.Q.val:=by
 obtain ⟨s,l,e⟩:= shout A p u f _ le_rfl; let u':= (sit_T A p u); have H: 2^q*1* (Uq).b= (Uq).P:=by change _*1=k; rw [mul_one,mul_one,w]
 have ht: (Uq).growth x y 1=x*y^k:=by change x^(1* (1:ℕ))*y^(1*k)=_; rw [one_mul,one_mul,pow_one]
 rw [←ht]; exact (Uq).lift_clock E v h g t q 1 A.Q.val H u' (board_v A p u) v1 s l 0 false _ e
end Buses
end YM.CF.DPress.Wagon
