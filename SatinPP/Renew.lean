import SatinThinRenew
/-! # Dual volume renewal. Controller on the projection f heights earlier than measured Mark. Geometry proof adapts Afterglow.twice. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
attribute [local instance] opCStarAlgebra

open CF.Pannier.Chancel
variable {N B:Side}{D:ℕ}
namespace Again
/-! # Physical checker procedure. Only its root structure is tracked in CS!
Derived from CF.Pannier.Chancel.Cliplet.StageTw; supports even much richer v Marks under these constraints. -/
variable {M:Side}(p:Site N→ Mark M)(F:Mark M→ℂ)
-- no nonempty, for theorem
variable {T k w b:ℕ}{q:ℤ→ℤ}{d:ℝ}
variable {p F}(h:GraceA B D T p F q w)
variable (l:List (Site N))

include h
omit h in
private lemma goldi {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
lemma renewed_transverse (j:Axis)
    (v:outdoor T l)(e:∀ i,i≠j → cows i (upperRoll l) b)
    (u:b+plusAgain B D≤ N.val)
    (lower:N.val ≤ l.length*b)
    (upper:l.length ≤ 2*N.val)
    (f:∀ x:Fields M, ‖(l.map p).prod x‖ ≤ d^l.length):
    ∃ (y:List (Site N))(m:ℕ), outdoor T y ∧ y.length=m*l.length ∧ (∀ x:Fields M, ‖(y.map p).prod x‖ ≤ d^y.length) ∧ ‖F (l.map p).prod‖^m ≤ ‖F (y.map p).prod‖ ∧ 0< m ∧ y.length≤ (More N).val^4 ∧ (More N).val^4 ≤ y.length*(4*(b+plusAgain B D))^4:=by
 let q' := univ.erase j
 obtain ⟨k,u',t⟩:= goldi (Nat.add_pos_right _ plusAgain_pos) u
 obtain ⟨Y,V,hv,z,s⟩:=spun_all h l q' v (fun i hi=>e i (mem_erase.mp hi).1) u' f
 have hc:q'.card=3:=by simp [q',card_erase_of_mem,Axis]
 rw [hc] at hv z s
 refine ⟨Y,_,V,hv,?_,s,by positivity,?_,?_⟩
 · rw [hv,mul_comm _ l.length,pow_mul]; exact z
 · change Y.length ≤ (N.val*2)^4
   rw [hv,pow_succ _ 3]; refine mul_le_mul' (pow_le_pow_left' ?_ _) ?_
   · have hp:= u'.trans' (Nat.le_mul_of_pos_right (2^k) (Nat.add_pos_right _ (show 0 < plusAgain B D from plusAgain_pos))); omega
   · omega
 · have hb₀: N.val*2 ≤ 2^k*(4*(b+plusAgain B D)):= (Nat.mul_le_mul_right 2 t).trans_eq (by ring)
   have hb₁: N.val*2 ≤ l.length*(4*(b+plusAgain B D)):= 
      (Nat.mul_le_mul_right 2 lower).trans (by nlinarith)
   change (N.val*2)^4≤_
   rw [hv,pow_succ]
   refine (mul_le_mul' (pow_le_pow_left' hb₀ 3) hb₁).trans_eq (by ring)

end Again
end YM.CF.Buffered.Afterglow
