import YM.CF.BProof.Double.Foible

/-! Oblique projection from B-op. Deck also covers unpressed bra by empty P,Q. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I]{A P Q C:Op I}{c r:ℝ}
lemma nothing_deck (g:Shelf A C r): Double.Deck A 0 0 C 1 r:=by
 have ht:floorH A 0 0 0=A:=by rw [floorH]; simp only [house,space,add_zero,sub_zero,wedgeP,wedgeQ,mul_zero,land,zero_mul,zero_add, zero_smul,zero_pow (by decide:2≠0),one_mul]; rw [send, entered,g.proj.isSelfAdjoint,g.proj.isIdempotentElem,add_sub_cancel,inv_one,one_mul, g.proj.isIdempotentElem]
 refine ⟨⟨g.proj,IsStarProjection.zero ..,IsStarProjection.zero ..,by simp,by simp,by simp,one_pos,le_rfl⟩, cc_zero,cc_zero,Commute.zero_right C,Commute.zero_right C, by rwa [ht]⟩
def oblique (A P Q C: Op I): M I:= penR A * (penR A + penL P Q C)⁻¹
namespace Deck
variable (p: Double.Deck A P Q C c r)
include p
lemma enters (x:Book I): Enter (acts (oblique A P Q C) x) A:= (realEnter ..).mpr (by rw [←act_mul, oblique,←mul_assoc,(projRight p.cbP.a).isIdempotentElem])
lemma cloud : 1-oblique A P Q C=penL P Q C*(penR A+penL P Q C)⁻¹:=by
 let V:= penR A+penL P Q C; have ht: V*V⁻¹=1:= (live (active (margin_pos p.cbP.nice p.safety.lid) p.reserve)).1; unfold oblique; nth_rw 1 [←ht]; rw [show V*V⁻¹= _ from (add_mul (penR A) (penL P Q C) V⁻¹),add_sub_cancel_left]
lemma living (x:Book I): Live (acts (1-oblique A P Q C) x) P Q C:=(p.onFoot _).2 (by rw [p.cloud,←act_mul,←mul_assoc,p.project.isIdempotentElem])
end Deck
end YM.CF.BProof.Double
