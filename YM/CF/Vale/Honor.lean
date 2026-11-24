import YM.CF.Vale.Oak
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vale
open Function Filter Lattice Laurent Wilson Precision Tree Finset Exterior Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Pec Next.Free Pressure Cascade Reef Hom
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {K:Teller group}{P:RG.Patch}{R:ChartRatio group}{W:Postal}{η:ℝ}{n k:ℕ}{f g:ℝ}{B A C:Side}
lemma empty_pay (h:0≤f):CardK A k 0 f g:=by
 refine ⟨fun i j a b=>?_,?_,fun i=>?_⟩
 · ext z; simp
 · intro i j k z w; simp [Nacre.halo]; change 0=twist (matter w) 0; rw [map_zero]
 simp [balance]; exact h
lemma empty_field : (colorX (0:Toy k A))=0:=by -- use idempotence
 have he:CardK A k 0 0 0:=empty_pay le_rfl
 let V:=colorX (0:Toy k A); have ht: V=V+V:=by have hx:= (carK (0:Toy k A) 0 he.1 he.1 he.2.1 he.2.1).2.2.1; simpa only [add_zero] using hx
 exact (add_left_cancel (show V+V=V+0 from (add_zero V).symm ▸ ht.symm))
lemma empty_stance: Neat (0:Toy k A):=by intro x; rw [empty_field]; simp
lemma white_cost (h:0≤f): Lac (0:Pride A) g f∧ClearP (0:Pride A):=by
 refine ⟨⟨fun i t a b=>rfl,?_,fun i=>?_⟩,?_⟩
 · intro i p q; simp [mom]
 · simp [cents]; exact h
 funext i p q; simp [shineP]
def babyM:Male:=⟨1,by simp⟩ -- adjust
variable (N:Side)
def vanilla:Interest N:= ⟨babyM,⟨0,0⟩,0⟩
lemma naturalC (C:Credit):InterestX C N (vanilla N):= ⟨⟨⟨empty_pay C.posF.le,empty_pay C.posU.le⟩,(white_cost C.posB.le).1⟩,⟨empty_stance,empty_stance⟩, (white_cost (f:=0) (g:=0) le_rfl).2⟩
end YM.CF.Vale
