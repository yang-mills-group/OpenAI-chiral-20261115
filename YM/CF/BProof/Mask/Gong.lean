import YM.CF.BProof.Epoch.Use
import YM.CF.BProof.Mask.Post
import YM.CF.BProof.Grid.Vertex
import YM.CF.BProof.Counter.Turn
import YM.CF.Ridge.Ply
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide.Mask
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Half
open Skye Taxi.Denn Py
open Cupboard Cupboard.Episode
variable {N L:Side}{r:ℕ} {R:Patch}
local notation "Λ"=>More N
abbrev Grants (C: Cart N r) :Prop:= ∀ i:Axis, ∀ x y:Seat N,C.w x y ≠0→ y∈ shade N i true r∪shade N i false r
abbrev Zoned (N:Side)(r:ℕ)(R:Patch):= {C: Wheels N r R//Grants C.val}
section
variable {c:Side}(B:Ratio c (More N))(p:B.count.val∣N.val)(v:B.count.val=2*R.L.val)
def spot (r:ℕ)(x: Seat N):= univ.filter fun y:Seat N=> warm B r y∧ separation x y ≤ r
def earn (r:ℕ)(x y:Seat N) : ℝ:=if y∈spot B r x then ((spot B r x).card:ℝ)⁻¹ else 0
include v
lemma armP (x y: Seat N){s:Sweep N}(h:ply_U R.L 1 s): boxA s y∈spot B r (boxA s x) ↔ y∈spot B r x:=by simp [spot,sitT,motion_r B v s h]
-- v erased by explicit? tune include
lemma debtL (x y:Seat N){s:Sweep N}(h:ply_U R.L 1 s): earn B r (boxA s x) (boxA s y)=earn B r x y:=by
 have h': spot B r (boxA s x)=(spot B r x).map (boxA s).toEmbedding:=by ext y; simp; convert armP B v x ((boxA s).symm y) h using 2; simp
 unfold earn; rw [h']; simp
include p
lemma record (w:0<r)(u:2*r≤ B.count.val) : ∃ Z:Zoned N r R,(Z.val.val).w=earn B r:=by
 let f:= earn B r; have hx(x:Seat N):∑ i,f x i=1:=by obtain ⟨y,q,h⟩:= occurs B (x:=x) u; have ht: (spot B r x).card≠0:= Finset.card_ne_zero.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,q,h⟩⟩; unfold f earn; rw [← sum_filter]; simp [ht] -- tune univ filter mem
 have he{x y:Seat N}(h:f x y≠0): warm B r y∧separation x y≤r:= (mem_filter.mp (not_not.mp (mt (fun e=> show f x y=0 from if_neg e) h))).2
 let V:Cart N r:= ⟨f,fun i j=>(by unfold f earn; split <;> positivity),hx,fun i j p=> (he p).2⟩
 have hv : ∀ s, ply_U R.L 1 s → V.Turns s:=by intro s k x y; let A:=(boxA s).symm; simpa only [Equiv.apply_symm_apply] using (debtL B v ((boxA s).symm x) ((boxA s).symm y) k (r:=r)).symm -- defeq earn? tune
 refine ⟨⟨⟨V,hv⟩,fun i x y p'=>bill_r B p w (he p'|>.1) i⟩,rfl⟩
end
-- buy for each level incl every period meeting `eq:box`, same λ. uses Mark transport option as in sew.
def exactCart (R:Patch)(N:Side)(r:ℕ)(c:Side)(B:Ratio c (More N))(p:B.count.val∣ N.val)(v:B.count.val=2*R.L.val)(t:0<r)(h:2*r≤B.count.val): Zoned N r R:= Classical.choose (record B p v t h)
lemma gives (R:Patch)(N:Side)(r:ℕ)(w:2*R.L.val∣N.val)(t:0<r)(p:r ≤ R.L.val): Nonempty (Zoned N r R):=by
 obtain ⟨m,hm⟩:= w; have hx:0 < m:=by by_contra h; have ht:m=0:=(by omega); rw [ht,mul_zero] at hm; exact N.property.ne' hm
 let c:Side:= ⟨m*2, Nat.mul_pos hx (by decide)⟩; let B': Side:= (More R.L); let B: Ratio c (More N):=⟨B',(by rw [natM,natM,hm]; rw [show c.val=m*2 from rfl]; ring)⟩; have he:B.count.val=2*R.L.val:=by rw [show B.count=B' from rfl,natM]; ring
 refine ⟨exactCart R N r c B (by rw [he]; exact ⟨m,hm⟩) he t (he ▸ by omega)⟩
end YM.CF.BProof.Bide.Mask
