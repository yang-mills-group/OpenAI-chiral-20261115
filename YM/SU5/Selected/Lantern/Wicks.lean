import YM.SU5.Selected.Lantern.Booth
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
variable {n m T:Type*}[Fintype n][LinearOrder n][Nonempty n][Fintype m][DecidableEq m][Fintype T][DecidableEq T]

def restore (T:Type*) [Fintype T][DecidableEq T](X Z: WRect n T)(P:Op n): WRect n T:= P*Z*(Xᴴ*(P*Z))⁻¹
lemma rents 
    (X Z:WRect n T)(P:Op n)(p:IsStarProjection P) (R ε δ:ℝ)
    (e:δ+ε≤1/3)(h:‖X‖≤1)(q:‖Z‖≤R) (g:‖Xᴴ*Z-1‖≤δ)(f:‖(1-P)*Z‖≤ε) :
    let Y:= restore T X Z P; P*Y=Y ∧ Xᴴ*Y=1 ∧ ‖Y‖≤2*R ∧ ‖Z-Y‖ ≤ ε+R*2*(δ+ε):=by
 have hc:= show ‖Z-P*Z‖≤ε from (by rwa [Matrix.sub_mul,Matrix.one_mul] at f); let V:=P*Z; let A:= Xᴴ*V; let y:=V*A⁻¹
 have hp:‖V‖≤R:=bound_shift p q
 have ht: ‖A-1‖≤δ+ε:=by
    have ht:A-1=(Xᴴ*Z-1)-Xᴴ*(Z-V):=by unfold A; rw [Matrix.mul_sub]; abel
    rw [ht]; exact (norm_sub_le ..).trans (add_le_add g ((charge_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le h) hc).trans_eq (one_mul _)))
 obtain ⟨hg,l⟩: IsUnit A∧‖A⁻¹‖≤2:=by
    cases isEmpty_or_nonempty T; · rw [Subsingleton.elim A 1]; exact ⟨isUnit_one,by rw [Subsingleton.elim ((1:Op T)⁻¹) 0,norm_zero]; norm_num⟩
    exact inv_close_le 1 (le_trans ht e)
 have ha:A*A⁻¹=1:= Matrix.mul_nonsing_inv _ (A.isUnit_iff_isUnit_det.mp hg)
 have hz:‖(1:Op T)-A⁻¹‖ ≤ 2*(δ+ε):=by
    rw [show _-A⁻¹=(A-1)*A⁻¹ from (by rw [sub_mul,ha,one_mul])]; exact (charge_mul ht l).trans_eq (mul_comm ..)
 intro Y; change P*y=y∧ _; refine ⟨?_,?_,?_,?_⟩
 · unfold y V; rw [←Matrix.mul_assoc,←Matrix.mul_assoc,p.isIdempotentElem]
 · change Xᴴ*y=_; unfold y; rw [←Matrix.mul_assoc]; exact ha
 · exact (charge_mul hp l).trans_eq (mul_comm ..)
 change ‖Z-y‖≤_; apply (norm_sub_le_norm_sub_add_norm_sub Z V y).trans; refine add_le_add hc ?_; unfold y; rw [show V-V*A⁻¹=V*(1-A⁻¹) from (by rw [Matrix.mul_sub, Matrix.mul_one])]; exact (charge_mul hp hz).trans_eq (by ring)
lemma support_w {i: Finset n} (P:Op n)(p:IsStarProjection P){X Z: WRect n m}{S:Finset n}{F:FC n}{b:Bool}
    (h: (hand (!b) (cutM S))*X=X)(hp: Contained (iᶜ) Z)
    (g:Fine S i false F) {R ε δ E:ℝ}(v:δ+ε≤1/3)(r:ε+R*2*(δ+ε) ≤ E^3)
    (e:‖X‖≤1)(q:‖Z‖≤R)(k:‖Xᴴ*Z-1‖≤δ)(t:‖(1-hand b P)*Z‖≤ε) :
    ∃ Y:m→Ket n, Chancel.Sheet S i P F b (col X) Y (col Z) (2*R) E:=by
 let U:= hand b P; let Y:= restore m X Z U
 obtain ⟨l,hh,y,z⟩:=rents X Z U (raft b p) R ε δ v e q k t
 have hy:Xᴴ*Y=1:= hh; have hx(i j:m):inner ℂ (col Y i) (col X j)=(1:Op m) i j:=by rw [← inner_conj_symm,income_t,hy]; simp [Matrix.one_apply,apply_ite,eq_comm] -- tune
 exact ⟨col Y, ⟨(col_lim ..).2 l,fun i=> (col_charge ..).trans y,(containedT ..).1 hp, fun i=>by rw [←col_sub]; exact ((col_charge ..).trans z).trans r,(col_lim ..).2 h,fun i=>(col_charge X i).trans e,fun i=> by rw [hx,Matrix.one_apply_eq],fun i j p=>by rw [hx,Matrix.one_apply_ne p],g⟩⟩ -- rw syntax inside tuple tune

-- Glue across arbitrary finite number of blocks. no coupling T growth in norm correction.
def globe (A:T→ WRect n m): WRect n (T×m):= Matrix.of fun i k=> A k.1 i k.2
@[simp] lemma globe_val(A:T→ WRect n m)(i:n)(t:T)(j:m): globe A i (t,j)=A t i j:=rfl
lemma globe_col(A:T→WRect n m)(i:m)(t:T): col (globe A) (t,i)=col (A t) i:=rfl
lemma globe_action(A:Op n)(Q:T→ WRect n m): A*globe Q=globe (fun x=> A*Q x):=by ext i ⟨x,j⟩; rw [globe_val]; rfl
lemma globe_add (A V:T→WRect n m): globe (A+V)=globe A+globe V:=rfl
lemma globe_s {A V:T→WRect n m}(p:∀ i j:T, i ≠ j→ (A i)ᴴ* V j=0) : (globe A)ᴴ*globe V=jump (Equiv.refl T) (fun i=> (A i)ᴴ*V i):=by
 ext ⟨i,j⟩ ⟨k,l⟩; change ((A i)ᴴ * V k) j l=_; by_cases e:i=k; · subst k; simp [jump_apply]
 rw [p i k e]; simp [jump_apply,e]
lemma globe_cost {A:T→WRect n m}{S:T→Finset n}{C:ℝ}(c:0≤C)(q:∀ i,Contained (S i) (A i))(p: Pairwise (Disjoint on S))(e:∀ i,‖A i‖≤C) : ‖globe A‖≤C:= by
 apply le_of_sq_le_sq _ c; rw [sq,←Matrix.l2_opNorm_conjTranspose_mul_self, globe_s (fun i j t=> (q i).other (q j) (p t))]; apply jump_bound _ _ (by positivity); intro i; rw [Matrix.l2_opNorm_conjTranspose_mul_self, ←sq]; gcongr; exact e _
lemma globe_grant {A V:T→WRect n m}{S:T→Finset n}{δ:ℝ}(d:0≤δ)(p:Pairwise (Disjoint on S))(q:∀ i,Contained (S i) (A i))(r:∀ i,Contained (S i) (V i))(h:∀ i, ‖(A i)ᴴ*V i-1‖ ≤ δ) :‖(globe A)ᴴ*globe V-1‖≤δ:=by
 rw [globe_s (fun i j t=> (q i).other (r j) (p t)),←jump_id,←jump_sub]; exact jump_bound _ _ d h
lemma globe_hold {A:T → WRect n m}{S:Finset n}(t:∀ i, Contained S (A i)): Contained S (globe A):= by unfold Contained; rw [globe_action]; exact congrArg globe (funext t) -- defeq
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms rents
#print axioms globe_cost
#print axioms support_w
