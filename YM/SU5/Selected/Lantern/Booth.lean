import YM.SU5.Selected.Airy.Frame
import YM.SU5.FiniteGaugeData.Pannier.CaneSugar
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
-- elementary rect matrix on one particle. Fast price. Fixed norms Matrix.l2 wrect. `Support` on old S plans.
variable {n m T Q P: Type*} [Fintype n][DecidableEq n] [Fintype m][DecidableEq m] [Fintype T][DecidableEq T] [Fintype Q][DecidableEq Q] [Fintype P][DecidableEq P]
def col (F: WRect n m)(j:m): Ket n:= WithLp.toLp 2 (fun i:n=> F i j)
@[simp] lemma col_val (F:WRect n m)(j:m)(i:n):(col F j).ofLp i=F i j:=rfl
lemma col_charge (F:WRect n m)(j:m): ‖col F j‖ ≤ ‖F‖:=by
 have e:actR F (basisKet j)=col F j:=by apply PiLp.ext; simp [Matrix.mulVec,dotProduct,mul_ite]
 rw [←e]; simpa [basisKet] using (actR F).le_opNorm (basisKet j)
lemma line_s (D: WRect n m)(F: WRect m T)(i:T): col (D*F) i=actR D (col F i) :=by apply PiLp.ext; intro; exact Eq.refl _
lemma line_a (D:Op n)(F:WRect n m)(i:m): col (D*F) i=acts D (col F i):= line_s D F _
lemma col_scale (c:ℂ)(F:WRect n m)(i:m): col (c•F) i=c • col F i:=rfl -- maybe reduce
lemma col_add (A B:WRect n m)(i:m): col (A+B) i=col A i+col B i:=rfl
lemma col_sub (A B:WRect n m)(i:m): col (A-B) i=col A i - col B i:=rfl
lemma col_own {A B:WRect n m}(t:∀ i:m,col A i=col B i):A=B:= Matrix.ext (fun i j=>congrArg (fun h:Ket n=> h i) (t j))
lemma income_t (A: WRect n m)(B: WRect n T)(i:m)(j:T): inner ℂ (col A i) (col B j)=(Aᴴ*B) i j:=by
 simp only [PiLp.inner_apply, col_val,Matrix.mul_apply,Matrix.conjTranspose_apply]; apply sum_congr rfl; intro k _; change B k j * star (A k i)= _; ring
lemma col_lim (F:WRect n T)(V:Op n): (∀ i, acts V (col F i)=col F i) ↔ V*F=F:= ⟨fun u=>col_own (fun i=> (line_a ..).trans (u _)),fun u i=> (line_a ..).symm.trans (congrArg (fun A:WRect n T=> col A i) u)⟩ -- tune
lemma col_zero (F: WRect n T)(V:Op n): (∀ i,acts V (col F i)=0) ↔ V*F=0:=by
 have h(i:T): col (0:WRect n T) i=0:=rfl; exact ⟨fun u=> col_own fun i=>(line_a ..).trans ((u i).trans (h i).symm),fun u i=>by rw [←line_a,u]; rfl⟩
lemma ortho_pair (A:WRect n m)(B:WRect n T): Aᴴ*B=0 ↔ ∀ i j, inner ℂ (col A i) (col B j)=0:=by simp_rw [income_t]; exact ⟨fun h i j=>by rw [h]; rfl,fun g=>Matrix.ext g⟩
lemma charge_mul {A:WRect n m}{B:WRect m T}{a b:ℝ}(h:‖A‖ ≤ a)(g:‖B‖≤b): ‖A*B‖ ≤ a*b:= (Matrix.l2_opNorm_mul ..).trans (mul_le_mul h g (norm_nonneg _) ((norm_nonneg _).trans h))
lemma rent_v {F:WRect n m}(T:UNI n): ‖T.val*F‖ = ‖F‖:=by
 have h:= paid_l (star T) (T.val*F); have ht:(star T).val*(T.val*F)=F:= by rw [←Matrix.mul_assoc, show (star T).val*T.val=1 from T.property.1,Matrix.one_mul]
 exact le_antisymm (paid_l ..) (by rwa [ht] at h) -- scope
lemma rent_w {F:WRect n m}(T:UNI m): ‖F*T.val‖ = ‖F‖:=by
 rw [← Matrix.l2_opNorm_conjTranspose,Matrix.conjTranspose_mul, show T.valᴴ=(star T).val from rfl, rent_v (star T),Matrix.l2_opNorm_conjTranspose] -- tune
lemma bound_shift {θ:ℝ}[Nonempty n]{X:WRect n m}{U:Op n}(u:IsStarProjection U)(g:‖X‖ ≤ θ):‖U*X‖≤θ:= (charge_mul (u.norm_le U) g).trans_eq (one_mul _)
-- patch constraints
section loom
variable {n:Type*}[Fintype n][LinearOrder n]
def Contained (S:Finset n)(A:WRect n m): Prop:=cutM S*A=A
lemma containedT (S:Finset n)(A:WRect n m): Contained S A↔∀ i:m,withinM S (col A i):= (col_lim ..).symm
lemma containedP (S:Finset n)(A:WRect n m): Contained S A↔∀ i,i∉S→∀ j:m,A i j=0:=by
 rw [containedT]; simp_rw [within_test, col_val]; tauto -- grind
lemma Contained.grows{S T: Finset n} {A: WRect n m}(h:Contained S A)(p:S⊆T) : Contained T A:= containedP ..|>.mpr fun i v j=> (containedP .. |>.1 h) i (mt (fun h=>p h) v) j -- try without instance
lemma Contained.add {S:Finset n}{A B:WRect n m}(h:Contained S A)(p:Contained S B): Contained S (A+B):= by unfold Contained; rw [Matrix.mul_add,h,p]
lemma Contained.times {S:Finset n}{A:WRect n m}(h:Contained S A)(B:WRect m T): Contained S (A*B):=by unfold Contained; rw [←Matrix.mul_assoc,h]
lemma Contained.smul {S:Finset n}{A:WRect n m}(h:Contained S A)(b:ℂ):Contained S (b•A):=by unfold Contained; rw [Matrix.mul_smul,h]
lemma cuts_zero {S T: Finset n}(h:Disjoint S T): cutM S*cutM T=0:=by ext i j; unfold cutM; rw [Matrix.diagonal_mul_diagonal]; by_cases p:i=j; subst j; by_cases u:i∈S; simp [u, disjoint_left.mp h u]; simp [u]; simp [p] -- tune
lemma Contained.away {A:WRect n m}{S T:Finset n}(h:Contained S A)(p:Disjoint T S): cutM T*A=0:=by
 unfold Contained at h; rw [←h,←Matrix.mul_assoc,cuts_zero p,Matrix.zero_mul]
lemma Contained.other {A: WRect n m}{B:WRect n T}{S V:Finset n}(h: Contained S A) (p:Contained V B)(t: Disjoint S V): Aᴴ*B=0:=by
 unfold Contained at h; rw [←h, Matrix.conjTranspose_mul, Matrix.mul_assoc, show (cutM S)ᴴ=cutM S from (cutM_idp _).isSelfAdjoint, p.away t, Matrix.mul_zero]
end loom
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Contained.other
#print axioms rent_v
#print axioms col_charge
