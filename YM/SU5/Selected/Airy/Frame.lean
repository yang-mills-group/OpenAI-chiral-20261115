import YM.CF.Rush.Cart
import YM.CF.Fock.Ket
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Lat Fir Rush Fock Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
open scoped Kronecker
attribute [local instance] opCStarAlgebra
-- rectangular tools and mass-independent norma
abbrev WRect (X Y:Type*) := Matrix X Y ℂ
variable {X n m l T:Type*} [Fintype X][DecidableEq X] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype l] [DecidableEq l]
def actR (F: WRect n m) : Ket m→L[ℂ] Ket n:= Matrix.toEuclideanLin (𝕜:=ℂ) (m:=n) (n:=m) |>.trans LinearMap.toContinuousLinearMap <| F -- tune
@[simp] lemma actR_fee (F:WRect n m): ‖actR F‖=‖F‖:= rfl
@[simp] lemma actR_val (F:WRect n m)(v:Ket m) : (actR F v).ofLp=F *ᵥ v.ofLp:=rfl
lemma actR_mul (F:WRect n m)(G: WRect m l)(v:Ket l) : actR (F*G) v= actR F (actR G v):=by apply PiLp.ext; intro x; change ((F*G)*ᵥ v.ofLp) x=(F*ᵥ (G*ᵥ v.ofLp)) x; rw [Matrix.mulVec_mulVec]
lemma paidUnit (U:UNI n) : ‖U.val‖ ≤1:= by
 cases isEmpty_or_nonempty n; · rw [Subsingleton.elim U.val (0:Op n),norm_zero]; norm_num
 exact (CStarRing.norm_of_mem_unitary U.property).le
lemma paid_l (U: UNI n)(F:WRect n m): ‖U.val*F‖ ≤ ‖F‖:= (Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_left (norm_nonneg _) (paidUnit _))
lemma paid_r (U: UNI n)(F:WRect m n): ‖F * U.val‖ ≤ ‖F‖:= (Matrix.l2_opNorm_mul ..).trans (mul_le_of_le_one_right (norm_nonneg _) (paidUnit _))
lemma ships_add {S:Finset T}(F:T→ WRect n m)(G:WRect m l): (∑ x∈S,F x)*G=∑ x∈S,F x*G:= by ext; simp [Matrix.mul_apply, Matrix.sum_apply,Finset.sum_mul]; rw [Finset.sum_comm]
lemma ships_add' {S:Finset T}(F:T→ WRect m l)(G:WRect n m): G*(∑ x∈S,F x)=∑ x∈S,G*F x:= by ext; simp [Matrix.mul_apply, Matrix.sum_apply,Finset.mul_sum]; rw [Finset.sum_comm]
-- mask. Inc for any H->Site inject, prior rank also for selection of lists & subset.
def mask (f : X→ n) : WRect n X:= Matrix.of fun i j=> if i=f j then 1 else 0
lemma mask_mem (f:X→n) (F:WRect m n)(i:m)(j:X): (F*mask f) i j=F i (f j):= by simp [Matrix.mul_apply,mask,mul_ite]
lemma mask_star_mem (f:X→n) (F:WRect n m)(i:X)(j:m): ((mask f)ᴴ*F) i j=F (f i) j:= by simp [Matrix.mul_apply,mask,apply_ite,ite_mul]
lemma mask_self (f:X→n)(p:Injective f): (mask f)ᴴ * mask f=1:=by ext i j; rw [mask_star_mem]; simp [mask,p.eq_iff, Matrix.one_apply]
lemma mask_norm {X n:Type*}[Fintype X][DecidableEq X][Fintype n][DecidableEq n]{F:WRect n X}(p:Fᴴ*F=1) : ‖F‖≤1:=by
 cases isEmpty_or_nonempty X; · rw [Subsingleton.elim F 0,norm_zero]; norm_num
 have h:= Matrix.l2_opNorm_conjTranspose_mul_self F; rw [p,norm_one] at h; nlinarith [norm_nonneg F]
lemma mask_toll (f:X→n)(p:Injective f) :‖mask f‖≤1:=mask_norm (mask_self f p)

def tap (F:X→ WRect n m): WRect (X×n) (X×m):= Matrix.of fun i j=> if i.1=j.1 then F i.1 i.2 j.2 else 0
lemma tap_square (F:X→ Op n): tap F=jump (Equiv.refl X) F:=rfl
lemma tap_star (F:X→WRect n m): (tap F)ᴴ=tap (fun i=>(F i)ᴴ):=by
 ext ⟨a,i⟩ ⟨b,j⟩; by_cases p:a=b; · subst b; simp [tap]
 simp [tap,p,Ne.symm p]
lemma tap_mul (F:X→WRect n m)(G:X→WRect m l): tap F * tap G=tap (fun x=> F x * G x):=by
 ext ⟨a,i⟩ ⟨b,j⟩; rw [Matrix.mul_apply,Fintype.sum_prod_type]; rw [sum_eq_single a]; · by_cases p:a=b <;> simp [tap,p, Matrix.mul_apply]
 · intro k _ l; simp [tap, Ne.symm l]
 simp
lemma tap_add (F G:X→WRect n m): tap (F+G)=tap F+tap G:= by ext ⟨a,i⟩ ⟨b,j⟩; by_cases p:a=b <;> simp [tap,p]
lemma tap_sub (F G:X→WRect n m): tap (F-G)=tap F-tap G:= by ext ⟨a,i⟩ ⟨b,j⟩; by_cases p:a=b <;> simp [tap,p]
lemma tap_smul (c:ℂ) (F:X→WRect n m): tap (c•F)=c•tap F:= by ext ⟨a,i⟩ ⟨b,j⟩; by_cases p:a=b <;> simp [tap,p]
lemma tap_sum (F:T→X→WRect n m)(S:Finset T): tap (∑ i∈S,F i)=∑ i∈S,tap (F i):= by
 ext ⟨a,i⟩ ⟨b,j⟩; by_cases p:a=b <;> simp [tap,p,Matrix.sum_apply]
lemma tap_norm {F:X→WRect n m}{k:ℝ}(p:0≤k)(h:∀ i:X, ‖F i‖ ≤k): ‖tap F‖ ≤k:=by
 apply le_of_sq_le_sq _ p; rw [sq,←Matrix.l2_opNorm_conjTranspose_mul_self, tap_star,tap_mul,tap_square]; apply jump_bound _ _ (by positivity); intro x; rw [Matrix.l2_opNorm_conjTranspose_mul_self,←sq]; gcongr; exact h _ -- tune
-- multi-component convolution ***real resolution*** sampled; aliases independent of spacings.
variable {N: Side}
local notation "U" i:max=> Rush.overU N i
lemma square_filter (F:Momentum→ Op n): plates N F= (U n).val * tap (F ∘ mel) * (U n).valᴴ:= by rw [plates,twist_formula]; rfl

def freeze (F: Site N → WRect n m): WRect (Site N×n) (Site N×m):= (U n).val * tap F * (U m).valᴴ
lemma freeze_square (F: Momentum→ Op n): plates N F=freeze (N:=N) (F ∘ mel):= square_filter _
lemma freeze_mul (F:Site N→WRect n m)(G:Site N→WRect m l): freeze F * freeze G=freeze (fun x=> F x * G x):=by
 let P:= (U m).val; have h:Pᴴ*P=1:= (U m).property.1
 unfold freeze; simp only [←Matrix.mul_assoc]; rw [Matrix.mul_assoc _ (U m).valᴴ,h,Matrix.mul_one,Matrix.mul_assoc _ (tap F),tap_mul]
lemma freeze_star (F:Site N→WRect n m): (freeze F)ᴴ=freeze (fun x=>(F x)ᴴ):=by unfold freeze; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,tap_star,Matrix.conjTranspose_conjTranspose,Matrix.mul_assoc]
lemma freeze_norm{F: Site N→ WRect n m}{k:ℝ}(p:0≤k)(h:∀ x:Site N,‖F x‖≤k): ‖freeze F‖≤k:= by
 unfold freeze; exact (paid_r (star (U m)) ..).trans ((paid_l ..).trans (tap_norm p h)) -- tune
lemma freeze_sub (F G:Site N→WRect n m): freeze (F-G)=freeze F-freeze G:=by unfold freeze; rw [tap_sub, Matrix.mul_sub,Matrix.sub_mul]
lemma freeze_one : freeze (fun (_:Site N)=>(1:Op n))=1:=by unfold freeze; rw [tap_square,jump_id,Matrix.mul_one]; exact (U n).property.2
lemma freeze_sum (F:T→Site N→WRect n m)(S:Finset T): freeze (∑ i∈S,F i)=∑ i∈S,freeze (F i):= by unfold freeze; rw [tap_sum, ships_add', ships_add]
lemma freeze_smul (c:ℂ) (F:Site N→WRect n m): freeze (c•F)=c•freeze F:=by unfold freeze; rw [tap_smul, Matrix.mul_smul, Matrix.smul_mul]
-- helpers price on full locations via Fourier
lemma tap_at (F:X→ WRect n m)(A: WRect l (X×n))(x:l)(i:X)(j:m): (A*tap F) x (i,j)=∑ k:n,A x (i,k)*F i k j:=by
 rw [Matrix.mul_apply,Fintype.sum_prod_type, Finset.sum_eq_single i]; · simp [tap]
 · intro b _ g; simp [tap,g]
 simp
lemma freeze_charge (F:Site N→ WRect n m)(x y:Site N)(i:n)(j:m) : freeze F (x,i) (y,j)=∑ k:Site N, Fourier N x k * F k i j * star (Fourier N y k):=by
 unfold freeze; rw [Matrix.mul_apply,Fintype.sum_prod_type]; simp_rw [tap_at]; apply Finset.sum_congr rfl; intro w _; simp [Rush.overU, Matrix.one_apply, mul_ite, ite_mul, apply_ite]
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms freeze_norm
#print axioms mask_toll
#print axioms freeze_mul
#print axioms freeze_charge
