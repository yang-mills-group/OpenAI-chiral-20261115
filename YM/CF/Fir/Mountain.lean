import YM.CF.Fir.Flash
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
set_option linter.unusedSimpArgs false
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset Set WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable (L:Side)
abbrev St (L:Side):= Site L× SpinIdx
abbrev Stk (L:Side):= Op (St L)
def stack (J:Site L→Op SpinIdx):Stk L:=jump (Equiv.refl _) J
def spike (J: Op SpinIdx):Stk L:=stack L (fun r=> if r=0 then J else 0)
def peb :Stk L:=spike L 1
def col (f:Site L→Op SpinIdx):Stk L:= Matrix.of fun i j=> if j.1=0 then f i.1 i.2 j.2 else 0
lemma c_app (f:Site L→Op SpinIdx)(i b k a): col L f (i,b) (k,a)=if k=0 then f i b a else 0:=rfl
lemma s_app (f:Site L→Op SpinIdx)(i b k a): stack L f (i,b) (k,a)=if i=k then f i b a else 0:=by rw [stack,jump_apply]; rfl
@[simp] lemma stack_add (f g:Site L→Op SpinIdx):stack L (f+g)=stack L f+stack L g:= jump_add .. -- check
@[simp] lemma stack_sub (f g:Site L→Op SpinIdx):stack L (f-g)=stack L f-stack L g:=by rw [sub_eq_add_neg, sub_eq_add_neg,stack_add]; congr 1; exact jump_neg _ g
@[simp] lemma stack_mul (f g:Site L→Op SpinIdx): stack L (f*g)=stack L f*stack L g:=by rw [stack,stack,stack, jump_mul]; rfl
@[simp] lemma stack_one : stack L 1=1:=jump_id
@[simp] lemma stack_star (f:Site L→Op SpinIdx): star (stack L f)=stack L (star f):= by rw [stack, jump_star]; rfl
@[simp] lemma stack_zero:stack L 0=0:=by ext ⟨x,a⟩ ⟨y,b⟩; simp [s_app]
lemma stackA (Y:Op SpinIdx)(f:Site L→ℂ): Commute (stack L (fun _=>Y)) (col L (fun i=> f i • 1)):=by
  ext ⟨i,b⟩ ⟨k,a⟩; simp only [Matrix.mul_apply, St,Fintype.sum_prod_type,s_app,c_app,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul]; by_cases h:k=0 <;> simp [h, mul_ite, ite_mul, mul_comm] <;> try grind; -- check
lemma stacked (A B:Site L→Op SpinIdx): stack L A*col L B=col L (A*B):=by
  ext ⟨x,i⟩ ⟨y,j⟩; unfold St; simp only [Matrix.mul_apply, c_app,St,Fintype.sum_prod_type,s_app,Pi.mul_apply]; by_cases h:y=0
  · simp [h, ite_mul,Matrix.mul_apply]
  simp [h,ite_mul]
lemma spike_mul (A: Op SpinIdx)(f: Site L→Op SpinIdx): spike L A * stack L f=spike L (A*f 0):=by rw [spike, ← stack_mul, spike]; congr 1; funext i; by_cases h:i=0 <;> simp [h]
lemma mul_spike (f: Site L→Op SpinIdx)(A: Op SpinIdx): stack L f * spike L A=spike L (f 0*A):=by rw [spike, ← stack_mul,spike]; congr 1; funext i; by_cases h:i=0 <;> simp [h]
lemma col_spike (f:Site L→Op SpinIdx)(A: Op SpinIdx): col L f * spike L A = col L (fun i=> f i*A):=by
  ext ⟨x,i⟩ ⟨y,j⟩; simp only [Matrix.mul_apply, c_app,St,Fintype.sum_prod_type,s_app,spike]; -- order
  by_cases h:y=0 <;> simp [s_app,h,ite_mul]
lemma plucks (f:Site L→Op SpinIdx)(A: Op SpinIdx): spike L A * col L f=spike L (A*f 0):=by
  rw [spike,stacked]; ext ⟨i,a⟩ ⟨j,b⟩; by_cases h:i=0 <;> by_cases g:j=0 <;> simp [h,g,spike,s_app,c_app] <;> try grind
lemma peb_col (f:Site L→Op SpinIdx): col L f*peb L=col L f:=by rw [peb,col_spike]; simp
lemma spike_times (A B:Op SpinIdx): spike L A*spike L B=spike L (A*B):=by rw [spike,mul_spike]; simp
lemma spike_scale (c:ℂ)(A:Op SpinIdx): spike L (c • A)=c • spike L A:=by ext ⟨i,b⟩ ⟨k,a⟩; by_cases h:i=k <;> by_cases g:k=0 <;> simp [spike,s_app,h,g] <;> grind
lemma spike_star (A:Op SpinIdx): star (spike L A)=spike L (star A):=by rw [spike,stack_star,spike]; congr 1; funext i; by_cases h:i=0 <;> simp [h]
@[simp] lemma peb_sq : peb L*peb L=peb L:=by simp [peb,spike_times]
@[simp] lemma peb_star : star (peb L)=peb L:=by simp [peb,spike_star]
lemma chunks (A B:Site L→Op SpinIdx): star (col L A)* col L B=spike L (∑ i, star (A i)* B i):=by
  ext ⟨x,i⟩ ⟨y,j⟩; simp only [Matrix.mul_apply,c_app, Matrix.star_apply,St,Fintype.sum_prod_type,spike,s_app]; by_cases h:x=0 <;> by_cases g:y=0 <;> simp [h,g, Matrix.sum_apply,Matrix.mul_apply] <;> try grind
lemma spike_form (f:Site L→Op SpinIdx): spike L (f 0)=col L (fun i=>if i=0 then f i else 0):=by
  ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:x=0 <;> by_cases g:y=0 <;> simp [s_app,c_app,h,g,spike] <;> try grind
lemma stack_scale (c:ℂ)(f:Site L→Op SpinIdx): stack L (c • f)=c • stack L f:=by ext ⟨x,i⟩ ⟨y,j⟩; by_cases h:x=y <;> simp [s_app,h]
end YM.CF.Fir
