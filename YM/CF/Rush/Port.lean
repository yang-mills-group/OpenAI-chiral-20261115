import YM.CF.Rush.Knoll
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N F:Side}(G:Ratio N F) (L : Side)
def putlow (A : Op (Site N ×SpinIdx)): Op (Site N×St L):= Matrix.of fun x y=> if x.2.1=0 ∧ y.2.1=0 then A (x.1,x.2.2) (y.1,y.2.2) else 0
lemma low_mul (A B : Op (Site N × SpinIdx)): putlow L (A*B)=putlow L A*putlow L B:=by
  ext ⟨x,r,a⟩ ⟨y,t,b⟩; simp only [Matrix.mul_apply,putlow,St,Fintype.sum_prod_type,Matrix.of_apply]; by_cases h:r=0 <;> by_cases g:t=0 <;> simp [h,g,Matrix.mul_apply,Fintype.sum_prod_type,ite_mul]
lemma low_label (A: Site N→Op SpinIdx): putlow L (jump (Equiv.refl _) A)=jump (Equiv.refl _) fun i=> spike L (A i):=by
  ext ⟨x,r,a⟩ ⟨y,t,b⟩; by_cases h:r=0 <;> by_cases g:t=0 <;> by_cases e:x=y <;> simp [jump_apply,putlow,h,g,e,spike,stack] <;> grind
lemma low_ice (A:Op (Site N × SpinIdx)): star (putlow L A)= putlow L (star A):=by
  ext ⟨x,r,a⟩ ⟨y,t,b⟩; by_cases h:r=0 <;> by_cases g:t=0 <;> simp [Matrix.star_apply,putlow,h,g]
lemma folio (A:Op (Site N × SpinIdx)): (overU N (St L)).val*putlow L A=putlow L ((overU N SpinIdx).val*A):=by
  ext ⟨x,r,a⟩ ⟨y,t,b⟩; simp only [Matrix.mul_apply,putlow,St,Fintype.sum_prod_type,Matrix.of_apply]; by_cases h:r=0 <;> by_cases g:t=0 <;> simp [h,g,overU,Matrix.one_apply,mul_ite,ite_mul, Matrix.mul_apply,Fintype.sum_prod_type]
lemma folio' (A:Op (Site N ×SpinIdx)): putlow L A*star (overU N (St L)).val=putlow L (A*star (overU N SpinIdx).val):=by
  have h:= congr_arg star (folio L (star A)); simpa only [star_mul,low_ice,star_star] using h
lemma low_pose (A:Momentum→Op SpinIdx): plates N (fun p=> spike L (A p))=putlow L (plates N A):=by
  unfold plates; rw [twist_formula,twist_formula,← show putlow L (mark N A)=mark N (fun p=> spike L (A p)) from low_label L _,folio,folio']
lemma vine_stem (j:ℕ)(M:Side)(u:Bool): plates N (vine u j L M)=jump (Equiv.refl _) (fun _=>tall u L)+putlow L (plates N (bent u j (L*M))):=by
  rw [← pilesV,← low_pose,pilesA]; rfl

def echo (i:Axis) : Op (Site F × SpinIdx):=jump (advance i) (fun x => seam (anticut F) x i • (1 : Op SpinIdx))
def sentry (u:List Axis) : Op (Site N×St G.count):=(u.map fun i=>solo G (echo i)-1).prod
lemma blaze (h:Odd G.count.val)(i:Axis): solo G (echo i)-1 =
    plates N (fun p=> trident G.count p*stack G.count (fun l=> chip (aliasAt p l i) • (1:Op SpinIdx))*star (trident G.count p)):=by
  -- derive echo-1 = cart for chip
  -- monoomial identity symbol
  let C:Cover:=step i; let f(z:Cover):Op SpinIdx:=if z=C then 1 else 0
  let A(p:Momentum):Op SpinIdx:= mode p C • 1
  have hk(p:Momentum): mode p C=Complex.exp (Complex.I*p i):=by simp [mode,C,step_apply,mul_ite,apply_ite]
  have he:Reads f A:=by
    refine ⟨fun a b=> summable_of_hasFiniteSupport ((Set.finite_singleton C).subset fun z hz=> by by_contra h; simp at h; simp [f,h,Function.support] at hz),fun p hp a b=>?_⟩
    unfold A Laurent.read
    rw [tsum_eq_single C]; simp [f]; intro z h; simp [f,h]
  have hh(z:Site F): wind z C=seam (anticut F) z i:=by
    let k:Site F:=0
    have h1:=freq_advance k z C; rw [show wrap F C=step i from wrap_step ..] at h1
    have h2:= frequency_hop k z i; rw [show BZ.phase (pm k i)=mode (mel k) C from (by rw [hk]; unfold BZ.phase mel tmap; rw [mul_comm])] at h2
    have h3 := frequency_unit k (z+step i); exact mul_right_cancel₀ (by intro h; rw [h,mul_zero] at h3; exact zero_ne_one h3) (h1.trans h2.symm)
  have hf: cart F f=echo i:=by
    ext ⟨x,a⟩ ⟨y,b⟩; simp only [cart,wagon_app,Matrix.of_apply]; rw [tsum_eq_single C]
    · simp only [echo,jump_apply, f,hh, if_true,Matrix.smul_apply,smul_eq_mul,show wrap F C=step i from wrap_step ..]; rfl
    intro z h; simp [f,h]
  rw [← hf, loop_m G A f he h,← piles1,pilesM]; apply pilesE; intro p hp hx
  have hv := pointed G.count p hp.1; let B:= stack G.count fun l=> A (aliasAt p l)
  rw [show stack G.count (fun l : Site G.count=> chip (aliasAt p l i) • (1:Op SpinIdx))= B - 1 by
    unfold B; rw [← stack_one, ← stack_sub]; congr 1; funext l; unfold A chip; simp [hk,sub_smul]]
  change _ = trident G.count p * (B-1)*star _; rw [mul_sub,sub_mul,mul_one,hv.2]
end YM.CF.Rush
