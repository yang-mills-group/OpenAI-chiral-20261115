import YM.CF.Aroma.Nice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N:Side}
def clime(t:Cover) : UNI (Tx N n):=⟨jump (Equiv.addRight (wrap _ t)) (fun i=> Rush.wind i t • 1), jump_unitary _ _ (fun x=>by
 let u : ℂ:=Rush.wind x t; have hv:star u=u:=fee_real _; have hx:u*u=1:=fee_one _; constructor <;> simp only [star_smul,hv,star_one,Matrix.mul_smul,Matrix.smul_mul,mul_one] <;> rw [smul_smul,Rush.wind,fee_real,fee_one,one_smul] -- tune
 )⟩
lemma creep(t:Cover)(x y: Site N)(i j:coneA n)(H:Cab n N): twist (clime t) H (x,i) (y,j)= Rush.wind x t * Rush.wind y t * H (x+wrap _ t,i) (y+wrap _ t,j):=by
 let A: Equiv.Perm (Site N):=Equiv.addRight (wrap _ t); let B (i: Site N): Op (coneA n):=Rush.wind i t • 1; let P:= jump A B
 rw [twist_formula,mul_assoc]; change (P* (H *star P)) _ _=_; unfold P
 rw [rowBlock]; simp only [B,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,mul_ite,ite_mul,mul_zero,zero_mul,mul_one, Finset.sum_ite_eq, mem_univ,ite_true]
 rw [Matrix.mul_apply]; unfold Tx; rw [Fintype.sum_prod_type]; simp only [jump_star, jump_apply, Equiv.symm_apply_eq,star_smul,B,Rush.wind,fee_real,star_one, Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite,mul_zero,mul_one,Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.sum_ite_eq,mem_univ,ite_true, Equiv.symm_apply_apply]
 unfold A; dsimp; ring
variable {q:Momentum}
def Lurch (q:Momentum)(A:Cab n N):Prop:=∀ t,twist (clime t) A= mode q (2 • t) • A

def pet(v: Site N)(p:Momentum):ℂ:= Rush.wind (0:Site N) (lift v)*mode p (lift v)
lemma pet_live (v k: Site N): pet v (mel k)=frequency k v:=by
 have he:=freq_advance k (0:Site N) (lift v); rw [wrap_lift,zero_add, show frequency k 0=1 by simp [frequency],one_mul] at he
 rw [pet,←he,←mul_assoc,Rush.wind,fee_one,one_mul]
lemma dial_cov (F:Tide N q)(A:Cab n N)(h:Lurch q A)(x y:Site N)(i j:coneA n)(k:Site N): A (x,i) (x+y,j)*frequency k (x+y)= frequency (F.σ k) x * (A (0,i) (y,j)*pet y (mel k)):=by
 let t:=natural x
 have he:= congr_arg (fun A:Cab n N=> A (0,i) (y,j)) (h t); change twist (clime _) _ _ _= _ at he; rw [creep,Matrix.smul_apply,smul_eq_mul] at he
 have hx:wrap N t=x:= nat_true x; let c:=mode q (2 • t); let u:= Rush.wind (0:Site N) t; let w:=Rush.wind y t
 rw [hx,zero_add,add_comm y] at he; change u*w*A (x,i) (x+y,j)=c*A (0,i) (y,j) at he
 have hv:w*frequency k (x+y)=frequency k y*frequency k x:=by have h:= freq_advance k y t; rw [hx,add_comm y] at h; rw [← freq_mode k x]; exact h
 have hh:u*frequency k x=frequency k x:=by have h:=freq_advance k (0:Site N) t; rw [hx,zero_add,show frequency k 0=1 by simp [frequency],one_mul,show mode (mel k) t=frequency k x from freq_mode ..] at h; exact h
 have hp:frequency k x≠0:=fun H=>by simpa [H] using frequency_unit k x
 rw [show u=1 from mul_right_cancel₀ hp (by rwa [one_mul]),one_mul] at he
 calc
    _=(w*A (x,i) (x+y,j))*(w*frequency k (x+y)):=by rw [show _ * (w*frequency k (x+y)) = w*w*(A (x,i) (x+y,j)*frequency k (x+y)) by ring,show w*w=1 from fee_one _,one_mul]
    _ = _ := by rw [he,hv,F.door,pet_live]; unfold c t; ring
lemma tunnel (F:Tide N q)(A:Cab n N)(h:Lurch q A)(B:Site N→ Op (coneA n))(he:∀ k i j,B k i j = ∑ y,A (0,i) (y,j)*pet y (mel k)): A=hub F.σ B:=by
 apply probe; intro x k i j; rw [he,mul_sum]
 exact Eq.trans (Equiv.sum_comp (Equiv.addLeft x) (fun y=> A (x,i) (y,j)*frequency k y)).symm (sum_congr rfl fun y _=> dial_cov F A h x y i j k)
end YM.CF.Aroma
