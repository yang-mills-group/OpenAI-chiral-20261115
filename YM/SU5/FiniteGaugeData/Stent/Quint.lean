import YM.SU5.FiniteGaugeData.Stent.Minna
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent
set_option linter.unusedSimpArgs false
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
open NormedSpace
variable {N: Side}{b:Bool}{F:Op SU.Slot}
local notation "Ω"=> Op SU.Slot
abbrev PlusM (Q:Ω)(i:SpinIdx):= ((Aop-(1/2:ℂ) • 1) i i) • Q
def Lock(F:Ω)(b:Bool)(i:SpinIdx): Ω:= exp (if b then PlusM F i else -(PlusM F i))
lemma lock_live (a:SpinIdx): IsUnit (Lock F b a) := by letI:NormedAlgebra ℚ Ω:= NormedAlgebra.restrictScalars ℚ ℂ Ω; unfold Lock; exact isUnit_exp _ -- tune a declaration
lemma Poleg(i:SpinIdx): Continuous (fun x:Op SU.Slot=> Lock x b i):=by letI:NormedAlgebra ℚ Ω:= NormedAlgebra.restrictScalars ℚ ℂ Ω; unfold Lock; split <;> fun_prop -- tune
local notation "R₀" n:max=> Equiv.refl (Site n ×SpinIdx)
lemma fee_plank (N:Side)(v: Op SU.Slot): plankP N v=jump (R₀ N) (fun x=> PlusM v x.2):=by
 let u:=Aop-(1/2:ℂ) • (1:Op SpinIdx); ext ⟨⟨i,a⟩,b⟩ ⟨⟨j,d⟩,c⟩; change jump (Equiv.refl (Site N)) (fun _=>u ⊗ₖ v) (i,a,b) (j,d,c)=_; simp_rw [jump_apply, Matrix.kroneckerMap_apply]; by_cases h:i=j <;> by_cases p:a=d <;> simp [u,h,p,Matrix.one_apply,PlusM,gr_diag] -- tune
noncomputable def ShapeP (N:Side):(Site N× SpinIdx→ Op SU.Slot) →+* Op (Single N) where
 toFun v:= jump (R₀ N) v
 map_one':= jump_id
 map_zero':= by ext i j; rw [jump_apply]; simp
 map_add' _ _:= jump_add ..
 map_mul' x y:=by rw [jump_mul]; rfl
private lemma shpc (N:Side):Continuous (ShapeP N):=by
 apply continuous_matrix; intro i j; change Continuous fun v:Site N×SpinIdx→ Ω=> jump (R₀ N) v i j; simp_rw [jump_apply]; split; exact (continuous_apply i.1).matrix_elem i.2 j.2; exact continuous_const
private lemma arch_exp {ι:Type*}[Fintype ι](F:ι→Op SU.Slot)(i:ι) : exp F i= exp (F i):= by letI: NormedAlgebra ℚ (Op SU.Slot):= NormedAlgebra.restrictScalars ℚ ℂ _; exact Pi.coe_exp F i
private lemma exp_shape (N:Side)(x: Site N ×SpinIdx→ Op SU.Slot): exp (ShapeP N x) = jump (R₀ N) (fun i=>exp (x i)):=by
 letI: NormedAlgebra ℚ Ω:= NormedAlgebra.restrictScalars ℚ ℂ _; letI:NormedAlgebra ℚ (Op (Single N)):= NormedAlgebra.restrictScalars ℚ ℂ _; letI : NormedAlgebra ℚ (Site N×SpinIdx→ Ω):= inferInstance; rw [← map_exp (ShapeP N) (shpc N)]; exact congrArg (jump (R₀ N)) (funext (fun i:Site N × SpinIdx=>arch_exp x i)) -- unw
lemma feeM : feeL b N F=jump (R₀ N) (fun i=> Lock F b i.2):=by
 unfold feeL Lock; rw [fee_plank]; split_ifs; exact exp_shape N (fun (x:Site N×SpinIdx)=>PlusM F x.2); rw [← jump_neg]; exact exp_shape N (fun (x:Site N×SpinIdx)=> -PlusM F x.2)
lemma fee_work (x:Site N ×SpinIdx)(u:SU.Slot) : acts (feeL b N F) (basisKet (x,u))=∑ j:SU.Slot, Lock F b x.2 j u • basisKet (x,j) := by
 apply PiLp.ext; rintro ⟨i,j⟩; rw [basis_act,feeM,jump_apply]; simp only [WithLp.ofLp_sum,Finset.sum_apply,basis_apply,WithLp.ofLp_smul,Pi.smul_apply, smul_eq_mul,mul_ite,mul_one,mul_zero]; rw [sum_eq_single j]; swap; · intro k _ e; rw [if_neg (fun w=>e (Prod.mk.inj w).2.symm)]
 swap; · simp
 by_cases h:i=x <;> simp [h, Equiv.refl_apply, h,Ne.symm]
#print axioms feeM
end YM.CF.Buffered.Stent
