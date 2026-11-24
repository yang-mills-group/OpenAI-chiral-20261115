import YM.CF.BProof.Dream.Disk
import YM.CF.Operator.Commute

/-! B-Gz principals mark `U` iff every angle < π and net phase m. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Dream
open Matrix Complex Finset Function Unitary
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff BigOperators ComplexConjugate
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]
local notation "D" => Matrix.diagonal
-- remember Eq for B symmetry even repeated angles.
def dial (U:UNI n)(d:n→ℂ): Op n:=twist U (D d)
lemma dial_eq (U:UNI n)(d:n→ℂ): dial U d=U.val*D d*star U.val:=twist_formula ..
lemma dial_mul (U:UNI n)(d e:n→ℂ): dial U d *dial U e= dial U (d*e):=by rw [dial,dial,← map_mul,dial,diagonal_mul_diagonal]; rfl
lemma dial_one (U:UNI n): dial U (1:n→ℂ)=1:=map_one (twist U)
lemma dial_star (U:UNI n)(d:n→ℂ): star (dial U d)=dial U (fun i=> star (d i)):=by rw [dial,← map_star,dial]; apply congrArg; ext i j; by_cases h:i=j <;> simp [h,Ne.symm]
lemma dial_inj (U:UNI n): Injective (dial U):= fun _ _ h=> diagonal_injective ((twist U).injective h)
lemma dial_sub (U:UNI n)(d e:n→ℂ): dial U (d-e)= dial U d-dial U e:=by unfold dial; rw [←map_sub,diagonal_sub]; rfl
lemma dialT (U: UNI n) (d:n→ℂ): (dial U d).trace=∑ i,d i:=by rw [dial_eq,trace_mul_cycle,Unitary.star_mul_self_of_mem U.property,one_mul,trace_diagonal] -- tune
lemma dial_det (U:UNI n)(d:n→ℂ): (dial U d).det=∏ i,d i:=by
 have he:= congrArg Matrix.det ((Unitary.star_mul_self_of_mem U.property): star U.val * U.val=1); rw [Matrix.det_mul,Matrix.det_one] at he; rw [dial_eq,det_mul,det_mul,mul_comm _ (det (star _)),←mul_assoc,he,one_mul,det_diagonal]
lemma dial_smul (U:UNI n)(d:n→ℂ)(z:ℂ): z • dial U d=dial U (z • d):=by rw [dial_eq,dial_eq, Matrix.diagonal_smul]; simp [Algebra.smul_mul_assoc,Algebra.mul_smul_comm] -- tune direction
lemma dial_add (U:UNI n)(d e:n→ℂ): dial U d+dial U e=dial U (d+e):=by unfold dial; rw [←map_add,Matrix.diagonal_add]; rfl
lemma dial_diag (U:UNI n)(d:n→ℂ): ‖dial U d‖=‖d‖:=by rw [dial,twist_norm,l2_opNorm_diagonal]

def clockM (U:UNI n)(a:n→ℝ)(t:ℝ):=dial U (fun i=>rose (a i*t))
lemma clocks (U:UNI n)(a:n→ℝ)(s t:ℝ): clockM U a s*clockM U a t=clockM U a (s+t):=by unfold clockM; rw [dial_mul]; apply congrArg; ext1 i; rw [mul_add,rose_add]; rfl
@[simp] lemma clock0 (U:UNI n)(a:n→ℝ): clockM U a 0=1:=by simp_rw [clockM,mul_zero,rose_zero]; exact dial_one _
lemma clockU (U:UNI n)(a:n→ℝ)(t:ℝ): clockM U a t ∈ unitary _:=by
 have he : star (clockM U a t)=clockM U a (-t):=by simp only [clockM,dial_star,rose_star,mul_neg]
 constructor <;> rw [he,clocks] <;> simp
lemma clocksDet (U:UNI n)(a:n→ℝ)(t:ℝ): (clockM U a t).det=rose ((∑ i,a i)*t):=by
 rw [clockM, dial_det]; have he : ∀ (s:Finset n), rose ((∑ i∈s,a i)*t)=∏ i∈s,rose (a i*t):=by intro s; induction s using Finset.induction_on with | empty=>simp | @insert i s hi ih=> rw [sum_insert hi,prod_insert hi,add_mul,rose_add, ih]
 exact (he _).symm
def linDial (U:UNI n): (n→ℂ) →ₗ[ℂ] Op n where
 toFun:=dial U
 map_add' x y:=(dial_add U x y).symm
 map_smul' x y:=(dial_smul U y x).symm
lemma clockS (U: UNI n)(a:n→ℝ): ContDiff ℝ ∞ (clockM U a):=((linDial U).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (contDiff_pi.mpr (fun i : n=> rose_smooth.comp (ContDiff.mul (contDiff_const (c:=a i)) contDiff_id)))

lemma BothU {U:UNI n}{M: Op n}{d:n→ℂ} : dial U d*M=M*(dial U d)ᵀ ↔
     let X:=star U.val*M*(star U.val)ᵀ; D d* X=X*D d:=by
 let V:=U.val; have hu:V*star V=1:=U.property.2; have hh:star V*V=1:=U.property.1; have hv:(star V)ᵀ*Vᵀ=1:=by rw [←transpose_mul,hu,transpose_one]
 have hr:Vᵀ*(star V)ᵀ=1:=by rw [←transpose_mul,hh,transpose_one]
 -- shifts
 let A:=D d; rw [dial_eq]; change V*A*star V*M=M*(V*A*star V)ᵀ ↔ _; rw [transpose_mul,transpose_mul,diagonal_transpose] -- tune name
 change _ ↔ A*(star V*M*(star V)ᵀ)=star V*M*(star V)ᵀ*A; constructor
 · intro h; have he:= congrArg (fun X:Op n=> star V*X*(star V)ᵀ) h; simp only [←mul_assoc,hh,one_mul] at he; simp only [mul_assoc,hr,mul_one] at he ⊢; exact he
 intro h; have he:= congrArg (fun X:Op n=> V*X*Vᵀ) h; simp only [mul_assoc,hv,mul_one] at he; simp only [←mul_assoc,hu,one_mul] at he ⊢; exact he
lemma clockShares (U: UNI n)(a:n→ℝ)(M: Op n)(e:∀ i,MainT (a i)) (h:clockM U a 1*M=M*(clockM U a 1)ᵀ)(t:ℝ): clockM U a t*M=M*(clockM U a t)ᵀ:=by
 let Y:=star U.val*M*(star U.val)ᵀ; apply BothU.mpr; ext i j
 have ht(i j:n):rose (a i)*Y i j=Y i j*rose (a j):=by simpa only [diagonal_mul, mul_diagonal,mul_one,Y] using Matrix.ext_iff.mpr ((BothU (d:=fun i=>rose (a i*1))).mp h) i j
 change (D (fun i=>rose (a i*t))*Y) i j=(Y*D (fun i=>rose (a i*t))) i j; rw [diagonal_mul,mul_diagonal]; by_cases H:Y i j=0; simp [H]; rw [main_inject (e i) (e j) (mul_right_cancel₀ H ((ht i j).trans (mul_comm ..))),mul_comm]
lemma clockDisk [Nonempty n](U:UNI n)(a:n→ℝ)(e:∀ i,MainT (a i)): ∃ (M:Op n)(r:ℝ),0<r ∧ r<1∧ ∀ (s:ℝ),0≤s→ s≤1 → ‖clockM U a s-M‖≤r := by
 choose d r h H X using fun i=> scalarDisk (a i) (e i); obtain ⟨i,v,hv⟩:= exists_max_image univ r univ_nonempty; refine ⟨dial U d,r i,h i,H i,fun t ht ht'=>?_⟩; rw [clockM, ←dial_sub,dial_diag]; exact (pi_norm_le_iff_of_nonneg (h _).le).mpr (fun x=> (X x t ht ht').trans (hv x (mem_univ _)))
def Whirl (M: Op n)(m:ℝ) : Prop := ∃ (U: UNI n)(a:n→ℝ), M=dial U (rose ∘ a) ∧ (∀ i,MainT (a i)) ∧ ∑ i, a i=m
lemma whirl_one : Whirl (1:Op n) 0:=⟨1,0,(by simp [dial,twist_formula,Function.comp_def]),fun _=> main0,by simp⟩ -- tune
lemma cc_Whirl {M: Op n}{m:ℝ}(h:Whirl M m): Whirl (cc M) (-m):=by
 obtain ⟨U,a,rfl,he,w⟩:=h; let V:=ccU U; refine ⟨V,-a,?_,fun i=>(he i).neg,by simp [w]⟩; rw [dial_eq,dial_eq,cc_mul,cc_mul,cc_star]; rw [show cc (D (rose ∘ a))=D (rose ∘ (-a)) from (by ext i j; by_cases h:i=j; subst j; simp only [cc_apply,Matrix.diagonal_apply_eq,Function.comp_apply, rose_star,Pi.neg_apply]; simp [h])]; rfl
end YM.CF.BProof.Dream
