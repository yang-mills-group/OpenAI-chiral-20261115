import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Matrix Real Complex
open scoped Matrix MatrixGroups Topology Classical ComplexOrder
abbrev Two := SL(2, ℂ)
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
abbrev val (s:Two):Mat:=s.1
noncomputable def pin (a b c d:ℂ)(p:a*d-b*c=1): Two:=⟨!![a,b;c,d],by rw [Matrix.det_fin_two]; exact p⟩
def A (s:Two):=val s 0 0
def B (s:Two):=val s 0 1
def C (s:Two):=val s 1 0
def D (s:Two):=val s 1 1
@[simp] lemma Ap(a b c d p): A (pin a b c d p)=a:=rfl -- spacing
@[simp] lemma Bp(a b c d p): B (pin a b c d p)=b:=rfl
@[simp] lemma Cp(a b c d p): C (pin a b c d p)=c:=rfl
@[simp] lemma Dp(a b c d p): D (pin a b c d p)=d:=rfl
lemma det(s:Two): A s*D s-B s*C s=1:=by have h:=s.prop; rwa [Matrix.det_fin_two] at h
lemma tone(s t:Two)(h:A s=A t)(p:B s=B t)(q:C s=C t)(w:D s=D t):s=t:= Matrix.SpecialLinearGroup.ext s t (fun i j=>by fin_cases i <;> fin_cases j <;> assumption)
@[simp] theorem A_one:A 1=1:=rfl
@[simp] theorem B_one:B 1=0:=rfl
@[simp] theorem C_one:C 1=0:=rfl
@[simp] theorem D_one:D 1=1:=rfl
variable (g k:Two)
lemma mul_val : val (g*k) = val g * val k:=rfl
@[simp] theorem A_mul:A (g*k)=A g*A k+B g*C k:=by simp only [A,B,C,mul_val,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem B_mul:B (g*k)=A g*B k+B g*D k:=by simp only [A,B,D,mul_val,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem C_mul:C (g*k)=C g*A k+D g*C k:=by simp only [A,C,D,mul_val,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem D_mul:D (g*k)=C g*B k+D g*D k:=by simp only [D,B,C,mul_val,Matrix.mul_apply,Fin.sum_univ_two]
lemma pin_inv: ∃ h,g⁻¹=pin (D g) (-B g) (-C g) (A g) h:=by
 have h:D g*A g- -B g * -C g=1:=by simp [mul_comm (D g),det]
 refine ⟨h, left_inv_eq_right_inv (inv_mul_cancel _) ?_⟩; apply tone <;> (simp <;> first|(solve|ring)|linear_combination det g) -- tune
@[simp] theorem A_inv:A g⁻¹=D g:= by obtain ⟨h,p⟩:=pin_inv g; simp only [p,Ap]
@[simp] theorem B_inv:B g⁻¹= - B g:= by obtain ⟨h,p⟩:=pin_inv g; simp only [p,Bp]
@[simp] theorem C_inv:C g⁻¹= - C g:= by obtain ⟨h,p⟩:=pin_inv g; simp only [p,Cp]
@[simp] theorem D_inv:D g⁻¹=A g:= by obtain ⟨h,p⟩:=pin_inv g; simp only [p,Dp]
noncomputable def bezel := pin (-1) 0 0 (-1) (by simp)
variable (a:ℂ)
noncomputable def Head := pin 1 a 0 1 (by simp)
noncomputable def Tail := pin 1 0 a 1 (by simp)
variable (u:ℂˣ)
noncomputable def Pole:=pin u 0 0 (u:ℂ)⁻¹ (by simp)
noncomputable def turn := pin 0 1 (-1) 0 (by simp)
@[simp] lemma bezel_sq : bezel * bezel=1:= tone _ _ (by simp [bezel]) (by simp [bezel]) (by simp [bezel]) (by simp [bezel])
lemma bezel_stays : bezel*g=g*bezel:=by apply tone <;> simp [bezel,mul_comm]
@[simp] lemma bezel_inv: bezel⁻¹=bezel:= inv_eq_of_mul_eq_one_right bezel_sq -- maybe left
abbrev rehome {G:Type*}[Group G](g s:G) := g*s*g⁻¹
lemma rehome_mul{G:Type*}[Group G](g u v:G) : rehome g (u*v)=rehome g u*rehome g v:=by unfold rehome; group
lemma rehome_comp{G:Type*}[Group G](g u v:G) : rehome (g*u) v=rehome g (rehome u v):=by unfold rehome; group
@[simp] lemma rehome_back{G:Type*}[Group G](g v:G) : rehome g⁻¹ (rehome g v)=v:=by unfold rehome; group
@[simp] lemma rehome_first{G:Type*}[Group G](g v:G) : rehome g (rehome g⁻¹ v)=v:=by unfold rehome; group
@[simp] lemma rehome_bezel: rehome g bezel=bezel:=by unfold rehome; rw [← bezel_stays];group
@[simp] lemma Head_one: Head 0=1:=by apply tone <;> simp [Head]
@[simp] lemma Tail_one: Tail 0=1:=by apply tone <;> simp [Tail]
lemma Head_add(b:ℂ):Head a*Head b=Head (a+b):=by apply tone <;> simp [Head,add_comm]
lemma Tail_add(b:ℂ):Tail a*Tail b=Tail (a+b):=by apply tone <;> simp [Tail,add_comm]
@[simp] lemma Head_inv:(Head a)⁻¹=Head (-a):=by apply tone <;>simp [Head]
@[simp] lemma Tail_inv:(Tail a)⁻¹=Tail (-a):=by apply tone <;>simp [Tail]
@[simp] lemma Pole_pow(v:ℂˣ):Pole u* Pole v=Pole (u*v):=by apply tone <;> simp [Pole,mul_comm]
@[simp] lemma Pole_inv:(Pole u)⁻¹=Pole u⁻¹:=by apply tone <;> simp [Pole]
@[simp] lemma Pole_bezel:Pole (-1)=bezel:=by apply tone <;> simp [Pole,bezel]
@[simp] lemma Pole_one:Pole 1=1:=by apply tone <;> simp [Pole]
lemma Pole_zpow(n:ℤ):Pole (u^n)=(Pole u)^n:= map_zpow ({toFun:= Pole,map_one':=Pole_one,map_mul':=fun i j=>(Pole_pow i j).symm}:ℂˣ→*Two) _ n
lemma Pole_nat(n:ℕ):Pole (u^n)=(Pole u)^n:= map_pow ({toFun:= Pole,map_one':=Pole_one,map_mul':=fun i j=>(Pole_pow i j).symm}:ℂˣ→*Two) _ n
lemma scales: rehome (Pole u) (Head a)=Head ((u:ℂ)^2*a):= by apply tone <;> simp [rehome,Head,Pole,pow_two,mul_left_comm,mul_comm,mul_assoc, u.ne_zero] -- maybe
lemma dart: rehome turn (Head a) = Tail (-a):=by apply tone <;> simp [rehome,turn,Head,Tail]
-- topology via four shadows
example:IsTopologicalGroup Two:=inferInstance
@[fun_prop] lemma cA:Continuous A:= by change Continuous (fun g:Two => val g 0 0); unfold val; fun_prop
@[fun_prop] lemma cB:Continuous B:= by change Continuous (fun g:Two => val g 0 1); unfold val; fun_prop
@[fun_prop] lemma cC:Continuous C:= by change Continuous (fun g:Two => val g 1 0); unfold val; fun_prop
@[fun_prop] lemma cD:Continuous D:= by change Continuous (fun g:Two => val g 1 1); unfold val; fun_prop
lemma fromFour {ι:Type*}[TopologicalSpace ι](a b c d:ι→ℂ)(p:∀ i:ι,a i*d i-b i*c i=1)(h:Continuous a)(i:Continuous b)(j:Continuous c)(k:Continuous d): Continuous fun t:ι=> pin _ _ _ _ (p t):= by
 apply (Matrix.SpecialLinearGroup.isClosedEmbedding_val).isEmbedding.continuous_iff.mpr; refine continuous_matrix fun i j=>?_ ; fin_cases i <;> fin_cases j <;> assumption
@[fun_prop] lemma cH:Continuous Head:=fromFour _ _ _ _ _ continuous_const continuous_id continuous_const continuous_const
@[fun_prop] lemma cT:Continuous Tail:=fromFour _ _ _ _ _ continuous_const continuous_const continuous_id continuous_const
@[fun_prop] lemma cP:Continuous Pole:= fromFour _ _ _ _ _ Units.continuous_val continuous_const continuous_const (by fun_prop (disch:=aesop)) -- tune val inv
end YM.Marque
