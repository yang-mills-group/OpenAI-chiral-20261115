import YM.SU5.Reconstruction.Marque.Sew
import YM.SU5.Reconstruction.Trap.Pilot
set_option autoImplicit false
noncomputable section
namespace YM.Marque.Flow
open Function Set Filter Matrix Real Complex
open scoped Matrix MatrixGroups Topology InnerProductSpace Classical
-- canonical
abbrev clock : Axis := 3
variable (g h:Two) (x y:E4)
noncomputable def herm : Mat:=
 !![(x 3:ℂ)+x 2, (x 0:ℂ)+(x 1:ℂ)*Complex.I;(x 0:ℂ)-(x 1:ℂ)*Complex.I, (x 3:ℂ)-(x 2:ℂ)]
noncomputable def out (p:Mat):E4 := WithLp.toLp 2 ![(p 0 1).re,(p 0 1).im,((p 0 0).re-(p 1 1).re)/2,((p 0 0).re+(p 1 1).re)/2]
@[simp] lemma fromHerm : out (herm x)=x:= by ext1 i; fin_cases i <;> norm_num [out,herm, Complex.mul_re,Complex.mul_im] <;> ring_nf <;> rfl
lemma visible : Injective herm:=fun i j p=>(fromHerm i) ▸ ((fromHerm j) ▸ congrArg out p) -- tune symm rewriting
@[simp] lemma formal : (herm x)ᴴ = herm x:= by ext i j :1; fin_cases i<;> fin_cases j <;> simp [herm]; abel
lemma acc(p:Mat)(h:pᴴ=p) : herm (out p)=p:= by
 let d(i:Fin 2):star (p i i)=p i i:= congrFun (congrFun h i) i; have hd(i:Fin 2):(p i i).im=0:= by have e:= congrArg Complex.im (d i); change -(p i i).im=(p i i).im at e; linarith
 have ha:star (p 0 1)=p 1 0:= congrFun (congrFun h 1) 0; ext i j :1; fin_cases i <;> fin_cases j <;>  (apply Complex.ext <;> simp [herm,out, Complex.mul_re,Complex.mul_im,hd,← ha] <;> try ring)
variable (p:Mat) (t:ℝ)
noncomputable def remit := val g*p*(val g)ᴴ
noncomputable def Motion : E4 → E4 := fun x=> out (remit g (herm x))
local notation "ρ"=>Motion
@[simp] lemma atMotion : herm (ρ g x)=remit g (herm x):= acc _ (by unfold remit; rw [conjTranspose_mul,conjTranspose_mul, conjTranspose_conjTranspose,formal]; rw [mul_assoc])
@[simp] lemma identity : ρ 1 x=x:= visible (by rw [atMotion,remit,show val 1=1 from rfl]; simp)
@[simp] lemma multiplies:ρ (g*h) x = ρ g (ρ h x):= visible (by rw [atMotion,atMotion,atMotion]; unfold remit; rw [mul_val,conjTranspose_mul]; simp only [mul_assoc]) -- argument visible
@[simp] lemma Motion_inv:ρ g (ρ g⁻¹ x)=x:= by rw [←multiplies,mul_inv_cancel,identity]
@[simp] lemma invMotion:ρ g⁻¹ (ρ g x)=x:= by rw[←multiplies,inv_mul_cancel,identity]
lemma herm_add : herm (x+y)= herm x + herm y := by ext i j :1; fin_cases i<;> fin_cases j <;> simp [herm] <;> ring
lemma herm_real : herm (t • x)= t • herm x:= by ext i j :1; fin_cases i<;> fin_cases j <;> simp [herm,real_smul] <;> ring
lemma visible_add:ρ g (x+y)= ρ g x+ρ g y:= visible (by rw [atMotion,herm_add,herm_add,atMotion,atMotion]; unfold remit; rw [mul_add,add_mul])
lemma visible_real:ρ g (t • x)=t • ρ g x:=visible (by rw[atMotion,herm_real,herm_real,atMotion]; unfold remit; rw[mul_smul_comm, smul_mul_assoc])
noncomputable def Lens : E4 ≃L[ℝ] E4:= LinearEquiv.toContinuousLinearEquiv {
 toFun:=ρ g
 invFun:=ρ g⁻¹
 map_add':= visible_add g
 map_smul':=fun c x=>visible_real g x c
 left_inv:=invMotion g
 right_inv:=Motion_inv g}
@[simp] lemma Lens_on : Lens g x= ρ g x:= rfl
lemma Lens_zero : Motion g 0=0:= map_zero (Lens g)
@[simp] lemma Lens_neg: ρ g (-x)= -(ρ g x):= map_neg (Lens g) x
-- continuity
@[fun_prop] lemma Motion_cont:Continuous (fun y: Two×E4=> Motion y.1 y.2):= by
   unfold Motion out remit herm; have hv:Continuous fun g:Two=> val g:= Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous -- topology instance caution
   fun_prop -- failures
lemma bez: val bezel= (-1:Mat):=by ext i j :1; fin_cases i <;> fin_cases j <;> simp [pin,bezel,val]-- tune
@[simp] lemma glossy: ρ bezel x=x:=visible (by rw [atMotion,remit, bez]; simp)
@[simp] lemma fixed : (herm x).det=(YM.Mink.m x:ℂ):=by
 rw [YM.Mink.m,← real_inner_self_eq_norm_sq]; unfold time; rw [PiLp.inner_apply]; rw [Matrix.det_fin_two]; simp [herm,Fin.sum_univ_castSucc, spatial]; rw [show timeAxis=(3:Axis) from rfl]; linear_combination ((x 1):ℂ)^2 * Complex.I_sq
lemma stays_m : YM.Mink.m (ρ g x)= YM.Mink.m x:= by exact_mod_cast (show (↑(YM.Mink.m (ρ g x)):ℂ)=(YM.Mink.m x:ℂ) from (by rw[← fixed,atMotion]; unfold remit; rw[det_mul,det_mul,det_conjTranspose,fixed,show (val g).det=1 from g.prop]; simp))
end YM.Marque.Flow
