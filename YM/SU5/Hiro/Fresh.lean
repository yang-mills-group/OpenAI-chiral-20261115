import YM.CF.Matter.Anomaly
import YM.CF.Cascade.Linen
import YM.SU5.Regis.Easel
import YM.Next.STATIONARY.Joint.OnShell
/-!
# The common SU adjoint direction in the matter Lie current.
No generation-dependent fitting. Keeps also the precise Dynkin trace coefficient
in physical normalization.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 160000
noncomputable section
namespace YM.CF.Hiro
open Lattice Laurent Finset Fock SU Cascade Function
open scoped MatrixOrder Matrix BigOperators Classical InnerProductSpace Kronecker Matrix.Norms.L2Operator ContDiff Topology
attribute [local instance] opCStarAlgebra
-- indices in third-generation as well as others
abbrev ColorL:= SU.group.Color
private def η : Op F→ₗ[ℝ] Op Ten where
 toFun:= ExTwo.gen
 map_add' a b:= by ext i j; rw [Matrix.add_apply,gen_entry,gen_entry,gen_entry]; simp only [Matrix.add_apply]; ring
 map_smul' a b:= by ext i j; rw [Matrix.smul_apply,gen_entry,gen_entry]; simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]; ring
private def gL : Op F→ₗ[ℝ] Op SU.Slot where
 toFun:= dMatter
 map_add' x y:=by
    have hv: sheetD (x+y)=sheetD x+sheetD y:=by
       ext i j; rw [sheetD,show ExTwo.gen (x+y)= ExTwo.gen x+ExTwo.gen y from map_add η _ _, cc_add]; cases i <;> cases j <;> simp [sheetD, Join.both]
    unfold dMatter; rw [hv]; exact Matrix.kronecker_add ..
 map_smul' t x:=by
    have hv: sheetD (t • x)=t • sheetD x:=by
       ext i j; rw [sheetD,show ExTwo.gen (t•x)= t • ExTwo.gen x from map_smul η t _,e1]; cases i <;> cases j <;> simp [sheetD,Join.both]
    unfold dMatter; rw [hv]; exact Matrix.kronecker_smul ..
where e1 (t:ℝ)(A:Op F):cc (t • A)=t•cc A:=by ext i j; simp [cc_apply,Complex.real_smul]
private def greenL : ColorL →ₗ[ℝ] Op Slot:= gL.comp group.colorMat
-- `green` is skew, `ting` is Hermitian
noncomputable def walkC : ColorL→ₗ[ℝ] Op Slot:={greenL with
 toFun:=ting, map_add':=fun x y=>by unfold ting; rw [show green (x+y)= green x+green y from map_add greenL x y, smul_add], map_smul':=fun t x=>by unfold ting; rw [show green (t • x)=t • green x from map_smul greenL t x]; exact smul_comm ..}
lemma walk_price (x:ColorL): walkC x= -Complex.I • SU.dMatter (SU.group.colorMat x):=rfl
lemma walk_star(x:ColorL):star (walkC x)= walkC x:= tingP _
lemma walk_trace(x:ColorL):Matrix.trace (walkC x)=0:=by
 let X:=group.colorMat x; have hp:=Thera.league.mp (group.colorMat_mem x); rw [walk_price,Matrix.trace_smul,(local_polynomial X ⟨hp.1,hp.2⟩).1,smul_zero]
lemma walk_rotate (u:E)(x:ColorL):walkC (group.adjoint u x)= twist (matter u) (walkC x):=by
 let a:=group.adjoint u x; have hv(t:ℝ):rollH a t=u*rollH x t*u⁻¹:=by unfold rollH; rw [← map_smul (group.adjoint u)]; exact ProjectorNext.Equivariance.exp_adjoint ..
 let U:UNI Slot:= matter u
 have hx:green a=twist U (green x):=by
    apply (greenD a).unique; have he(t): (matter (rollH a t)).val=twist U (matter (rollH x t)).val:= by rw [hv,map_mul,map_mul,map_inv]; rfl
    simp_rw [he]; let L: (Op Slot) →L[ℝ] (Op Slot):=(twist U).toAlgEquiv.toLinearMap.toContinuousLinearMap; exact L.hasFDerivAt.comp_hasDerivAt 0 (greenD x)
 change -Complex.I • green a=twist U (-Complex.I • green x); rw [hx,twist_scalar]
lemma walk_square (x:ColorL): Matrix.trace (walkC x * walkC x)= 60*(‖x‖^2:ℝ):=by
 by_cases h:x=0; · rw [h,map_zero]; simp
 let A:=walkC x; let t:=‖x‖; have ht:t>0:= norm_pos_iff.mpr h; let y:= t⁻¹ • x; have hy: ‖y‖=1:=by unfold y; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le]; exact inv_mul_cancel₀ ht.ne'
 have hx:(t • walkC y)=A:=by unfold A; rw [← map_smul, smul_inv_smul₀ ht.ne' x]
 change Matrix.trace (A*A)= _; rw [←hx,Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.trace_smul, show Matrix.trace (walkC y*walkC y)=(60:ℂ) from tingV y hy]; simp only [Complex.real_smul,t,Complex.ofReal_mul,Complex.ofReal_pow]; ring
lemma walk_bill (x y:ColorL) : Matrix.trace (walkC x * walkC y)=60*(inner ℝ x y:ℝ):=by
 let A:=walkC x; let B:=walkC y; have h:= walk_square (x+y); rw [map_add, add_mul,mul_add,mul_add,Matrix.trace_add,Matrix.trace_add,Matrix.trace_add,walk_square,walk_square,Matrix.trace_mul_comm B A,norm_add_sq_real] at h
 push_cast at h ⊢; apply add_left_cancel (a:= -(60*(‖x‖:ℝ)^2 : ℂ)) -- rewrite ring via solve
 -- linear_combination supported ℂ
 linear_combination h/2
end YM.CF.Hiro
#print axioms YM.CF.Hiro.walk_bill
#print axioms YM.CF.Hiro.walk_rotate
