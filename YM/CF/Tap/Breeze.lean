import YM.CF.Tap.Limas
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
def waveB (z:Op Slot): Pal:= (Aop-(1/2:ℂ) • 1)⊗ₖ z
private lemma red(H:Op SpinIdx)(x:Op Slot): H⊗ₖ (1:Op Slot)*((1:Op SpinIdx)⊗ₖ x) = H⊗ₖ x:=by rw [op_kron_mul,one_mul,mul_one]
lemma symWave(z:Op Slot)(p:Mind z): AxisP (fun _=> waveB z):=by
 let Z:=1+(1:Op (coneA Slot)); let d:=Aop-(1/2:ℂ) • 1
 have hf:star d=d:=by unfold d; rw [star_sub,Aadj,star_smul,star_one]; norm_num
 refine ⟨fun s b U hp q _=>?_,fun g q _=>?_,fun _=>differentiableAt_const _⟩
 · have hk:sings b (xtra b).V z=z:=by change twist 1 _=z; rw [one_des]; cases b; rfl; exact p.realV
   rw [waveB,Scroll.wingK,hk]
   have he : sings b U Aop=swapX (detX s) Aop:=by have he:=angleX hp true; change sings b U Aop=_ at he; cases hx:detX s <;>rw [hx] at he<;> exact he
   rw [singT,win_l,map_sub, ←singT,he,win_c,win_i, twist_scalar, map_one, show cSignX b (1/2)=1/2 from (by cases b<;> norm_num [cSignX])]; cases hx:detX s; rfl
   change (1-Aop-(1/2:ℂ) • _)⊗ₖ z= -star (d⊗ₖ z); rw [op_star_kron,hf,p.adj,show 1-Aop-(1/2:ℂ) • _= -d by unfold d; module,op_kron_neg]
 change (d⊗ₖ z)*(1⊗ₖ _)=(1⊗ₖ _)*(d⊗ₖ z); rw [op_kron_mul,op_kron_mul,mul_one,one_mul,p.firm g]
variable (j:ℕ)(k:1≤j)(M:Male)
include k
lemma boot_wave (z:Op Slot)(i:Axis): HasDerivAt (fun s=> potion j M (fun _=>waveB z) (bout i s)) (petal i⊗ₖ z) 0:=by
 let P(t):= boot j M (bout i t); let d:=Aop-(1/2:ℂ) • 1; let h:= bins Slot
 let U:Pal:=(1:Op SpinIdx)⊗ₖ z
 have he:P 0=1-h:=by unfold P; rw [bout_zero,boot_o]
 have hp:(fun s=> potion j M (fun _=>waveB z) (bout i s))=ᶠ[𝓝 0] fun s=> (1-P s)*h*P s*U:=by
    filter_upwards [Ps_b j k M i] with t ht; have hp:P t*P t=P t:=ht.1; have hh: P t*U=U* P t:=by unfold U P boot; rw [op_kron_mul,op_kron_mul,mul_one,mul_one,one_mul,one_mul]
    change _ * (d⊗ₖ z)* P t=_
    rw [← red,show d⊗ₖ (1:Op Slot)=h-(1/2:ℂ) • 1 from (by simp only [h,bins,d,sub_eq_add_neg,Matrix.add_kronecker,op_kron_neg,Matrix.smul_kronecker,Matrix.one_kronecker_one])]; change (1-P t)*((h-_) *U) *P t=_; rw [←mul_assoc,mul_assoc, ←hh,←mul_assoc]; congr 1; rw [mul_sub, sub_mul (a:=(1- P t)*h),Matrix.mul_smul, Matrix.smul_mul,mul_one,show (1-P t)*P t=0 by rw [sub_mul,one_mul,hp,sub_self], smul_zero,sub_zero] -- tune a:
 let Q(t):=1-P t; let X:=petal i⊗ₖ (1:Op Slot)
 have ht: HasDerivAt P (boom i) 0:=barox j k M i
 refine HasDerivAt.congr_of_eventuallyEq ?_ hp
 have hg: HasDerivAt Q (-boom i) 0:= ht.const_sub _
 apply ((((hg.mul_const h).mul ht).mul_const U)).congr_deriv
 change (_*P 0+Q 0*h*_)*U= _; rw [he,show Q 0=h from (by unfold Q; rw [he]; abel),neg_mul,neg_mul,mul_assoc (boom i),mul_sub,mul_one,binsSq, sub_self,mul_zero,neg_zero,zero_add,boom_A]; exact red ..
lemma wave_z (z:Op Slot):zeus j M (fun _=>waveB z)=z:=by
 unfold zeus zest; rw [(boot_wave j k M z 0).deriv]; simp [spa_v]
omit k
lemma zeus_cost : ∃ C:ℝ, 0<C ∧∀ (j:ℕ),1≤j →∀ (M:Male)(V:Momentum→Pal),AxisP V → ‖zeus j M V‖ ≤ C*(‖V 0‖+‖deriv (fun z=> V (bout 0 z)) 0‖):=by
 let U:=coneA Slot; let A:=bins Slot
 let B: (Pal×Pal)→Pal:=fun X=> (-boom 0*X.1 + A*X.2)*(1-A)+A*X.1*boom 0
 let F:Op Slot→ₗ[ℂ] Pal:={ toFun:=fun X=> petal 0 ⊗ₖ X,map_add':=fun _ _=>Matrix.kronecker_add ..,map_smul':=fun _ _=>Matrix.kronecker_smul .. }
 let P: (Pal×Pal)→L[ℂ] Pal:=(show _→ₗ[ℂ] Pal from {
    toFun:=B,map_add':=fun a b=>by simp only [B,Prod.snd_add,Prod.fst_add,mul_add,add_mul]; abel
    map_smul':=fun a b=>by change (-boom 0* (a • b.1)+ A*(a • b.2))*(1-A)+A*(a • b.1)*boom 0=a • B b; simp only [Matrix.mul_smul, Matrix.smul_mul, ←smul_add, B] }).toContinuousLinearMap
 obtain ⟨E,H⟩:=F.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (spa_i 0)); let E':= E.toContinuousLinearMap
 refine ⟨max 1 (‖E'.comp P‖),lt_max_of_lt_left one_pos,?_⟩
 intro j h M V e; let X:= (V 0,deriv (fun s=> V (bout 0 s)) 0); let W:=zeus j M V
 have ht:zest j M V 0 = P X:=by
    let b:=barox j h M 0; unfold zest; rw [show deriv (fun t=> potion j M V (bout 0 t)) 0= _ from (((((b.const_sub (1:Pal)).mul (e.age 0).hasDerivAt).mul b)).deriv)]; unfold X; change _= B _ -- LHS formula
    simp only [B,A,bout_zero,boot_o]; simp; rw [boot_o,sub_sub_cancel]
 change ‖W‖ ≤ _; rw [←show (E'.comp P X)= W from (by change E (P X)=_; rw [←ht,(normalization j h M e).2.2 0]; exact DFunLike.congr_fun H W)]; apply ((E'.comp P).le_opNorm X).trans; gcongr; exact le_max_right ..; rw [Prod.norm_def]; exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
end YM.CF.Tap
