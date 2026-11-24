import YM.CF.BProof.Bias.Tide
/-! Discrete tangential fiber within full spin operator. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint
open Fir Laurent Rush Bloch Next.Free BZ
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}(i:Axis)(p q:Per N)
abbrev ht(i:Single N): Per N:= fsite i 0
def Label := univ.filter fun x:Site N=> x i=p
@[simp] lemma labelled(x:Site N): x∈ Label i p ↔ x i=p:= by simp [Label]
abbrev wing := modality (Label i p)
abbrev ζ(p:Per N):= BZ.phase (principal p)
lemma wing_eq: axisShift N i * wing i p = ζ p • wing i p:=by
 rw [relic_shift,wing,modality,relic_mul,relic_scalar]; apply congrArg; funext x; by_cases g:x i=p <;> simp [thinK,g,pm]
lemma wing_eq_of {T:Op (Single N)}(h:axisShift N i * T=ζ p • T): wing i p*T=T:=by
 let f(x:Site N): Op SpinIdx:= (ζ (x i)-ζ p)⁻¹ • 1; let A:= axisShift N i; let B:=wing i p; let U:= relic f
 have H: U*(A-ζ p • 1)=1-B:=by
    unfold U A B wing modality; rw [relic_shift,← relic_one,relic_scalar,relic_sub,relic_sub,relic_mul]; -- direction
    apply congrArg; funext x; by_cases g:x i=p
    · simp [thinK,g,pm,f]
    have he:ζ (x i)-ζ p≠0:=sub_ne_zero.mpr fun h=> g (phase_inj _ _ h); change f x * (ζ (x i) • 1-ζ p • 1)=(1:Op SpinIdx)-thinK (Label i p) x; unfold f; rw [← sub_smul,Matrix.smul_mul,one_mul,inv_smul_smul₀ he]; simp [thinK,g]
 have ht:(1-B)*T=0:=by rw [←H,mul_assoc,sub_mul,Matrix.smul_mul,one_mul,h,sub_self,mul_zero] -- tune h rw A
 exact (sub_eq_zero.mp (show T-B*T=0 from (by rw [sub_mul,one_mul] at ht; exact ht))).symm
lemma wing_sum : ∑ p:Per N,wing i p=1:=by
 unfold wing modality; rw [relic_sum, ← relic_one]; apply congrArg; funext x; rw [Finset.sum_apply,sum_eq_single (x i)]; simp [thinK]; intro p _ h; simp [thinK,Ne.symm h]; simp
lemma wing_unit : axisShift N i ∈ unitary _:=by
 let f(z:Site N):Op SpinIdx:= (ζ (z i)) • 1; have h(t:Per N): star (ζ t)*ζ t=1:= by rw [mul_comm]; exact phase_one _
 rw [relic_shift i]; constructor -- uses implicit?
 all_goals change (HMul.hMul _ _)=(1:Op (Single N)); rw [relic_star,relic_mul,← relic_one]; apply congrArg; funext z; first | exact (show star (f z)*f z=(1:Op SpinIdx) from (by unfold f; rw [star_smul,star_one,Matrix.smul_mul,one_mul,smul_smul,h,one_smul]))|exact (show f z*star (f z)=(1:Op SpinIdx) from (by unfold f; rw [star_smul,star_one, Matrix.smul_mul,one_mul,smul_smul, mul_comm (ζ _),h,one_smul])) -- tune
lemma shades (C:Op (Single N))(p q:Per N){v:ℂ}(h:axisShift N i*C=v • C*axisShift N i)(u: v * ζ p=ζ q): wing i q*C*wing i p=C*wing i p:=by
 have he: axisShift N i*(C*wing i p)=ζ q • (C*wing i p):=by rw [←mul_assoc,h,mul_assoc,wing_eq,Matrix.smul_mul,Matrix.mul_smul,smul_smul,u]
 rw [mul_assoc]; exact wing_eq_of i q he
lemma wave_comm (P: Op (Single N))(g: Commute P (axisShift N i))(h:IsSelfAdjoint P):Commute (wing i p) P:=by
 have ht:P*wing i p=wing i p*P*wing i p:= (shades i P p p (v:=1) (by rw [one_smul]; exact g.symm.eq) (one_mul _)).symm; have hu:=congrArg star ht; simp_rw [star_mul,h.star_eq,show star (wing i p)=_ from (mode_p _).isSelfAdjoint] at hu; exact hu.trans ((mul_assoc ..).symm.trans ht.symm)
lemma modal_bridge (W:UNI (Single N)){f:ℂ}(x:axisShift N i*W.val=f • W.val*axisShift N i)(h:f*ζ p=ζ q): W.val*wing i p= wing i q*W.val:=by
 have hp:f≠0:=by intro u; rw [u,zero_mul] at h; exact Complex.exp_ne_zero _ h.symm
 let A:=axisShift N i; have hW:= W.property
 have he: A*star W.val=f⁻¹ • star W.val*A := by
   let V:=W.val
   have h1:A*V=f • (V*A):=by rw [←Algebra.smul_mul_assoc]; exact x
   have h2:A=(A*V)*star V:=by rw [mul_assoc, hW.2,mul_one]
   have hv: f⁻¹ • (star V*A)=A*star V:=calc
      _ = f⁻¹ • (star V*((f • (V*A))*star V)):=by rw [← h1,← h2]
      _ = _:= by rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,inv_smul_smul₀ hp, ← mul_assoc,←mul_assoc,hW.1,one_mul]
   exact hv.symm.trans (Algebra.smul_mul_assoc ..).symm
 let V:=wing i p; let T:=wing i q; have hb:T*W.val*V=W.val*V:= shades i W.val p q x h; have hv:V*star W.val*T=star W.val*T:=shades i _ q p he (by rw [←h,← mul_assoc,inv_mul_cancel₀ hp,one_mul]); have hu:= congrArg star hv; simp_rw [star_mul,star_star] at hu; rw [show star V=V from (mode_p ..).isSelfAdjoint,show star T=T from (mode_p ..).isSelfAdjoint] at hu; exact hb.symm.trans ((mul_assoc ..).trans hu)
lemma axis_t (x:i≠0):Span ht 0 (axisShift N i):=by
 intro a b g; rw [axis_shift i a]; dsimp only; split; swap; rfl
 rename_i t; have h: ht a=ht b:=by unfold ht; rw [show fsite b=a.1.1+step i from t.symm]; simp [fsite,Ne.symm x]
 rw [h,d_id] at g; omega
lemma wing_t (x:i≠0): Span ht 0 (wing i p):= by
 apply (Span.comm_iff _).mpr; intro s; apply Commute.symm (wave_comm i p _ ((axis_t i (N:=N) x).comm _) (timeR_proj ..).isSelfAdjoint)
end YM.CF.BProof.Bias
