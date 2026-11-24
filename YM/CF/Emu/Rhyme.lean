import YM.CF.Onyx.Quod
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{j:ℕ}{M:Jill.Male}{s r R c:ℝ}{d:Candle}
variable (S:Slide N d)
def rake (k:Site N)(x:Slot):Stag N:= (k-wrap _ (S.z x),x)
def trackF(U:Stag N→Peb)(x:Slot): Site N→Peb:=fun i=>U (rake S i x)
lemma ramp(k:Site N)(x:Slot): Kea.angle S (rake S k x)=glen (S.u x) k:=by simp only [Kea.angle,rake,sub_add_cancel]; rfl
def tilt (X U: Stag N→Peb)(i:Stag N):Peb:=laneP Aop (X i) (U i)
lemma tall_s(X U:Stag N→Peb): Dofu N (tilt X U)= laneP (tickA N) (Dofu N X) (Dofu N U):=by
 unfold laneP; rw [landP N, ←map_one (Dofu N), ← map_sub,←map_mul,←map_mul]; rfl -- tune list
variable {S}{U Y:Stag N→Peb}
lemma coat_v(Z:∀ i,Clad (field S j M i) Aop (portT S M j r s i) (Y i) (U i))(h:Even N.val)(k:Site N)(x:Slot)(g:r*pinch N^2<disk j M (glen (S.u x) k))(p:0<r): trackF S (tilt (portT S M j r s) U) x k = dip j M (tmap (glen (S.u x) k)):=by
 let i:=rake S k x; let A:=field S j M i; let B:=glen (S.u x) k; let P:=U i; let d:=disk j M B; have hp:0< d:= (lt_trans (by have he:= pinch_pos N; positivity) g)
 have ht: portT S M j r s i=1:=by
    have he:i∉risky S j M r:=fun f=>not_le_of_gt g (by have he:= (mem_filter.mp f).2; change high_d M S i j≤_ at he; unfold high_d at he; rw [show Kea.angle S i=_ from ramp S k x] at he; exact he)
    simp only [portT,openW,Pi.add_apply,Pi.one_apply,Pi.smul_apply,shake,if_neg he,smul_zero,add_zero]
 have he:=Z i; rw [ht] at he; have hx:Kea.angle S i=B:=ramp S k x; have hh:= (crestQ j M S h i).2.2.1; have hc: d= high_d M S i j:=by rw [high_d,hx]
 have hl:d • P=A*Aop:=by
    have hg:=he.left; rw [mul_one] at hg; have hh:Aop*A*Aop=d • Aop:=by rw [hc]; exact hh -- tune
    rw [← show P*Aop=P from he.stem,←Matrix.mul_smul, ← hh, ←mul_assoc P (_*_ ) Aop]; exact congrArg (·*Aop) hg
 change minA*portT S M j r s i*P=_; rw [ht,mul_one]; have hℂ:(d:ℂ)≠0:=by exact_mod_cast hp.ne'
 unfold dip; rw [← pear, ice_h h k]; change _=(d:ℂ)⁻¹ • (minA*bar j M.val (tmap B)*Aop); rw [show bar j _ (tmap B)=A by unfold A field; rw [hx],mul_assoc,←hl,Matrix.mul_smul, ← BZ.ofReal_action,inv_smul_smul₀ hℂ]
lemma attire (Z:∀ i,Clad (field S j M i) Aop (portT S M j r s i) (Y i) (U i))(h:Even N.val)(p:0<r)(u:0<c)(b:∀ i,‖U i‖≤ c*N.val)(t:∀ i,‖portT S M j r s i‖ ≤ c)(x:Slot): FormU (S.u x) j M r (c^2*Real.pi) (trackF S (tilt (portT S M j r s) U) x):=by
 refine ⟨fun k g=>coat_v Z h k x g p,fun k g=>?_⟩
 let i:=rake S k x; let X:=portT S M j r s i; change ‖minA*X* U i‖ ≤ _; have hv:= (norm_mul_le minA X).trans ((mul_le_mul (IsStarProjection.norm_le _ minA_p) (t i) (norm_nonneg _) zero_le_one).trans_eq (one_mul c)); have hp:= nPos N
 exact (norm_mul_le ..).trans ((mul_le_mul hv (b _) (norm_nonneg _) u.le).trans_eq (by unfold pinch; field_simp)) -- tune
end YM.CF.Emu
