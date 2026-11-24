import YM.CF.Aroma.Cyclone
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}{J:InJ n N}
namespace Foot
variable {T:Op n}{j:ℕ}(P:Foot T j M J)
include P
set_option maxHeartbeats 800000 in
lemma calls(x:Air N)(h:Dir x): palmH J (lop x)=0:=by
 let v:=lop x; let K:=ski T x; let Q(t:ℝ):=exp (t • K); let A:=flatV n N
 have he:star K= -K:=tiltQ T P.realT _
 have hv(t:ℝ): Q t∈unitary (Cab n N):=by
    letI:NormedAlgebra ℚ (Cab n N):= NormedAlgebra.restrictScalars ℚ ℝ (Cab n N)
    apply exp_mem_unitary_of_mem_skewAdjoint; rw [show (t • K) ∈ skewAdjoint (Cab n N) ↔ star (t • K)= -(t • K) from Iff.rfl]; simp only [star_smul,star_trivial,he,smul_neg]
 have hF : Commute A K:=by
    change jump _ _*jump _ _=_; unfold A K flatV ski; rw [jump_mul,jump_mul]; congr 1; ext1 i; simp only [Equiv.refl_apply, Matrix.smul_mul,Matrix.mul_smul,bins,thrust,op_kron_mul,one_mul,mul_one]
 have hU(t:ℝ):Commute A (Q t):= (hF.smul_right t).exp_right -- tune
 have hh : (fun s:ℝ=> cash (Met J (s • v)))=ᶠ[𝓝 0] fun _=> cash (Met J 0):=by
    filter_upwards [P.peak x h] with s hs; change J (s • v)= Q s*J 0*star (Q s) at hs
    let V : UNI (Tx N n):=⟨Q s,hv s⟩
    have hu: twist V A=A:=by rw [twist_formula,show V.val*A=A*V.val from (hU s).eq.symm,mul_assoc,V.property.2,mul_one]
    change cash _=cash _; rw [show Met J (s • v)= twist V (Met J 0) from ?_]; swap
    · rw [Met,Met,hs,show Q s*J 0*star (Q s)=twist V (J 0) from (twist_formula V (J 0)).symm,map_add,map_mul,map_star,map_sub,map_one,show twist V (flatV n N)=_ from hu]
    unfold cash; rw [twist_formula,Matrix.det_mul,Matrix.det_mul]; rw [show (V.val.det*Matrix.det (Met J 0))*_=Matrix.det (Met J 0)*(V.val.det*(star V.val).det) by ring, ← Matrix.det_mul,V.property.2, Matrix.det_one,mul_one]
 change deriv (deriv fun s:ℝ=> cash (Met J (s • v))) 0=_; rw [hh.deriv.deriv_eq]; simp
end Foot
lemma aiming {T:Op n}{j:ℕ}(P:Foot T j M J)(e:16≤N.val):room J (why N)=0:=by
 let q:=why N; let c:=1-vi N; let r:=pinch N; have hr:0<r:=pinch_pos _
 have hg: r≤Real.pi:=by unfold r pinch; exact div_le_self Real.pi_pos.le (by exact_mod_cast N.property)
 have hc:c≠0:=by
    apply sub_ne_zero.mpr; intro t
    have he: Complex.exp ((r:ℂ)*Complex.I)=Complex.exp 0:= by change vi N=_; rw [←t,Complex.exp_zero]
    have hp:=Real.pi_pos
    have h:= Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ he; simp_all
    all_goals simp_all <;> linarith
 let F(z:Site (More N)):= c⁻¹*dialH q z
 let x:Air N:=fun z=> (F z).re; let y:Air N:=fun z=> (F z).im
 have he : ∀ z i, i ≠ (1:Axis)→ F (z+step i)= F z:=by intro z i k; unfold F q; rw [hymn, if_neg k,one_mul]
 have hp(z):F z-F (z+step (1:Axis))=dialH q z:=by unfold F q; rw [hymn, if_pos rfl, ← mul_sub,show dialH _ _-_= c*dialH (why N) z by unfold c; ring]; field_simp
 unfold room; rw [show (amber (why N):Air N)=lop x from funext fun z=> (congr_arg Complex.re (hp z)).symm, show zinnia _=lop y from funext fun z=> (congr_arg Complex.im (hp z)).symm,P.calls x (fun i j h=>congr_arg Complex.re (he i j h)), P.calls y (fun i j h=>congr_arg Complex.im (he i j h)),add_zero]
namespace Foot
variable {T:Op n}{j:ℕ}(P:Foot T j M J)
include P
lemma coinsY(x:Air N):flatV n N * JG (Met J) x x = JG (Met J) x x:=by
 let V:= Met J; let Q:=flatV n N; let L(z):=fderiv ℝ V z x
 let B:Cab n N→L[ℝ] Cab n N:= ContinuousLinearMap.mul ℝ (Cab n N) Q
 have hv := met_ray _ P.smooth; have hx:HasFDerivAt L _ 0:= (ContinuousLinearMap.apply ℝ (Cab n N) x).hasFDerivAt.comp 0 (((hv.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt)
 have he : B ∘ L =ᶠ[𝓝 0] L :=by
   let G(z):= V z-(1-Q)
   have hh : B ∘ V=ᶠ[𝓝 0] G:= pose_cut P.heft
   filter_upwards [eventually_eventually_nhds.mpr hh,hv.eventually (by simp)] with z hz hu
   have hy:= (hu.differentiableAt (by simp)).hasFDerivAt
   exact DFunLike.congr_fun (((B.hasFDerivAt.comp z hy).congr_of_eventuallyEq (show B ∘ V=ᶠ[𝓝 z] G from hz).symm).unique (hy.sub_const (1-Q))) x
 exact DFunLike.congr_fun (((B.hasFDerivAt.comp 0 hx).congr_of_eventuallyEq he.symm).unique hx) x
end Foot
end YM.CF.Aroma
