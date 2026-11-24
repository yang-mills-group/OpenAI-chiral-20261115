import YM.CF.Aroma.Park
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
section map
variable {n:Type*}[DecidableEq n][Fintype n]
-- Det real path through complex Ops
lemma TaylorA {f:ℝ→Op n}{B:Op n}{t:ℝ}(h:IsUnit (f t))(hf: HasDerivAt f B t):HasDerivAt (fun x=>(f x).det) (((f t)⁻¹*B).trace*(f t).det) t:=by
 let V:=f t
 let T : ContinuousMultilinearMap ℂ (fun _ : n => n→ℂ) ℂ:=
   { Matrix.detRowAlternating.toMultilinearMap with
     cont:=by change Continuous fun A:n→ n→ℂ=> (Matrix.of A).det; apply Continuous.matrix_det; apply continuous_matrix; intro i j; simp only [Matrix.of_apply]; fun_prop }
 let D := T.restrictScalars ℝ
 have he(i j:n):HasDerivAt (fun x=> f x i j) (B i j) t:=by
   let L:Op n→ₗ[ℝ]ℂ:= ⟨⟨fun x=> x i j,fun a b=>rfl⟩,fun a b=>rfl⟩; exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf
 have hx:= (D.hasFDerivAt _).comp_hasDerivAt t (show HasDerivAt (fun x (i j:n)=> f x i j) (fun i j=> B i j) t from hasDerivAt_pi.mpr fun i=> hasDerivAt_pi.mpr fun j=>he i j)
 let G:= B*V⁻¹
 have ht:G*V=B:=by unfold G V; rw [mul_assoc,(Fock.live h).2,mul_one]
 have hl(i:n): Matrix.det (V.updateRow i (B i))= G i i * V.det:=by
    have hi : (∑ k,G i k • V k)=B i:=by funext m; rw [Finset.sum_apply]; exact congr_fun (congr_fun ht i) m
    rw [← hi]; exact Matrix.det_updateRow_sum ..
 rw [ContinuousMultilinearMap.linearDeriv_apply] at hx; rw [Matrix.trace_mul_comm, Matrix.trace,sum_mul]
 change HasDerivAt (fun x=>(f x).det) (∑ i,G i i*V.det) t; change HasDerivAt _ (∑ i, Matrix.det (V.updateRow i (B i))) t at hx
 simp_rw [hl] at hx; exact hx
lemma inverseH {f:ℝ→Op n}{B:Op n}{t:ℝ}(h:IsUnit (f t))(hf:HasDerivAt f B t): HasDerivAt (fun x=>(f x)⁻¹) (- ((f t)⁻¹*B*(f t)⁻¹)) t:=by
 obtain ⟨x,e⟩:=h; simp_rw [Matrix.nonsing_inv_eq_ringInverse]; rw [← e, Ring.inverse_unit]; have ht:= hasFDerivAt_ringInverse (𝕜:=ℝ) x; rw [e] at ht; exact ht.comp_hasDerivAt t hf
end map
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}{J:InJ n N}
def cash(F:Cab n N) :=-(1/2:ℝ)*Real.log F.det.re
def palmH (J:InJ n N)(x:Air N):ℝ:= deriv (deriv fun s:ℝ=> cash (Met J (s • x))) 0
def room(J:InJ n N)(q:Momentum):= palmH J (amber q)+palmH J (zinnia q)
lemma plateH {f:ℝ→Cab n N}{B: Cab n N}{t:ℝ}(h:IsUnit (f t))(hk:star (f t)=f t)(g:HasDerivAt f B t): deriv (fun s:ℝ=> cash (f s)) t= -(1/2:ℝ)*(((f t)⁻¹* B).trace).re:=by
 let K:=(f t).det
 have he: K≠0:= isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp h)
 have hu:star K=K:=by have hh:= congr_arg Matrix.det hk; rw [Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose] at hh; exact hh
 have hp: K.im=0:= Complex.conj_eq_iff_im.mp hu
 have hv: K.re≠0:= fun p=>he (Complex.ext p hp)
 have hd:HasDerivAt (fun x=>(f x).det.re) ((((f t)⁻¹*B).trace*K).re) t:= Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (TaylorA h g)
 have hx := (hd.log hv).const_mul (-(1/2:ℝ)); apply HasDerivAt.deriv; rw [Complex.mul_re,hp,mul_zero,sub_zero] at hx; refine hx.congr_deriv ?_; change -(1/2)*(_*K.re/K.re)= _; field_simp
namespace Foot
variable {T:Op n}{j:ℕ}(P:Foot T j M J)
include P
lemma issue(x:Air N): let V:=Met J; let m:=(V 0)⁻¹; let f:=JD V x; let H:= Matrix.trace (m*f*m*f - m* JG V x x); palmH J x=(1/2:ℝ)*H.re:=by
 intro V m f H
 let L(s:ℝ):= s • x; let Q:=fderiv ℝ V; let F:= V ∘ L; let B(s:ℝ):= Q (L s) x; let G(s):= (((F s)⁻¹*B s).trace).re
 have hx:L 0=0:=zero_smul ..; have he B : HasDerivAt L x B:=by simpa [L] using ((hasDerivAt_id' B).smul_const x)
 have hh:ContDiffAt ℝ ω V 0:=met_ray _ P.smooth; have hv: IsUnit (F 0):=by unfold F; rw [Function.comp_apply,hx]; exact P.census.1
 have hG (t:ℝ)(h: DifferentiableAt ℝ V (L t)):HasDerivAt F (B t) t:= (h.hasFDerivAt.comp_hasDerivAt t (he t))
 have hg: DifferentiableAt ℝ V (L 0):= hx.symm ▸ hh.differentiableAt (by simp); have hf := hG 0 hg
 have hK : deriv (fun s=> cash (F s))=ᶠ[𝓝 (0:ℝ)] fun t=>-(1/2:ℝ)*G t :=by
    have hu: Tendsto L (𝓝 0) (𝓝 0):= hx ▸ ((he 0).continuousAt : Tendsto L (𝓝 0) (𝓝 (L 0))) -- tune
    have hx' := (hf.continuousAt).eventually (Units.isOpen.mem_nhds hv) -- tune
    filter_upwards [hu.eventually (hh.eventually (by simp)),hx'] with i h' hi; exact plateH hi (vis_a _ _) (hG _ (h'.differentiableAt (by simp)))
 let p:=JG V x x
 have hp:HasFDerivAt Q (JG V) (L 0):= hx.symm ▸ ((hh.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)).hasFDerivAt
 have hl:HasDerivAt B p 0:=(ContinuousLinearMap.apply ℝ (Cab n N) x).hasFDerivAt.comp_hasDerivAt 0 (hp.comp_hasDerivAt 0 (he 0))
 let r:Cab n N→L[ℝ]ℂ:=(Matrix.traceLinearMap _ _ _).toContinuousLinearMap
 have hb : HasDerivAt G (-H.re) 0:=by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (r.hasFDerivAt.comp_hasDerivAt 0 ((inverseH hv hf).mul hl))
    refine hd.congr_deriv ?_; rw [show (F 0)⁻¹=m by unfold F; rw [Function.comp_apply,hx],show B 0=f by unfold B; rw [hx]; rfl]; change ((-(m*f*m)*f + m*p).trace).re = (- H.re); unfold H; simp only [neg_mul,Matrix.trace_add, Matrix.trace_neg,Matrix.trace_sub,Complex.add_re,Complex.neg_re, Complex.sub_re,p]; abel
 rw [palmH]; change deriv (deriv fun s=> cash (F s)) 0=_; rw [hK.deriv_eq, ((hb.const_mul _).deriv)]; ring
end Foot
end YM.CF.Aroma
