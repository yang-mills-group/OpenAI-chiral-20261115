import YM.CF.Cascade.Bice
import YM.SU5.FiniteGaugeData.Brique.Wood -- norm and shape
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
/-! # Trace costs. Work package 17, extensive earnings, full chiral campaign. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Cascade Brique Real NormedSpace MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n][DecidableEq n]{A T B P Y:Op n}{a r b:ℝ}
-- open notation ComplexOrder needed!
abbrev lit (A:Op n):= IsStrictlyPositive A
abbrev TrR (A:Op n):ℝ:=A.trace.re
abbrev Canon (n:Type*) [Fintype n][DecidableEq n](a:ℝ):Op n:= a • (1:Op n)
lemma canon_map : Canon n a = algebraMap ℝ (Op n) a:= by rw [Algebra.algebraMap_eq_smul_one]
lemma canon_left (r:ℝ) (X:Op n): (Canon n r)*X = r • X:=by rw [Canon,Algebra.smul_mul_assoc,one_mul]
lemma canon_nn(h:0≤r):0≤Canon n r:= by
 exact smul_nonneg h zero_le_one
lemma canon_live (h: 0<r):lit (Canon n r):= ⟨canon_nn h.le,by rw [canon_map]; exact (isUnit_iff_ne_zero.mpr h.ne').map _⟩ -- tune
lemma lit_of_fee(h:0<a)(u:Canon n a≤A): lit A:=by
 exact ⟨(canon_nn h.le).trans u, CStarAlgebra.isUnit_of_le (Canon n a) u (canon_live h)⟩
lemma TrR_nn(h:0≤A): 0≤TrR A:=(Complex.le_def.mp ((Matrix.nonneg_iff_posSemidef.mp h).trace_nonneg)).1
lemma TrR_sub : TrR (A-B)=TrR A-TrR B:=by unfold TrR; rw [Matrix.trace_sub]; rfl
lemma TrR_le (h:A≤B): TrR A≤TrR B:=by apply sub_nonneg.mp; rw [← TrR_sub]; exact TrR_nn (sub_nonneg.mpr h)
lemma TrR_comm(A B:Op n):TrR (A*B)=TrR (B*A):=by unfold TrR; rw [Matrix.trace_mul_comm]
lemma TrR_one : TrR (1:Op n)=(Fintype.card n:ℝ):=by unfold TrR; simp -- tune
lemma TrR_star(X:Op n): TrR (star X)=TrR X:= by unfold TrR; rw [Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]; rfl
lemma TrR_add(X Y:Op n): TrR (X+Y)=TrR X+TrR Y:= by unfold TrR; rw [Matrix.trace_add]; rfl
lemma TrR_smul (r:ℝ)(X:Op n): TrR (r • X)= r*TrR X:=by unfold TrR; rw [Matrix.trace_smul]; simp
lemma mvId (P:Op n): kg (star P)= TrR (P*star P):=by rw [kgt,kg,Matrix.trace_mul_comm]
lemma lit_mulin (h:lit A): A*A⁻¹=1:= Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp h.isUnit)
lemma lit_inmul(h:lit A): A⁻¹*A=1:= mul_eq_one_comm.mp (lit_mulin h)
lemma lit_inv (h:lit A): lit (A⁻¹):= ⟨ Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp h.1).inv), live_of (lit_inmul h)⟩
lemma lit_smul (h:lit A)(e:0<a): lit (a • A):=⟨smul_nonneg e.le h.1, (canon_left a A) ▸ IsUnit.mul (canon_live e).2 h.2⟩ -- tune
lemma inv_red(h:lit A)(t:A*B=1) : A⁻¹=B:= by rw [←one_mul B, ←lit_inmul h, mul_assoc,t,mul_one]
lemma inv_fee (h:lit A) (e:0<a): (a • A)⁻¹=(a:ℝ)⁻¹ • A⁻¹:=by apply inv_red (lit_smul h e); rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_inv_smul₀ e.ne',lit_mulin h]
lemma def_beam(h:lit A) : 0<A.det:= ((Matrix.nonneg_iff_posSemidef.mp h.1).posDef_iff_isUnit.mpr h.2).det_pos
lemma def_norm(h:0≤A) : ‖A.det‖= A.det.re:= by
 have ht:0 ≤ A.det := (Matrix.nonneg_iff_posSemidef.mp h).det_nonneg
 have u: A.det=A.det.re:= Complex.ext (by simp) (Complex.le_def.mp ht).2.symm
 nth_rw 1 [u]; exact Complex.norm_of_nonneg (Complex.le_def.mp ht).1
lemma inv_order(h:lit A)(p:A≤B): B⁻¹ ≤ A⁻¹:=by rw [Matrix.nonsing_inv_eq_ringInverse,Matrix.nonsing_inv_eq_ringInverse]; exact CStarAlgebra.ringInverse_le_ringInverse p h
lemma inv_power (N:lit A) (h:0<a)(p:Canon n a ≤ A): ‖A⁻¹‖ ≤ a⁻¹:=by
 apply (CStarAlgebra.norm_le_iff_le_algebraMap A⁻¹ (inv_nonneg.mpr h.le) (lit_inv N).1).mpr; apply (inv_order (canon_live h) p).trans_eq; rw [←canon_map]; unfold Canon; rw [inv_fee (show lit (1:Op n) from ⟨zero_le_one,isUnit_one⟩) h, inv_one] -- tune name
lemma kt_can(c:ℝ)(X:Op n): kg (c • X)=c^2*kg X:=by unfold kg; rw [star_smul]; change TrR ((c • star X)*(c • X))= _; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,TrR_smul,sq] -- tune
abbrev LDiag(X:Op n) := ∑ i, ‖X i i‖ -- absolute cost
lemma trace_diag (X:Op n): |TrR X| ≤ LDiag X := by
 unfold TrR; exact (Complex.abs_re_le_norm _).trans (norm_sum_le ..)
lemma tax_diag(h:0<a)(A:Op n): LDiag A ≤ a*Fintype.card n + a⁻¹*kg A:=by
 rw [traceK,mul_sum]; let δ:=a⁻¹; rw [show a*(Fintype.card n:ℝ)=∑ i:n,a from by simp [mul_comm],←sum_add_distrib]; refine sum_le_sum fun i e=> ?_
 apply (add_le_add_right (mul_le_mul_of_nonneg_left (single_le_sum (s:=univ) (f:=fun j:n=>‖A j i‖^2) (fun i _=>sq_nonneg _) (mem_univ i)) (inv_nonneg.mpr h.le)) a).trans'; apply le_of_mul_le_mul_left _ h; have ht:= mul_inv_cancel₀ h.ne'; rw [mul_add a,←mul_assoc a (a⁻¹) _,ht,one_mul]; nlinarith only [sq_nonneg (‖A i i‖-a),mul_nonneg h.le (norm_nonneg (A i i))]
lemma TrR_c (h:0<a): |TrR A| ≤ a*Fintype.card n + a⁻¹*kg A:= (trace_diag A).trans (tax_diag h A)
lemma basis_b(X:Op n)(i:n): X i i= inner ℂ (basisKet i) (acts X (basisKet i)) :=by rw [basis_inner,basis_act]
lemma caible (X:Op n)(i:n): ‖acts X (basisKet i)‖^2 = ((star X*X) i i).re:=by
 rw [basis_b (star X*X) i,act_mul,←act_inner,star_star]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm -- tune
abbrev ReflW(A:Op n):Op n:= CFC.sqrt A
lemma refl_nn(_h:0≤A): 0≤ReflW A:= CFC.sqrt_nonneg _
lemma refl_star (h:0≤A): star (ReflW A)=ReflW A:= IsSelfAdjoint.of_nonneg (refl_nn h)
lemma refl_sq (h:0≤A): ReflW A* ReflW A=A:= CFC.sqrt_mul_sqrt_self _ h
lemma refl_live(h:lit A): lit (ReflW A):= ⟨refl_nn h.1,live_of (show ReflW A*(ReflW A*A⁻¹)=1 from by rw [←mul_assoc,refl_sq h.1,lit_mulin h])⟩
lemma TrR_quote(h:0≤A)(X:Op n): |TrR (A*X)| ≤ ‖X‖ * TrR A:=by
 let T:= ReflW A; have hp:star T=T:= refl_star h
 rw [← refl_sq h, mul_assoc, TrR_comm _ (ReflW A*X)]; -- need TrR(T X T)
 have h(t:n): ‖(T*X*T) t t‖ ≤ ‖X‖*‖acts T (basisKet t)‖^2:=by
    let x:= basisKet t; let y:= acts T x; have hh:(T*X*T) t t=inner ℂ y (acts X y):=by rw [basis_b (T*X*T) t, mul_assoc,act_mul,act_mul]; rw [←act_inner T,hp]
    rw [hh]; refine (norm_inner_le_norm ..).trans ?_; change ‖y‖ * ‖acts X y‖≤‖X‖*‖y‖^2; refine (mul_le_mul_of_nonneg_left ((acts X).le_opNorm y) (norm_nonneg _)).trans_eq ?_; change ‖y‖*(‖X‖*‖y‖)=_; ring
 apply (trace_diag _).trans; change LDiag (T*X*T) ≤ ‖X‖ * TrR (T*T); rw [show TrR (T*T)=_ from (show TrR (T*T)=kg T from by unfold kg; rw [hp]) , kg_I, mul_sum]; exact sum_le_sum fun i _=>h i -- syntax
-- C star reduced determinant. normalizer cost close independent tiny eigenvalues by base inverse mean
lemma own2(X:Op n){a:ℝ}(h:0≤a)(v:X*star X≤Canon n (a^2)): ‖X‖≤a:=by
 have he: ‖X * star X‖≤ a^2 := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg a) (by cfc_tac)).mpr (v.trans_eq canon_map)
 rw [CStarRing.norm_self_mul_star] at he; nlinarith only [h,he,norm_nonneg X]
-- logs for PSD-det called only at paid points
abbrev rueD(X:Op n):= Real.log ‖X.det‖
lemma reduced(h:lit A) : rueD A ≤ TrR A-Fintype.card n:=by
 have hv: A.PosDef:= (Matrix.nonneg_iff_posSemidef.mp h.1).posDef_iff_isUnit.mpr h.2; let T(i:n):= hv.isHermitian.eigenvalues i; have hp(i):0<T i:= hv.eigenvalues_pos i
 have hT:‖A.det‖= ∏ i, T i:=by rw [hv.isHermitian.det_eq_prod_eigenvalues]; change ‖∏ i,(T i :ℂ)‖= _; rw [←Complex.ofReal_prod]; exact Complex.norm_of_nonneg (prod_nonneg fun i _=>(hp i).le)
 unfold rueD TrR; rw [hT,Real.log_prod (by intro i _; exact (hp i).ne'),hv.isHermitian.trace_eq_sum_eigenvalues]; change ∑ i,Real.log _ ≤ (∑ i:n,(T i:ℂ)).re - _; rw [←Complex.ofReal_sum,Complex.ofReal_re]; refine (sum_le_sum (fun i _=> Real.log_le_sub_one_of_pos (hp i))).trans_eq ?_; simp [sum_sub_distrib]
lemma TrR_interest(X Y:Op n): TrR (X*(Y*X))=TrR (X*X*Y):=by rw [←mul_assoc,TrR_comm (X*Y),←mul_assoc]
abbrev tangle(A:Op n):Op n:= ReflW A⁻¹ -- check parsing
lemma intake_t (h:lit A): tangle A*tangle A = A⁻¹:=refl_sq (lit_inv h).1
lemma tangle_n(h:lit A): tangle A*A*tangle A=1:=by
 let T:=tangle A; have ht:tangle A*tangle A=A⁻¹:= intake_t h; have hw:A * (T*T)=1:=by rw [show T*T=A⁻¹ from ht, lit_mulin h]; -- simplify cancel
 apply ((refl_live (lit_inv h)).2).mul_left_injective; change tangle A*A*tangle A*tangle A = 1*tangle A; rw [mul_assoc (tangle A*A),mul_assoc, ht,lit_mulin h,mul_one,one_mul] -- `mul_right_injective` bypass
lemma route_log(h:lit A)(v:lit B): rueD A ≤ rueD B + TrR (B⁻¹ * (A-B)):=by
 let T:=tangle B; have ht:lit T:= refl_live (lit_inv v); let Y:=T*A*T; have hy:lit Y:=⟨conjugate_nonneg_of_nonneg h.1 ht.1,((ht.2).mul h.2).mul ht.2⟩
 have hg: rueD Y= rueD A-rueD B:=by
    have hi: T*T=B⁻¹:=intake_t v; have hx:Y.det=A.det/B.det:=by
       rw [div_eq_mul_inv]; unfold Y; rw [Matrix.det_mul,Matrix.det_mul,mul_comm (Matrix.det T) A.det,mul_assoc,←Matrix.det_mul,hi,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    unfold rueD; rw [hx,norm_div]; exact Real.log_div (norm_ne_zero_iff.mpr (def_beam h).ne') (norm_ne_zero_iff.mpr (def_beam v).ne')
 rw [mul_sub,lit_inmul v,TrR_sub,TrR_one]; apply sub_le_iff_le_add'.mp -- tune order
 rw [←hg]; exact (reduced hy).trans_eq (by unfold Y; rw [mul_assoc,TrR_interest,show T*T=B⁻¹ from intake_t v])
end YM.CF.Fock.Reduction
