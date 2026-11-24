import YM.CF.Thera.Pike
set_option autoImplicit false
noncomputable section
namespace YM.CF.Thera
open Function Filter NormedSpace Finset Fock Scroll Matrix Spire Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{B P K W Z C Y:Op n}[Nonempty n]
lemma sum_p(A:Op n)(h:‖A‖<1): Summable (fun k:ℕ=> bcoef k • A^(k+1)):=by
 apply Summable.of_norm; apply ((summable_geometric_of_lt_one (norm_nonneg _) h).mul_right ‖A‖).of_nonneg_of_le (fun i=>norm_nonneg _)
 intro i; rw [norm_smul]; apply le_trans (mul_le_mul (bc_norm i) (norm_pow_le ..) (norm_nonneg _) zero_le_one); rw [one_mul,pow_succ]
lemma debit(B C:Op n)(u:‖B*C‖<1)(w:‖C*B‖<1): invoice (B*C)=invoice (C*B):=by
 let Z:Op n →ₗ[ℝ]ℂ:=⟨⟨trace, Matrix.trace_add⟩,fun a B=> Matrix.trace_smul ..⟩; let X:= Z.toContinuousLinearMap
 have hp(i):trace ((B*C)^(i+1))=trace ((C*B)^(i+1)):=by
    have he(i:ℕ): C*(B*C)^i=(C*B)^i*C:=((show SemiconjBy C (B*C) (C*B) from (mul_assoc ..).symm).pow_right i).eq; rw [pow_succ', mul_assoc B C,he, trace_mul_comm B, show (C*B) ^ (i+1)=(C*B)^i*(C*B) from pow_succ ..,←mul_assoc] -- tune
 rw [tally_log u,tally_log w,pencil,pencil]; change X _= X _; rw [X.map_tsum (sum_p _ u),X.map_tsum (sum_p _ w)]; exact tsum_congr fun i=>by rw [map_smul,map_smul]; exact congrArg _ (hp i)
lemma wax(A:Op n)(u:‖A‖<1): star (invoice A)=invoice (star A):=by
 have ht:‖star A‖<1:= (norm_star ..).trans_lt u
 let F: Op n→L[ℝ] Op n:= (starL' ℝ).toContinuousLinearMap; have hx: pencil (star A) = star (pencil A):=by unfold pencil; change _=F _; rw [F.map_tsum (sum_p A u)]; apply tsum_congr; intro i; change _=star _; rw [star_smul,show star (bcoef i)=bcoef i from star_trivial _,star_pow]
 rw [tally_log u,tally_log ht,hx, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
lemma star_iv (h:Clad P B W Z K)(t:Clad (1-P) (1-B) Z W Y)(hp:TagG P C)(u:‖bentT K B W C‖<1)(w:‖bentT Y (1-B) Z (-star C)‖<1): invoice (bentT Y (1-B) Z (-star C))= star (invoice (bentT K B W C)):=by
 apply Function.Injective.eq_iff star_injective|>.mp; rw [star_star,wax _ w]
 let V:=K*(B*W)*(1-P); have he:V*C=bentT K B W C:=by unfold V; rw [mul_assoc _ (1-P) C, hp.pen]
 have ht: C*V=star (bentT Y (1-B) Z (-star C)):=by rw [xover h t hp]; unfold V; simp only [mul_assoc]
 have hx:‖C*V‖<1:=by rw [ht,norm_star]; exact w
 rw [←he,←ht,debit _ _ hx (he.symm ▸ u)]
lemma awards(A:Op n)(g:‖A‖ < 1)(b:Bool): invoice (windX b A)=cSignX b (invoice A):=by
 have h:‖windX b A‖=‖A‖:=by cases b; rfl; exact norm_cc _
 rw [tally_log (h.trans_lt g), tally_log g]; have hx:sings b (1:UNI n) (pencil A)=pencil (windX b A):=by
   unfold pencil; rw [sings_sumts _ _ _ (sum_p A g)]; apply tsum_congr; intro i; rw [singT,one_des,win_r]; congr 1
   have hi(k:ℕ): windX b (A^k)=(windX b A)^k:=by induction k with | zero=>simp [win_i]| succ i ih=> rw [pow_succ,pow_succ,win_m,ih]
   exact hi _
 rw [←hx,singT, one_des,win_trace]
end YM.CF.Thera
