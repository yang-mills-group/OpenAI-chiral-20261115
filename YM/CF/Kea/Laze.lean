import YM.CF.Kea.Pale
import YM.CF.Cascade.Seashore
import YM.CF.Mir.Spin
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Cascade Dial
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{d:Candle}
lemma landP(N:Side): tickA N=Dofu N fun _=> Aop:=by unfold tickA; rw [plane_diag]; change love N (spin _ _ _) = _; rw [turnU, raising,Adef.symm] -- tune
lemma det_d(U:UNI (Single N))(k:Op (Single N)): Matrix.det (twist U k)=Matrix.det k:=by rw [twist_formula,Matrix.det_mul,Matrix.det_mul,mul_right_comm, ← Matrix.det_mul,U.property.2, Matrix.det_one,one_mul]
lemma tr_d(U:UNI (Single N))(k:Op (Single N)): Matrix.trace (twist U k)=Matrix.trace k:=by rw [twist_formula,Matrix.trace_mul_comm, ←mul_assoc,U.property.1,one_mul]
lemma det_a(X:Stag N→ Op SpinIdx): Matrix.det (arch X)=∏ i:Stag N, Matrix.det (X i):= (Matrix.det_submatrix_equiv_self ..).trans (Mir.jump_det _)
lemma tr_a(X:Stag N→ Op SpinIdx): Matrix.trace (arch X)=∑ i:Stag N, Matrix.trace (X i):=by unfold Matrix.trace; rw [show (arch X).diag=(fun x:Bri N=> X x.1 x.2 x.2)∘ budE N from (by funext i; simp only [Matrix.diag,jump_apply,arch_at, and_self,ite_true]; rfl)]; refine (Equiv.sum_comp (budE N) (fun x:Bri N=>X x.1 x.2 x.2)).trans ?_; rw [Fintype.sum_prod_type]; rfl
lemma cut_t(N:Side):IsStarProjection (tickA N):=plus_P _
lemma meanV(S:Slide N d)(j:ℕ)(M:Jill.Male):Matrix.trace (tickA N)=Matrix.trace (Dofu N (field S j M)):=by
 rw [landP]; change Matrix.trace (twist _ (arch _))=Matrix.trace (twist _ (arch _)); rw [tr_d,tr_d,tr_a,tr_a]; unfold field; simp_rw [dateA,bar_n] -- check
lemma footQ (S:Slide N d)(g:Even N.val)(j:ℕ)(M:Jill.Male)(i:Stag N):Aop * field S j M i * Aop = ((disk j M (angle S i):ℝ):ℂ) • Aop:=by
 let x:= angle S i; have hp:tmap x∈ realCube zone:=base_subset_realCube zone_pos (b_base (up_p S g i)); unfold field; rw [(bar_side _ _ hp).1, Matrix.smul_mul,mul_add,mul_one,add_mul,AOne,zenA,mul_assoc _ (1-Aop),sub_mul,AOne,one_mul,sub_self,mul_zero,add_zero,express _ _ _ hp M.property]; rfl
lemma seatQ(c:ℂ): Matrix.det (c • Aop+(1-Aop))=c^2:=by
 rw [show Aop=cutM plusHalf from Adef.trans raising.symm]; let f(i:SpinIdx):ℂ:= if i∈plusHalf then c else 1
 rw [show c • cutM plusHalf+(1-cutM plusHalf)= Matrix.diagonal f from ?_,Matrix.det_diagonal]
 · norm_num [f,plusHalf,SpinIdx,Fin.prod_univ_succ,sq] -- tune
 ext i j; by_cases h:i=j <;> by_cases e:i∈plusHalf <;> simp [h,e,cutM,f,Matrix.diagonal_apply,Matrix.one_apply] <;> grind
lemma apex(S:Slide N d)(g:Even N.val)(j:ℕ)(M:Jill.Male)(v:Wave (Single N))(hv:Sea (Dofu N (field S j M)) v):
 ‖inner ℂ (mateK N) v‖= ∏ i:Stag N,disk j M (angle S i):=by
 let A:=tickA N; let U:=fun _:Stag N=> Aop; let Q:=field S j M; let P:=Dofu N Q; let F:= A*P; let m:= mateK N; have hp:IsStarProjection P:=idol S j M g
 let Y:=U*Q*U+(1-U); have ht:F*star F+(1-A)= Dofu N Y:=by
   unfold F; rw [star_mul,hp.isSelfAdjoint.star_eq,show star A=A from (cut_t N).2, ← mul_assoc, mul_assoc A P P, show P*P=P from hp.1]; unfold Y; rw [map_add,map_mul,map_mul,map_sub,map_one, ← show A= _ from landP N]
 have he:= Thera.prismK hp (cut_t N) (meanV S j M) 1 v hv m (tickB N); dsimp only at he; simp only [mul_one, skyGlow, quant_one,act_one] at he -- tune names
 have hx:‖inner ℂ m v‖^2 = (∏ i:Stag N,disk j M (angle S i))^2:=by
    have hi(w:Stag N): Matrix.det (Y w)=((disk j M (angle S w):ℝ):ℂ)^2:=by
       change Matrix.det (Aop*field S j M w*Aop+(1-Aop))= _; rw [footQ S g,seatQ]
    rw [ht] at he -- tune
    change (↑(‖inner ℂ m v‖^2):ℂ)=Matrix.det (twist _ (arch Y)) at he; rw [det_d,det_a] at he; simp_rw [hi, Finset.prod_pow] at he; exact_mod_cast he
 apply pow_left_inj₀ (norm_nonneg _) (prod_nonneg (fun i _=> norm_nonneg _)) (by decide : (2:ℕ)≠0) |>.mp hx -- tune
end YM.CF.Kea
