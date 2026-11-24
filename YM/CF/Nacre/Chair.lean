import YM.CF.Nacre.Pike
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
private lemma knot(k:Op SpinIdx)(e:∀ i,Commute k (gammaOp i)): k=k 0 0 • (1: Op SpinIdx):=by
 -- exploit diagonal γ and ig0*g1; then adjacency implies
 have he :Commute k grading:=by rw [grading_rule]; exact ((Commute.mul_right (e _) (e _)).mul_right (e _)).mul_right (e _)
 let T:=gammaOp 0*gammaOp 1; let v: SpinIdx→ℂ:= ![Complex.I,-Complex.I,Complex.I,-Complex.I] -- compute γ1γ2 = iσ3? upper -iσ1 times inverse lower (iσ2) gives iσ3
 let w: SpinIdx→ℂ:= ![1,1,-1,-1]
 have hp:T=Matrix.diagonal v :=by ext i j; fin_cases i<;>fin_cases j<;>norm_num [T,v,gammaOp,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Matrix.diagonal_apply] -- timeout
 have hx:grading=Matrix.diagonal w:=by ext i j; fin_cases i<;>fin_cases j<;>simp [grading,w,Matrix.diagonal_apply]
 have hv (i j:SpinIdx)(h:i≠j): v i ≠ v j ∨ w i≠w j:=by fin_cases i <;> fin_cases j <;> simp_all (config:={zeta:=false}) only [ne_eq,not_true, false_or,not_false_eq_true, Matrix.cons_val_one,Matrix.cons_val_zero,v,w, true_or, Decidable.not_not] <;> norm_num [v,w,Complex.ext_iff]
 have hf : k=Matrix.diagonal k.diag:=by
    ext i j; rw [Matrix.diagonal_apply]; split; next h=> simp [h]
    next h=>
       have hz(x:SpinIdx→ℂ)(e:Commute k (Matrix.diagonal x))(h:x i≠x j): k i j=0:=by
           by_contra p; have hu:=Matrix.ext_iff.mpr e.eq i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (x i)] at hu; exact h (mul_left_cancel₀ p hu.symm)
       apply (hv i j h).elim (hz v (hp ▸ ((e 0).mul_right (e 1) : Commute k T))) (hz w (hx ▸ he))
 have hD (i j:SpinIdx)(p:Axis)(v:gammaOp p i j≠0): k.diag i=k.diag j:=by
    have ha: Commute (Matrix.diagonal k.diag) (gammaOp p):=by rw [← hf]; exact e _
    have he:= Matrix.ext_iff.mpr ha.eq i j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm (gammaOp p _ _)] at he; exact mul_right_cancel₀ v he
 have hw(i:SpinIdx): k.diag 0=k.diag i:=by
    fin_cases i; rfl; exact (hD 0 2 3 (by simp [gammaOp])).trans (hD 2 1 1 (by simp [gammaOp])); exact hD 0 2 3 (by simp [gammaOp]); exact hD 0 3 1 (by simp [gammaOp])
 conv_lhs=> rw [hf]
 ext i j; by_cases h:i=j<;> simp only [Matrix.diagonal_apply,h,ite_true,ite_false,Matrix.smul_apply,Matrix.one_apply] <;> simp only [if_true,if_false,h,smul_zero,smul_eq_mul,mul_one]; exact (hw j).symm
 simp [h]
lemma kits(s:Signed)(U V:UNI SpinIdx)(h:JetS s false (detX s) U)(p:JetS s false (detX s) V):∃ z:ℂ, U.val=z • V.val ∧ z*star z=1:=by
 let A:=star V.val * U.val
 have ha: star A*A=1:=by unfold A; rw [star_mul,star_star, Matrix.mul_assoc, ← Matrix.mul_assoc V.val, V.property.2, Matrix.one_mul,U.property.1]
 have he(i): twist U (gammaOp i)=twist V (gammaOp i):=by obtain ⟨j,rfl⟩:=s.perm.surjective i; exact Eq.trans (h.cliff _) (p.cliff _).symm
 have hk:=knot A (fun i=>by
    have hl: U.val*gammaOp i=twist U (gammaOp i)*U.val:=by rw [twist_formula,Matrix.mul_assoc,U.property.1,Matrix.mul_one] -- tune
    have hh:star V.val*twist V (gammaOp i)=gammaOp i*star V.val:=by simp only [twist_formula,← Matrix.mul_assoc,V.property.1,Matrix.one_mul]
    unfold Commute SemiconjBy A; rw [Matrix.mul_assoc,hl, he, ← Matrix.mul_assoc, hh, Matrix.mul_assoc])
 let z:= A 0 0
 have hp:A=z • 1:=hk
 refine ⟨z,?_,?_⟩
 · rw [show U.val= V.val*A by unfold A; rw [← Matrix.mul_assoc,V.property.2,Matrix.one_mul],hp, Matrix.mul_smul,Matrix.mul_one]
 rw [hp,star_smul,star_one,Matrix.smul_mul,Matrix.mul_smul, smul_smul,Matrix.one_mul] at ha; rw [mul_comm]; exact (by simpa using Matrix.ext_iff.mpr ha 0 0)
end YM.CF.Nacre
