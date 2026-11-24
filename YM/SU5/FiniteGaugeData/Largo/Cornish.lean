import YM.SU5.FiniteGaugeData.Largo.Broad
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
variable {N X: Side} {σ C:ℝ}
section rank
variable {Y I J K:Type*}[Fintype Y][Fintype I][Fintype J][DecidableEq Y][DecidableEq I][DecidableEq J]
open LinearMap Module
lemma dim_b (F G:Ruler Y I)(L:Finset Y)(k:ℕ)(u:k+2*L.card≤ Fintype.card I): ∃ M:Ruler I (Fin k), Mᴴ*M=1 ∧ cutM L*F*M=0 ∧ cutM L*G*M=0:=by
 let a:= grip (fun i:L=>i.val) (fun _=>1); have he:a*aᴴ=cutM L:=by
    ext i j; rw [Matrix.mul_apply]; unfold a grip cutM; by_cases h:i=j <;> try (subst j)
    · by_cases v:i∈L; swap; · simp only [Matrix.of_apply,Matrix.diagonal_apply_eq,v,↓reduceIte]; refine sum_eq_zero fun l _=>?_ ; simp only [show i≠l.val from (fun h=>v (h ▸ l.property)),↓reduceIte,zero_mul]
      let l:L:=⟨i,v⟩; rw [sum_eq_single l, Matrix.diagonal_apply_eq];
      · simp [l,Matrix.conjTranspose_apply,v]
      · intro w _ w'; have he: i≠w.val:=fun h=>w' (Subtype.ext h.symm); simp [he]
      simp
    simp only [Matrix.diagonal_apply_ne _ h]; refine sum_eq_zero fun l _=>?_ ; by_cases t:i=l.val; · simp only [Matrix.conjTranspose_apply,Matrix.of_apply,t]; simp [show j≠l.val from fun v=>h (t.trans v.symm)]
    simp [t]
 let H:Ket I→ₗ[ℂ] Ket L × Ket L := (ract (aᴴ*F)).toLinearMap.prod (ract (aᴴ*G)).toLinearMap; -- coe syntax
 let S:=LinearMap.ker H; let n:=finrank ℂ S; have hu:= H.finrank_range_add_finrank_ker; have ht:finrank ℂ (LinearMap.range H) ≤ 2*L.card:= by
    refine (Submodule.finrank_le ..).trans_eq ?_; simp [add_comm,two_mul] -- syntax .. unknown
 have hx:k≤ n:=by rw [show finrank ℂ (Ket I)=Fintype.card I from finrank_euclideanSpace] at hu; unfold n S; omega
 let Y': Fin k→ S:= fun i=> stdOrthonormalBasis ℂ S (Fin.castLE hx i); let f: Ruler I (Fin k):= Matrix.of fun i j=> (Y' j).val.ofLp i; have hp(i:Fin k): ract f (basisKet i)=(Y' i).val:=by apply PiLp.ext; intro j; rw [R_basis]; rfl
 have hw (A:Ruler Y I)(h:∀ i:Fin k,ract (aᴴ*A) (Y' i).val=0): cutM L*A*f=0:=by rw [←he]; apply Matrix.ext; intro i j; rw [←R_basis i j (a*aᴴ*A*f), Matrix.mul_assoc a aᴴ A, R_mul,R_mul,hp,h,map_zero]; rfl
 refine ⟨f,?_,hw F (fun i=>?_ ),hw G (fun i=>?_ )⟩
 · ext i j; rw [←R_basis i j (fᴴ*f),R_mul,←basis_inner, Matrix.one_apply];
   -- inner: basis i, ract fᴴ (ract f ...). shift
   rw [← show _ = inner ℂ (basisKet i) (ract fᴴ (ract f (basisKet j))) from (Eq.trans (congrArg (fun F:Ruler I (Fin k)=>inner ℂ (ract F (basisKet i)) (ract f (basisKet j))) (Matrix.conjTranspose_conjTranspose f).symm) (R_adj fᴴ _ _)), hp,hp]; change inner ℂ (Y' i) (Y' j)=_; unfold Y'; rw [orthonormal_iff_ite.mp (stdOrthonormalBasis ..).orthonormal]; simp
 · have v:= congrArg Prod.fst ((Y' i).property : H _=0); exact v
 have v:= congrArg Prod.snd ((Y' i).property : H _=0); exact v
lemma cutShrunk (L S:Finset Y)(M:Ruler Y I)(h:cutM S*M=M)(p:cutM (S\ L)*M=0): cutM L*M=M:=by ext i j; rw [compass]; by_cases t:i∈L; rw [if_pos t]; rw [if_neg t]; have he:= congr_fun (congr_fun h i) j; rw [compass] at he; have hg:= congr_fun (congr_fun p i) j; rw [compass] at hg; by_cases b:i∈ S; rw [if_pos (by simp [b,t])] at hg; exact hg.symm; exact (if_neg b).symm.trans he -- types unknown
end rank
end YM.CF.Window.Largo
