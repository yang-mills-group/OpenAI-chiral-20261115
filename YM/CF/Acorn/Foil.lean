import YM.CF.Acorn.Lola
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Matrix NormedSpace Finset Fock Jet Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
variable {n Y D E:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D][TopologicalSpace E]
variable {X:Master D Y} {Z:Master E Y}{f g:E→ D}{O:n→Y}{S R:Seal Y}{a K c r h:ℝ}{A:D→ℂ}{L:D→Op (I n)}
lemma Drop.seam (i:I n)(p: Plum X O L a K)(u: Cop X Z f): Drop Z O a i (fun x=> unitL (mix (L (f x))) (pen i)) (K+K):=by
  obtain ⟨F,C,h,H,v,U⟩:= p.hit
  let y:=rflip i; let M:= K+K; let V(k:I n)(S:Seal Y)(x:D):=F S x k y-F S x y k
  let t(v:I n × Seal Y) : Seal Y × I n × (E→ℂ) × ℝ:= (v.2,v.1,V v.1 v.2 ∘ f,C v.2 v.1 y+C v.2 y v.1)
  refine ⟨I n × Seal Y,inferInstance,t,fun z=>?_, ?_,?_⟩
  · rcases z with ⟨z,m⟩; dsimp only
    let a:=h m z y; let b:=h m y z
    have ht':Pro X m (V z m) (C m z y+C m y z):= a.1.sum b.1.minusP
    refine ⟨ht'.cop u,fun v=>?_⟩; change C m z y+C m y z≠0 at v; by_cases he:C m z y=0; exact b.2 (by simpa [he] using v); exact And.symm (a.2 he)
  · rw [Fintype.sum_prod_type]; unfold t; simp only [mul_add, Finset.sum_add_distrib]; exact add_le_add (H.cols y) (H.rows y)
  intro x; dsimp only; rw [show unitL _ _=_ from unitt ..]; change boxL (L (f x)) _=_; rw [cashout,Fintype.sum_prod_type (f:=fun j:I n × Seal Y=> (t j).2.2.1 x • pen (t j).2.1),U]
  simp only [phaseX,Matrix.sum_apply,←sum_sub_distrib,sum_smul]; rfl
lemma Plum.nop(p:Plum X O L a K):Plum X O (-L) a K:=by
 obtain ⟨F,C,h,H,K,v⟩:=p.hit; refine ⟨fun i x=>-F i x,C,fun S i j=>⟨((h S i j).1).minusP,(h S i j).2⟩,H,K,fun x=>?_⟩; rw [Pi.neg_apply,v]; exact Eq.symm (sum_neg_distrib ..)
lemma Cash.silent (p: Cash Z S a (A ∘ f) K) : Carries Z O S a h (fun x=> (A ∘ f) x • 1) K:=by
 obtain ⟨M,C,h,H,t⟩:=p
 refine ⟨Seal Y,inferInstance,(fun i=>(i,[],M i,C i)),fun i=>⟨(h i).1,fun v=>⟨(h i).2 v,⟨0,rfl⟩,fun _ k=>by cases k⟩⟩,?_,fun i=>?_⟩
 · simpa only [bill,List.length_nil,pow_zero,mul_one] using (show ∑ i:Seal Y,cost a S i*_ ≤ K from H)
 dsimp only; rw [t,Finset.sum_smul]; simp [valK]
lemma eqIn {P C D A:Op n}(p:IsStarProjection P)(t:Cᵀ= -C)(e:IsUnit (stage P C))(g:IsStarProjection D)(u:Aᵀ= -A)(hx:IsUnit (stage D A)) : acts (exp (-excite D A) * exp (coupl A-coupl C)* exp (excite P C)) (filled P C)=filled D A:=by
 let X:=excite P C; let Y:=excite D A
 rw [act_mul,← exp_excite p t e];
 have he:Commute (coupl C) (coupl A):=by
   change _*_= _*_
   set S:=coupl C
   unfold coupl squareP; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
   congr 1; simp_rw [sum_mul,mul_sum,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [show S*(put i*put j)=_ from ((mark_y i).mul_right (mark_y j)).eq]
 have hQ : exp (coupl A-coupl C)* exp (coupl C)= exp (coupl A):=by
   letI : NormedAlgebra ℚ (FC n) := NormedAlgebra.restrictScalars ℚ ℂ (FC n)
   rw [← exp_add_of_commute (he.symm.sub_left (Commute.refl ..)), sub_add_cancel]
 rw [act_mul,← stored,←act_mul (exp (coupl A-coupl C)),hQ,stored,exp_excite g u hx, ← act_mul, show exp (-excite D A)*exp (excite D A)=1 from mul_eq_one_comm.mp (wind_inv _),act_one]
lemma phaseEQ {W N:FC n}{Q V:Wave n} {v b:ℂ}(S:ℂ)(h:S=b-v)(p:acts W (Complex.exp b • Q)=Complex.exp v • V)(w:N=Complex.exp S • W) : acts N Q = V:=by
 rw [w, h,act_smul]; rw [map_smul] at p
 rw [Complex.exp_sub,div_eq_inv_mul,mul_smul,p,smul_smul,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul]
end YM.CF.Acorn
