import YM.CF.Pec.Shall
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{δ:ℝ}
lemma nectar (U:Cloud n)(x: Orig n)(p:PlaqAxes)(v: Orig n): whale U x p.val.1 p.val.2=(4:ℝ)⁻¹ • ∑ t:RegHour, heat v (collect group U) (Sum.inl (pore x p t,p)):=by rw [worth]; unfold RegHour; rw [Fintype.sum_prod_type]; simp [pore,Font.heat]; abel
private lemma commute_s {I J K R:Type}[Fintype I][Fintype J][Fintype K][AddCommMonoid R](f:I→ J→ K→R): (∑ i:I, ∑ j,∑ k,f i j k)=∑ k:K, ∑ i,∑ j,f i j k:=by rw [sum_comm (s:=(univ:Finset K))]; apply sum_congr rfl; intro; intro; rw [sum_comm]
lemma scalpV (t: Tonic n)(x:Site n)(V:Ok n→Ok n→ℂ): (∑ i:Ok n,∑ j:Ok n, if atV x t=(i,j) then V i j else 0)=V (atV x t).1 (atV x t).2:=by obtain ⟨i,j⟩:=atV x t; rw [sum_eq_single i]; simp; intro k _ h; simp [Ne.symm h]; simp
lemma roan_r(P:Case)(U: Cloud n)(x:Site n):datam (node x) (roan P x) U= (16:ℝ)⁻¹ • ∑ v:Scan n, beam P (whale U (poolY x v)) (whale U (poolY x v)):=by
 let F(i):=heat (node x) (collect group U) i
 let f (p q:PlaqAxes)(i j:Ok n):= inner ℝ (F i) (F j) • valueV P p q
 rw [show datam _ _ _= ∑ t:Tonic n,f t.1 t.2.1 (atV x t).1 (atV x t).2 from ?_]; swap
 · unfold datam roan; simp_rw [Finset.smul_sum]; rw [commute_s]; refine sum_congr rfl fun t _=>?_ ; simp_rw [smul_ite,smul_zero]; exact scalpV t x _ -- tune
 unfold beam Tonic; simp_rw [Finset.smul_sum]; rw [←commute_s (I:=PlaqAxes) (J:=PlaqAxes) (K:=Scan n) (f:=fun _ _ _=>_)] -- f placeholder
 rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [Fintype.sum_prod_type]; refine sum_congr rfl ?_; intro j _; rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro k _
 rw [Fintype.sum_prod_type]; let V:=poolY x k; change _=(16:ℝ)⁻¹ • inner ℝ (whale U V _ _) (whale U V j.val.1 j.val.2) • P i j; rw [nectar U V i (node x),nectar U V j (node x),real_inner_smul_right, real_inner_smul_left,sum_inner]; simp_rw [inner_sum]; simp only [mul_assoc, mul_inv_rev, Finset.mul_sum,Finset.sum_smul, Finset.smul_sum]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; unfold f F atV valueV; dsimp only; unfold V; rw [smul_smul,smul_smul]; congr 1; ring
lemma roan_o(P:Case)(U:Cloud n): diem (roan P) U=(16:ℝ)⁻¹ • (↑(priceC P*(∑ i:Orig n,∑ b:PlaqAxes, ‖whale U i b.val.1 b.val.2‖^2)):ℂ):=by
 rw [← hum_pay P U]; unfold diem; simp_rw [roan_r,← Finset.smul_sum]; simp_rw [map_smul]; rw [←Finset.smul_sum,smul_comm]; apply congrArg
 let G(s i):=beam P (skew s (whale U i)) (skew s (whale U i)); let X(k:Site n)(v:Scan n):= (part n) (k,v); have hp(s): ∑ i:Site n, ∑ v:Scan n,G s (s.act (poolY i v))=∑ i: Orig n,G s i:=by
    calc
     _ = ∑ i: Orig n,G s (s.act i):=by rw [← Equiv.sum_comp (part n), Fintype.sum_prod_type]; rfl
     _ = _:= Equiv.sum_comp (s.actEquiv (R:=Per (More n))).toEquiv (G s) -- tune
 simp_rw [cluster]; change (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, pays s (∑ i:Site n,∑ v:Scan n,G s (s.act (poolY i v)))=_
 rw [Finset.smul_sum]; simp_rw [hp,map_sum]; simp only [Finset.smul_sum,hum]; rw [sum_comm]
lemma price_one : priceC (fun x y=>if x=y then 1 else 0)=1:=by
 -- could calculate bound on sum hum P. use beam invariant under signed for identity. or crystal crest 0 1 stays one norm under perms. prove
 let P:Case := fun i j=> if i=j then 1 else 0; let X:= crest 0 1 (1:ℝ)
 have h0:(0:Axis) ≠1:=by decide
 have he (s:Signed): beam P (skew s X) (skew s X)=1:=by
    let F:=skew s X; let i:Axis:=s.perm.symm 0; let j:Axis:=s.perm.symm 1; have hz:i ≠ j:= s.perm.symm.injective.ne h0
    let a:PlaqAxes:= if h:i<j then ⟨(i,j),h⟩ else ⟨(j,i),by order⟩
    have he(v:Axis) : (dye s v)^2=1:=by cases h:s.flip v<;> simp [dye,h]
    have hm(q:PlaqAxes):∑ k:PlaqAxes,inner ℝ (F q.val.1 q.val.2) (F k.val.1 k.val.2) • P q k= (F q.val.1 q.val.2)^2 • (1:ℂ):=by unfold P; rw [sum_eq_single q]; simp; ring; intro i _ hi; simp [Ne.symm hi]; simp
    unfold beam; change ∑ q:PlaqAxes, (∑ k:PlaqAxes,inner ℝ (F q.val.1 q.val.2) (F k.val.1 k.val.2) • P q k)=1; simp_rw [hm]; rw [sum_eq_single a]
    · rw [show (F _ _)^2=(1:ℝ) from ?_,one_smul]; unfold F skew; rw [smul_eq_mul,mul_pow,mul_pow,he,he]; unfold a X i j; split <;> simp [crest,ask,h0,h0.symm]
    · intro u _ hk; have hh:F u.val.1 u.val.2=0:=by
         let x:=u.val.1; let y:=u.val.2; have ht:x<y:=u.property; change F x y=0; unfold F X skew crest; have hy(s':Axis)(v:Axis): s'=s.perm v → s.perm.symm s'=v:=fun l=>by rw [l,Equiv.symm_apply_apply]
         have hp: ¬((0:Axis)=s.perm x ∧ (1:Axis)=s.perm y):=by
            rintro ⟨p,h⟩; apply hk; have he:i=x:=hy _ _ p; have hh:j=y:=hy _ _ h; unfold a; rw [dif_pos (show i<j by rwa [he,hh])]; exact Subtype.ext (Prod.ext he.symm hh.symm)
         have hv : ¬((1:Axis)=s.perm x ∧ (0:Axis)=s.perm y):=by
            rintro ⟨p,h⟩; apply hk; have he:j=x:=hy _ _ p; have hh:i=y:=hy _ _ h; unfold a; rw [dif_neg (show ¬i<j by rw [he,hh]; order)]; exact Subtype.ext (Prod.ext he.symm hh.symm)
         simp only [Pec.ask,if_neg hp,if_neg hv,sub_self,zero_smul,smul_zero]
      rw [hh]; simp
    simp
 unfold priceC crystalC hum; change (((Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,pays s (beam P (skew s X) (skew s X))).re) = _; simp_rw [he]; have ht(i:Signed): pays i 1=1:=by cases h:detX i <;>simp [pays,h];
 simp_rw [ht]; simp only [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; rw [inv_mul_cancel₀ (by positivity),one_smul,Complex.one_re]
end YM.CF.Pec
