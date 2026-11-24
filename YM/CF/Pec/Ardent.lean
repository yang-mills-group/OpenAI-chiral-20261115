import YM.CF.Pec.Shore
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c:ℝ}{P:Bed}
lemma spray(P:Bed)(U:Cloud n):letter (rushP P) U=(16:ℝ)⁻¹ • (Bid.gaugeFiscal P U U:ℂ):=by
 rw [oaksQ]; let f(x y: Ps (More n)):= oaks P x y * inner ℝ (heat (0:Orig n) (collect group U) (.inl x)) (heat (0:Orig n) (collect group U) (.inl y)); let A(x:Orig n):=(16:ℝ)⁻¹ • ∑ p:PlaqAxes,∑ v:Ps (More n), (f (x,p) v:ℂ)
 have hx(i:Site n)(k: Scan n): datam (node i) (bedV P i k) U=A (poolY i k):=by
    unfold datam; unfold Wind; simp_rw [Fintype.sum_sum_type]; simp only [bedV,smul_zero,sum_const_zero,add_zero]
    unfold A; simp only [Finset.smul_sum]; unfold Ps Face; rw [Fintype.sum_prod_type]; rw [sum_eq_single (poolY i k)]; rotate_right; simp; rotate_right; intro y _ h; simp [h]
    refine sum_congr rfl fun j _=>?_; apply sum_congr rfl; intro v _; simp only [if_true, f]; push_cast; simp only [Complex.real_smul]; rcases v with ⟨v,r⟩; simp only [Font.heat]; ring -- tune
 have he(i:Site n): datam (node i) (rushP P i) U= ∑ k,datam (node i) (bedV P i k) U:=by
    unfold rushP datam; simp only [Finset.sum_apply,Finset.smul_sum]; rw [sum_comm (s:=(univ:Finset (Scan n)))]; apply sum_congr rfl; intro; intro; rw [sum_comm]
 change (∑ k:Site n,datam _ _ _) = (16:ℝ)⁻¹ • (↑(∑ i, ∑ j,f i j):ℂ); simp_rw [he,hx]; simp_rw [Complex.ofReal_sum]; unfold Ps Face; rw [Fintype.sum_prod_type (α₁:=Four _), Finset.smul_sum];
 change _=∑ i:Orig n,A i; rw [←Equiv.sum_comp (part n) A,Fintype.sum_prod_type]; rfl
lemma fiscal_p(s:Bid.Sworn P (More n) group)(U:Cloud n): diem (rushP P) U= (16:ℝ)⁻¹ • (Bid.gaugeFiscal P U U:ℂ):=by
 have he(i:Signed): pays i (letter (rushP P) (litX i U))= (16:ℝ)⁻¹ • (Bid.gaugeFiscal P U U:ℂ):=by rw [spray,map_smul, show Bid.gaugeFiscal _ (litX i U) (litX i U)= _ from s i U U,complX]; cases h:detX i<;> simp [cSignX]
 change (Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed, pays s (letter (rushP P) (litX s U))= _; simp_rw [he]; rw [Finset.sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma oak_safe (h:P.metric.strip a b)(p:0≤a)(t:PlaqAxes)(x:Orig n)(v:PlaqAxes): (∑ y: Orig n,Faro a x y *‖oaks P (x,t) (y,v)‖) ≤ b:= tinct x p (h (plaquette t) (plaquette v))
def hailP (a b:ℝ):= nick a 4*taxH a*b
lemma bed_safe(h:P.metric.strip a b)(v:0<a)(p:b≤b)(he:0≤c)(e:c≤a/2)(i:Site n)(x:Scan n):cents (node i) (bedV P i x) c≤ Fintype.card PlaqAxes * (Fintype.card PlaqAxes * hailP a b) :=by
 let X:= node i; let T:= poolY i x; let F(y z):= nick c (contour X y z)* ‖bedV P i x y z‖
 change ∑ u:Wind _, ∑ v: Wind _,F u v ≤ (_:ℝ); unfold Wind; simp_rw [Fintype.sum_sum_type]; simp only [F,bedV,norm_zero,mul_zero,sum_const_zero,add_zero]; unfold Face; rw [Fintype.sum_prod_type]; rw [sum_eq_single T]; rotate_right; simp; rotate_right; intro b _ h; simp [← show T= _ from (show T=poolY i x from rfl),h]
 apply (sum_le_sum (g:=fun _=>↑(Fintype.card PlaqAxes)*hailP a b) ?_).trans_eq (by simp); intro a' _; rw [Fintype.sum_prod_type, Finset.sum_comm]; refine (sum_le_sum (g:=fun _=>hailP a b) ?_).trans_eq (by simp)
 intro m _; let A:= nick a 4*taxH a; have hp:0 ≤ A:=mul_nonneg ((nick_pos _ (by norm_num : (0:ℝ)≤4)).le) (Iteration.momentPrice_pos _ (half_pos v)|>.le)
 apply le_trans _ (mul_le_mul_of_nonneg_left (oak_safe h v.le a' T m) hp); rw [Finset.mul_sum]; refine sum_le_sum fun j _=>?_; simp only [show T=poolY i x from rfl,ite_true,norm_smul,Complex.norm_real]; rw [← mul_assoc A]; let D:= contour X (Sum.inl (T,a')) (Sum.inl (j,m)); let u:ℝ:= separation T j
 have hx:D≤ 4+u:=by
    have h0: (separation X T:ℝ)≤2:=by exact_mod_cast dealU i x
    have hw: (separation X j:ℝ)≤ (separation X T:ℕ)+(separation T j:ℝ):=by exact_mod_cast separation_triangle X T j
    unfold D contour dial u; dsimp only; push_cast; linarith
 change nick c D * (‖(16:ℝ)⁻¹‖* _) ≤ (A*Faro a T j)*‖oaks P (T,a') (j,m)‖
 apply mul_le_mul _ (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) (by positivity) (mul_nonneg hp (Real.exp_pos _|>.le)); refine ((nick_inc he (ct_pos ..) hx).trans (nick_add (show (0:ℝ)≤4 by norm_num) (show 0≤u from Nat.cast_nonneg _))).trans ?_; change _≤ A*Faro a T j; rw [show A*Faro a T j=nick a 4*(taxH a*Real.exp (a*u)) by unfold A Faro; rw [mul_assoc]]; apply mul_le_mul (nick_rate (by linarith) (by norm_num)) (dentH v e (show 0≤u from Nat.cast_nonneg _)) ((nick_pos _ (show 0≤u from Nat.cast_nonneg _)).le) ((nick_pos _ (by norm_num)).le)
end YM.CF.Pec
