import YM.CF.Pec.Ardent
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c:ℝ}
lemma bookZ {ι:Type}[Fintype ι](x:Orig n)(F:ι→Dues n)(h:∀ i,cents x (F i) a≤ b): cents x (∑ i,F i) a ≤ (Fintype.card ι)*b:=by
 refine le_trans ?_ (show (↑(Finset.univ (α:=ι)).card:ℝ)*b=Fintype.card ι*b from by simp).le
 suffices h:∀ s: Finset ι,cents x (∑ i∈s,F i) a≤ s.card*b from h univ
 classical
 intro s; induction s using Finset.induction_on with
 | empty=>simp [cents]
 | @insert i s g k=> rw [Finset.sum_insert g, Finset.card_insert_of_notMem g,Nat.cast_add,Nat.cast_one]; exact (coverG ..).trans ((add_le_add (h i) k).trans_eq (by ring))
def bed_c(a b:ℝ):ℝ:=16*(Fintype.card PlaqAxes * (↑(Fintype.card PlaqAxes) * hailP a b))
lemma strut {P:Bed}(h:P.metric.strip a b)(p:0<a)(he:0≤c)(t:c≤a/2)(i:Site n) : cents (node i) (rushP P i) c ≤ bed_c a b:= (bookZ (node i) _ (bed_safe h p le_rfl he t i)).trans_eq (by rw [←cardw,cardP]; rfl)
lemma value_p(k: Tonic n)(p:Case): ‖valueV p k.1 k.2.1‖≤ ‖p k.1 k.2.1‖:=by unfold valueV; rw [norm_smul]; apply mul_le_of_le_one_left (norm_nonneg _); norm_num
lemma journey(k:Tonic n)(x: Site n): contour (node x) (atV x k).1 (atV x k).2≤ 8:=by
 let V:=k.2.2.1; let p:=poolY x V
 have hx (a:PlaqAxes)(q:RegHour): (separation (node x) (pore p a q):ℝ) ≤4:=by
    have he:= (separation_triangle (node x) p (pore p a q)).trans (Nat.add_le_add (dealU x V) (poreC p a q)); exact_mod_cast he
 change _+_≤ _; have ht:=add_le_add (hx k.1 k.2.2.2.1) (hx k.2.1 k.2.2.2.2); exact ht.trans_eq (by norm_num)
private def p₀(n:Side)(P:Case)(x: Site n)(v:Tonic n): Dues n:=fun i j=> if atV x v=(i,j) then valueV P v.1 v.2.1 else 0
def unitK(a:ℝ):= (Fintype.card PlaqAxes:ℝ)*(Fintype.card PlaqAxes * ((16:ℝ)*Fintype.card (RegHour×RegHour)))*nick a 8
lemma vP(x:Site n)(h:0≤a)(p:Case)(k: Tonic n):cents (node x) (p₀ n p x k) a ≤ nick a 8 * ‖p k.1 k.2.1‖:=by
 unfold cents p₀; simp_rw [apply_ite norm,norm_zero,mul_ite,mul_zero]; let A:=contour (node x) (atV x k).1 (atV x k).2; have he(R:Ok n × Ok n)(f:Ok n→Ok n→ℝ): (∑ i:Ok n,∑ j:Ok n, if R=(i,j) then f i j else 0)=f R.1 R.2:=by obtain ⟨i,j⟩:= R; rw [sum_eq_single i]; simp; intro k _ h; simp [Ne.symm h]; simp
 rw [he]; exact mul_le_mul (nick_inc h (ct_pos ..) (journey k x)) (value_p k p) (norm_nonneg _) (nick_pos _ (by norm_num)|>.le)
lemma uv (x:Site n)(P:Case)(p:0≤c)(v:c≤a)(h:∀ i j,‖P i j‖ ≤ b):cents (node x) (roan P x) c≤unitK a*b:=by
 have hx: roan P x=∑ k,p₀ n P x k:=by funext i j; simp_rw [Finset.sum_apply]; rfl
 rw [hx]; refine (bookZ _ _ (fun t=>le_trans (vP x p P t) (mul_le_mul (nick_rate v (by norm_num)) (h ..) (norm_nonneg _) (nick_pos a (by norm_num)|>.le)))).trans_eq ?_; unfold Tonic; have h:=cardP n; unfold cardw at h; simp only [Fintype.card_prod (α:=PlaqAxes),Fintype.card_prod (α:= Scan n),Nat.cast_mul,h]; unfold unitK; ring -- tune
private def MCL : Case →L[ℝ] ℝ:= (show Case→ₗ[ℝ]ℝ from {
 toFun:=priceC
 map_add':=fun i j=>by unfold priceC crystalC hum beam; simp only [Pi.add_apply,smul_add,sum_add_distrib,map_add,Complex.add_re]
 map_smul':=fun i j=>by unfold priceC crystalC hum beam; simp only [Pi.smul_apply]; simp_rw [smul_comm _ i,← Finset.smul_sum, map_smul]; rw [←Finset.smul_sum,smul_comm]; simp only [Complex.smul_re,RingHom.id_apply] }).toContinuousLinearMap
def lime:= ‖MCL‖
lemma price_safe(P:Case)(s:0≤b)(p:∀ i j,‖P i j‖≤ b): |priceC P| ≤ lime*b := (MCL.le_opNorm P).trans (mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg s).mpr fun i=> (pi_norm_le_iff_of_nonneg s).mpr fun j=> p i j) (norm_nonneg _))
end YM.CF.Pec
