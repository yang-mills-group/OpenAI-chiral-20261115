import YM.CF.Nacre.Stem
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev CoreX:=group.Color
abbrev HtX(m:ℕ):= TaxX m group
variable {n:Side}{m:ℕ}
def lowerP (P:Toy m n)(g:E)(u v:Single n)(r:Trip m n):HtX m:= let V:=matter g; let a:=u.1; let b:=v.1
 ∑ i:Slot,∑ j:Slot, ((star V.val u.2 i)*V.val j v.2) • (P (a,i) (b,j) r).compContinuousLinearMap (fun _=> (group.adjoint g).toContinuousLinearMap)
lemma keynote(P:Toy m n)(g:E)(u v:HopK n)(r:Trip m n)(x:Fin m→ CoreX): halo (lowerP P g) u v r x= twist ((matter g)⁻¹) (halo P u v r (fun i=> group.adjoint g (x i))):=by
 let V:= matter g
 ext i j; unfold halo lowerP; rw [Matrix.of_apply]; dsimp only; simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]; rw [twist_formula]; change _=(star V.val*_*star (star V.val)) i j; rw [star_star,Matrix.mul_apply]; simp_rw [Matrix.mul_apply,sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro k _; apply sum_congr rfl; intro l _; change _*(P _ _ _ _)= _*(P _ _ _ _)*_; unfold V; ring_nf; rfl -- tune
private lemma adj_p (c:CoreX):Continuous fun g:E=> group.adjoint g c:=by
 simp only [Gauge.adjoint,LinearMap.coe_mk,AddHom.coe_mk, Gauge.conjugate]; apply group.projectColor.continuous_of_finiteDimensional.comp (f:=fun g:E=> _ * _ * _); -- tune
 fun_prop
lemma punctual (f:E→HtX m)(h:∀ x: Fin m→ CoreX,Continuous fun g=> f g x) : Continuous f:=by
 classical
 let I:=Fin m→Fin (Module.finrank ℝ CoreX); let b:= Module.finBasis ℝ CoreX
 let L:=LinearMap.pi (R:=ℝ) fun i:I=> (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m=>CoreX) ℂ (fun j=> b (i j))).toLinearMap
 have he: L.ker=⊥:=LinearMap.ker_eq_bot'.mpr (fun X hx=>by
    ext p; conv_lhs=> rhs; rw [show p=(fun i=> ∑ j,(b.repr (p i)) j • b j) from funext (fun i=>(b.sum_repr _).symm)]
    rw [ContinuousMultilinearMap.map_sum]; refine Finset.sum_eq_zero fun i _=>?_; rw [X.map_smul_univ (fun j:Fin m=> (b.repr (p j)) (i j))]; rw [show X (fun j=> b (i j))=0 from congr_fun hx i,smul_zero])
 obtain ⟨g,e⟩:= LinearMap.exists_leftInverse_of_injective L he
 have hp:f=g ∘ (L ∘ f):=by funext x; exact (DFunLike.congr_fun e (f x)).symm
 rw [hp]; exact g.continuous_of_finiteDimensional.comp (continuous_pi fun i=> h _)
set_option maxRecDepth 8000 in
lemma lacy(P:Toy m n)(u v: Single n)(r:Trip m n): Continuous fun g:E=> lowerP P g u v r:=by
 refine punctual _ ?_; intro x
 let Z(g:E):=fun i=> group.adjoint g (x i); have hx : Continuous Z:= continuous_pi fun i=> adj_p _
 unfold lowerP; dsimp only; simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Matrix.star_apply]; apply continuous_finsetSum; intro i _; apply continuous_finsetSum; intro j _
 exact (((matter_cont.matrix_elem i u.2).star.mul (matter_cont.matrix_elem j v.2)).mul ((P _ _ _).contDiff (n:=ω) |>.continuous.comp hx))
lemma silk(P:Toy m n)(u v:Single n)(g:E)(r:Trip m n):‖lowerP P g u v r‖≤∑ i:Slot,∑ j:Slot, ‖P (u.1,i) (v.1,j) r‖:=by
 have ht :‖(group.adjoint g).toContinuousLinearMap‖ ≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by rw [one_mul]; exact (group.norm_adjoint g x).le
 let V:= matter g; have he(i j):‖V.val i j‖≤1:= (norm_entry ..).trans (le_of_eq (by have ht:=CStarRing.norm_star_mul_self (x:=V.val); rw [V.property.1,norm_one] at ht; nlinarith [norm_nonneg (V.val)]))
 refine (norm_sum_le ..).trans (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_))
 rw [norm_smul]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_); swap
 · rw [norm_mul,Matrix.star_apply,norm_star]; exact mul_le_one₀ (he _ _) (norm_nonneg _) (he _ _)
 refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ?_); exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>ht)
def lantern (P: Toy m n):Toy m n:=fun i j r=> ∫ g:E, lowerP P g i j r ∂group.probHaar
lemma lifeP(P:Toy m n)(u v:HopK n)(i j:Slot)(r:Trip m n)(x:Fin m→ CoreX):
 halo (lantern P) u v r x i j=∫ g:E,(twist ((matter g)⁻¹) (halo P u v r (fun i=> group.adjoint g (x i)))) i j ∂group.probHaar:=by
 simp_rw [←keynote]; let L:=ContinuousMultilinearMap.apply ℝ (fun _:Fin m=>CoreX) ℂ x
 exact (L.integral_comp_comm ((lacy P (u,i) (v,j) r).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).symm
lemma flare (P:Toy m n)(u v:HopK n)(r:Trip m n)(x:Fin m→ CoreX):
 halo (lantern P) u v r x =∫ g:E,(halo (lowerP P g) u v r x) ∂group.probHaar:=by
 let F(g:E):=halo (lowerP P g) u v r x
 have hp:Continuous F:=by
    refine continuous_matrix fun i j=>?_ ; let L:=ContinuousMultilinearMap.apply ℝ (fun _:Fin m=>CoreX) ℂ x; exact L.continuous.comp (lacy P (u,i) (v,j) r)
 ext i j; rw [lifeP]; simp_rw [← keynote]; let L:= LinearMap.toContinuousLinearMap (show Op Slot→ₗ[ℝ]ℂ from ⟨⟨fun x=> x i j,fun a b=>rfl⟩,fun a b=>rfl⟩); exact L.integral_comp_comm (μ:=group.probHaar) (hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
lemma lantern_f(P: Toy m n): handy (lantern P):=by
 intro u v x C g; let V:=matter g; let Y(k:E)(A):=halo (lowerP P k) u v x A; let L:= (twist V).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 let ν:=group.probHaar
 have h(k:E): Y k (fun i=> group.adjoint g (C i))= L (Y (k*g) C):=by
    unfold Y; rw [keynote,keynote]; change twist _ _= twist V _; rw [← twin]; simp_rw [map_mul,_root_.mul_inv_rev, group.adjoint_mul]; rw [←mul_assoc,show V*(matter g)⁻¹*(matter k)⁻¹= (matter k)⁻¹ by unfold V; rw [mul_inv_cancel,one_mul]] -- tune
 have hp : Continuous (fun k:E=>Y k C):=continuous_matrix fun i j=> (ContinuousMultilinearMap.apply ℝ _ ℂ C).continuous.comp (lacy P (u,i) (v,j) x)
 rw [flare,flare]; change (∫ k,Y k _ ∂ν)= L (∫ k,Y k C ∂ν); simp_rw [h]; unfold ν; rw [integral_mul_right_eq_self (μ:=group.probHaar) (fun x=> L (Y x C))]; exact L.integral_comp_comm (hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
lemma polish_h(P:Toy m n)(h:handy P): handy (polish P):=by
 intro u v r C g; let V:=matter g; let t:= (humY P u v); have he(A): halo (polish P) u v r A=t • halo P (bro u u) (bro u v) (pinch (natural (-u.1)) r) A:=by ext; rfl
 rw [he, he,h]; rw [twist_formula,twist_formula]; simp only [Matrix.mul_smul,Matrix.smul_mul]
def sugarK :ℝ:= (Fintype.card Slot:ℝ)^2
lemma makes(P:Toy m n)(a C:ℝ)(h:∀ i:Single n,balance a P i≤C)(x:Single n): balance a (lantern P) x ≤ C*sugarK:=by
 rcases x with ⟨x,i⟩
 let μ:=group.probHaar
 have hp(y j r): ‖lantern P (x,i) (y,j) r‖ ≤∑ i:Slot,∑ j:Slot,‖P (x,i) (y,j) r‖:=by apply (norm_integral_le_of_norm_le_const (μ:=group.probHaar) (ae_of_all group.probHaar fun g=> silk P (x,i) (y,j) g r)).trans_eq; simp
 unfold balance Single; rw [Fintype.sum_prod_type]; let K(y: HopK n)(r:Trip m n):=nick a (notx m (x,i) (y,i) r)
 have ht(z l:Slot)(y: HopK n)(r:Trip m n):nick a (notx m (x,z) (y,l) r)= K y r:=rfl
 simp_rw [ht]
 calc
    _ ≤ ∑ y: HopK n,∑ _ : Slot,∑ r:Trip m n, K y r* (∑ i:Slot,∑ j:Slot,‖P (x,i) (y,j) r‖):= by apply sum_le_sum; intro y _; apply sum_le_sum; intro j _; apply sum_le_sum; intro r _; exact mul_le_mul_of_nonneg_left (hp _ _ _) (nick_pos a (notx_zero ..)|>.le)
    _ = ∑ _ : Slot,∑ k:Slot,balance a P (x,k) :=by
       rw [sum_comm]; unfold balance Single; refine sum_congr rfl fun i _ => ?_; simp_rw [Fintype.sum_prod_type (α₁:=Site n × SpinIdx),ht,mul_sum]; conv_rhs=> rw [sum_comm]
       refine sum_congr rfl fun y _=>?_ ; rw [sum_comm]; refine sum_congr rfl fun j _=>?_ ; rw [sum_comm]
    _ ≤ _ :=by apply (sum_le_sum (g:=fun _=>∑ _ : Slot,C) fun _ _=> sum_le_sum fun i _=> h _).trans_eq; simp [sugarK]; ring
end YM.CF.Nacre
