import YM.SU5.Selected.Cor.Quiver
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
local notation "ⅈ"=> Complex.I
variable {m n x y V:Type*}[Fintype m][DecidableEq m][Fintype n][DecidableEq n][Fintype x][DecidableEq x][Fintype y][DecidableEq y][Fintype V][DecidableEq V]
-- warp support basis incidence, norm stable. Provide rectangular α with no clash.
lemma portion_le (F:WRect n m)(v:x→m)(h:Injective v): ‖F*mask v‖ ≤ ‖F‖:= (charge_mul le_rfl (mask_toll v h)).trans_eq (mul_one _)
lemma recoil_b (F:WRect n m)(a: x≃ n)(b:y≃ m): ‖F.submatrix a b‖ ≤ ‖F‖:= by
 rw [show F.submatrix a b=(mask a)ᴴ*F*mask b from ?_]; exact (portion_le _ _ b.injective).trans ((charge_mul ((Matrix.l2_opNorm_conjTranspose (mask a)).trans_le (mask_toll _ a.injective)) le_rfl).trans_eq (one_mul _))
 ext; rw [mask_mem,mask_star_mem]; rfl
lemma warp_bound (F: WRect n m)(x :Type*)[Fintype x][DecidableEq x]: ‖F ⊗ₖ (1:Op x)‖ ≤ ‖F‖:=by
 rw [show F⊗ₖ (1:Op x)=(Crest.Airy.tap (fun (_:x)=> F)).submatrix (Equiv.prodComm ..) (Equiv.prodComm ..) from ?_]; exact (recoil_b ..).trans (tap_norm (norm_nonneg _) (fun _=> le_rfl))
 ext ⟨i,j⟩ ⟨u,v⟩; by_cases p:j=v; subst v; simp [Crest.Airy.tap]; simp [p,Crest.Airy.tap] -- tune binder shadow l
lemma warp_sub (F H: WRect n m)(K:WRect x y): (F-H) ⊗ₖ K= F ⊗ₖ K - H⊗ₖ K:=by ext ⟨a,b⟩ ⟨c,d⟩; simp [sub_mul]
-- generic Frame quotient-on-All. (occup is residual op; Q = 1-P mom). We will use separately Q identity-cost $≤1$ vs projected pert kernel. 
structure Payroll (Q:Op n)(F Z:WRect n m)(X C η ξ:ℝ): Prop where
  tribute : ‖F‖≤ X
  cost: ‖Z‖≤ C
  gram: ‖Fᴴ*Z-1‖ ≤ η
  seat: ‖Q*Z‖≤ ξ
namespace Payroll
lemma mono (A:Op n)(X Z:WRect n m)(Y C η ξ:ℝ)(p:Payroll A X Z Y C η ξ){Y' C' η' ξ':ℝ}(a:Y ≤ Y')(b:C≤C')(c:η≤η')(d:ξ≤ξ'): Payroll A X Z Y' C' η' ξ':= ⟨p.tribute.trans a,p.cost.trans b, p.gram.trans c,p.seat.trans d⟩
-- compressed reincarnation with τ occupations convex combos. Norm products no sign demands besides positive.
lemma office (A:Op n)(X Z:WRect n m)(Y C η ξ:ℝ)(p:Payroll A X Z Y C η ξ)(F G:WRect m x)(a:Fᴴ*G=1){U V:ℝ}(e:‖F‖≤ U)(g:‖G‖≤ V): Payroll A (X*F) (Z*G) (Y*U) (C*V) (U*η*V) (ξ*V):=by
 refine ⟨charge_mul p.tribute e,charge_mul p.cost g,?_,?_⟩; · rw [show (X*F)ᴴ*(Z*G)-1=Fᴴ*(Xᴴ*Z-1)*G from ?_]; exact charge_mul (charge_mul ((Matrix.l2_opNorm_conjTranspose ..).trans_le e) p.gram) g; rw [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,a]; simp [Matrix.mul_assoc]
 rw [←Matrix.mul_assoc]; exact charge_mul p.seat g
lemma inspect (A:Op n)(X Z:WRect n m)(Y C η ξ:ℝ)(p:Payroll A X Z Y C η ξ)(f:x→m)(h:Injective f): Payroll A (X*mask f) (Z*mask f) Y C η ξ:=by
 simpa only [one_mul,mul_one] using (p.office A X Z Y C η ξ (mask f) (mask f) (mask_self f h) (mask_toll f h) (mask_toll f h))
-- `Finset` Cost no rank restrictions. Warp x→slot exactly
lemma twill (A:Op n)(X Z:WRect n m)(Y C η ξ:ℝ)(p:Payroll A X Z Y C η ξ)(x:Type*)[Fintype x][DecidableEq x]: Payroll (A ⊗ₖ (1:Op x)) (X⊗ₖ (1:Op x)) (Z⊗ₖ (1:Op x)) Y C η ξ := by
 refine ⟨(warp_bound ..).trans p.tribute,(warp_bound ..).trans p.cost, ?_,?_⟩; · rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,← Matrix.mul_kronecker_mul, mul_one, ← Matrix.one_kronecker_one, ← warp_sub]; exact (warp_bound ..).trans p.gram
 rw [← Matrix.mul_kronecker_mul, mul_one]; exact (warp_bound ..).trans p.seat
-- rotate & orth cross for projected data. Norm occupancy. Algebra grade. `α=1/S`, `β=S/2` no accidental norm.
def design (T:UNI n)(F:WRect n m)(x:ℝ):= (x:ℂ) • (F-ⅈ • (T.val*F))
lemma designing (T:UNI n)(A:Op n)(h:Commute A T.val)(X:WRect n m)(x:ℝ): A*design T X x = design T (A*X) x:= by unfold design; rw [Matrix.mul_smul,Matrix.mul_sub,Matrix.mul_smul,←Matrix.mul_assoc,h.eq]; rw [Matrix.mul_assoc]
lemma display (T:UNI n)(X:WRect n m)(x:ℝ)(h:0≤x): ‖design T X x‖≤ x*2*‖X‖:=by unfold design; rw [norm_smul,Complex.norm_of_nonneg h]; apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le ..) h); rw [norm_smul,Complex.norm_I,one_mul]; exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (paid_l T X)) h).trans_eq (by ring)
lemma designed (A:Op n)(X Z:WRect n m)(Y C η ξ:ℝ)(p:Payroll A X Z Y C η ξ)(T:UNI n)(e:Commute A T.val)(v:Xᴴ*(T.val*Z)=0)(w:(T.val*X)ᴴ*Z=0){x:ℝ}(u:0<x): Payroll A (design T X x⁻¹) (design T Z (x/2)) ((2*Y)/x) (C*x) η (ξ*x):=by
 let X₀:=design T X x⁻¹; let Y₀:= design T Z (x/2); let a:=(x:ℂ)⁻¹; let b:ℂ:= (↑(x/2:ℝ)); refine ⟨(display T X _ (by positivity)).trans ((mul_le_mul_of_nonneg_left p.tribute (by positivity)).trans_eq (by ring)),(display T Z _ (by positivity)).trans ((mul_le_mul_of_nonneg_left p.cost (by positivity)).trans_eq (by ring)),?_,?_⟩
 · change ‖X₀ᴴ*Y₀-1‖≤η; rw [show X₀ᴴ* Y₀=Xᴴ*Z from ?_]; exact p.gram
   let J:= Xᴴ*Z; have ht:(T.val*X)ᴴ*(T.val*Z)=J:= (by rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,←Matrix.mul_assoc T.valᴴ, show T.valᴴ*T.val=1 from T.property.1,Matrix.one_mul])
   unfold X₀ Y₀ design; rw [Matrix.conjTranspose_smul,Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_smul]; rw [v,w,ht]; simp only [smul_zero,sub_zero,zero_sub, sub_neg_eq_add]; change (star ((↑(x⁻¹)):ℂ)) • (b • (J+ star ⅈ • (ⅈ • J)))=J; rw [smul_smul (star ⅈ), Complex.star_def,Complex.conj_I,neg_mul,Complex.I_mul_I,neg_neg,one_smul, ← two_smul ℂ J,smul_smul,smul_smul];
   have he: (x:ℂ) ≠0:= (by exact_mod_cast u.ne'); rw [Complex.conj_ofReal, show ((↑(x⁻¹):ℂ)*b*2) = 1 by unfold b; push_cast; field_simp, one_smul]
 rw [designing T A e]; exact (display T (A*Z) _ (by positivity)).trans ((mul_le_mul_of_nonneg_left p.seat (by positivity)).trans_eq (by ring))

end Payroll
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Payroll
#print axioms office
#print axioms twill
#print axioms designed
