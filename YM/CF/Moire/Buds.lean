import YM.CF.Nacre.Helios
import YM.CF.Tulip.Stem
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
abbrev Cin:= Fin (Module.finrank ℝ CoreX)
def sol:= Module.finBasis ℝ CoreX
def citeX :Op SU.F →ₗ[ℝ] CoreX:=group.projectColor ∘ₗ ((1/2:ℝ) • (LinearMap.id - (starL ℝ : Op SU.F ≃L[ℝ] Op SU.F).toLinearEquiv.toLinearMap))
lemma cit_h(A: Op SU.F):citeX A=group.projectColor ((1/2:ℝ) • (A-star A)):=rfl
lemma cit_m (U:E)(A:Op SU.F): citeX (twist (firstF U) A)=group.adjoint U (citeX A):=by
 rw [cit_h,cit_h, ←group.project_conjugate,map_star (twist (firstF U)) A|>.symm,← map_sub, ← map_smul]; -- tune
 congr 1
def slate(h:Bool)(A:Op SU.F): CoreX:= if h then citeX ((-Complex.I) • A) else citeX A
lemma slate_m(U:E)(A:Op SU.F)(h:Bool): slate h (twist (firstF U) A)=group.adjoint U (slate h A):=by
 cases h
 · exact cit_m ..
 change citeX ((-Complex.I) • _) =group.adjoint U _
 rw [show (-Complex.I) • (twist (firstF U)) A = twist (firstF U) ((-Complex.I) • A) by rw [twist_formula,twist_formula, Matrix.mul_smul,Matrix.smul_mul],cit_m]; rfl
def spurY(t:Cin): Op SU.F →L[ℂ] ℂ:=
 let f:Op SU.F→ₗ[ℝ]ℝ:= (sol.coord t).comp citeX
 let D: Op SU.F→ₗ[ℝ]ℂ:= Complex.ofRealAm.toLinearMap.comp f
 let V: Op SU.F→ₗ[ℝ] Op SU.F:=(-Complex.I) • LinearMap.id
 let L: Op SU.F→ₗ[ℝ]ℂ:=D+Complex.I • (D.comp V)
 (show Op SU.F→ₗ[ℂ]ℂ from {
   toFun:=L,map_add':=L.map_add
   map_smul':=fun z A=> by
     change L (z • A)= z • L A
     have he:L (Complex.I • A)=Complex.I • L A:=by
       have ht: V (Complex.I • A)= A:=by change (-Complex.I) • (Complex.I • A)=A; simp [smul_smul]
       have hu: Complex.I • A = - V A:=by simp [V];
       change D _+Complex.I • D (V _)=Complex.I • (D A+Complex.I • D (V A)); rw [ht,hu,map_neg]; rw [smul_add,smul_smul, Complex.I_mul_I,neg_smul,one_smul,add_comm]
     have hx:L (z • A)=L ((z.re:ℝ) • A + z.im • (Complex.I • A)):=by apply congrArg L; simp_rw [← Complex.coe_smul,smul_smul,←add_smul]; rw [Complex.re_add_im] -- tune
     rw [hx,map_add,map_smul,map_smul,he]; simp_rw [← Complex.coe_smul, smul_smul, ←add_smul,Complex.re_add_im] }).toContinuousLinearMap

def idol(h:Bool):ℂ:= if h then Complex.I else 1
lemma spur_b (i:Cin)(A:Op SU.F): spurY i A= ∑ h:Bool, idol h*↑(sol.repr (slate h A) i):=by rw [Fintype.sum_bool]; simp only [idol,Bool.false_eq_true,ite_false,ite_true,one_mul, add_comm (_*_)]; rfl

-- sector multilinear rotor arm
lemma mold_split(P:Toy m n)(x y:HopK n)(i:Trip m n)(a: Fin m→ Op SU.F):
  (∑ j:Fin m→Cin,(∏ k, spurY (j k) (a k)) • halo P x y i (fun k=>sol (j k))) =
  ∑ h:Fin m→Bool,(∏ j,idol (h j)) • halo P x y i (fun j=>slate (h j) (a j)):=by
 simp_rw [spur_b,Finset.prod_univ_sum,Finset.sum_smul]; rw [sum_comm]; apply sum_congr rfl; intro h hh; ext u v
 let K (j:Fin m):=slate (h j) (a j)
 rw [Matrix.sum_apply]; change _= (_:ℂ) • P _ _ i K
 conv_rhs=>rw [show K=(fun k=> ∑ j:Cin, (sol.repr (K k)) j • sol j) from funext fun i=> (sol.sum_repr _).symm]
 rw [ContinuousMultilinearMap.map_sum, Finset.smul_sum]; apply sum_congr rfl; intro j hj; rw [ContinuousMultilinearMap.map_smul_univ _ (fun i:Fin m=> sol.repr (K i) (j i)), Finset.prod_mul_distrib, Complex.real_smul,Complex.ofReal_prod,smul_eq_mul,Matrix.smul_apply,smul_eq_mul,mul_assoc]; rfl -- tune

def flaw(P:Toy m n)(x y:HopK n)(i:Trip m n)(a: Fin m→ Op SU.F): Op Slot:= ∑ j:Fin m→ Cin,(∏ k, spurY (j k) (a k)) • halo P x y i (fun k=>sol (j k))
lemma flaw_g(P:Toy m n)(p:handy P)(x y:HopK n)(i:Trip m n)(U:E)(a): flaw P x y i (fun j=> twist (firstF U) (a j))= twist (matter U) (flaw P x y i a):=by
 simp only [flaw,mold_split,map_sum,slate_m,p x y]
 simp only [twist_formula,Matrix.mul_smul,Matrix.smul_mul]
lemma flaw_v(P:Toy m n)(x y:HopK n)(i:Trip m n)(A: Fin m→ Op SU.F)(e:∀ k,star (A k) = -(A k)) : flaw P x y i A= halo P x y i (fun k=>group.projectColor (A k)):=by
 have hv(k:Fin m):citeX (A k)= group.projectColor (A k):=by rw [cit_h,e,sub_neg_eq_add,← two_smul ℝ,smul_smul]; norm_num
 have ht (k:Fin m):citeX ((-Complex.I) • (A k))=0:=by simp only [cit_h,star_smul, star_neg,e]; rw [show star Complex.I = - Complex.I by simp, neg_neg, smul_neg, neg_smul,sub_self, smul_zero]; exact group.projectColor.map_zero
 rw [flaw,mold_split, sum_eq_single_of_mem (fun _=>false) (mem_univ _)]; swap
 · intro h _ he; obtain ⟨j,p⟩:= Function.ne_iff.mp he; have hp:h j=true:= by cases hw:h j<;>simp_all;
   ext u v; rw [Matrix.smul_apply]; change _ • (P _ _ i _)=_; rw [(P _ _ i).map_coord_zero j (show slate (h j) (A j) =0 by rw [hp]; exact ht j)]; simp
 simp [slate,hv,idol]
end YM.CF.Moire
