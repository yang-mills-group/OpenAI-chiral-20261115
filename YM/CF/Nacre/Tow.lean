import YM.CF.Nacre.Rail
import YM.CF.Aroma.Boots
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
def crete (r:Bool):Op (Single n)→L[ℝ]Op (Single n):= if r then -((starL ℝ : Op (Single n)≃L[ℝ] Op (Single n)).toContinuousLinearMap) else ContinuousLinearMap.id _ _
lemma crete_c(x:Op (Single n))(r:Bool):crete r x=Thera.jazz r x:=by cases r <;>rfl
def ZoneH (a:Shape):Op (Single n) →L[ℝ] Op (Single n):=
 (crete (detX a.s)).comp (twist (prepU a (spinX a.s) inert n)).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
lemma zone_c (a:Shape)(X:Op (Single n)): ZoneH a X= Thera.jazz (detX a.s) (ape n a X):=crete_c ..
lemma zno (a b: Shape)(X: Op (Single n)): ZoneH b (ZoneH a X)=ZoneH (joinX a b) X:=by
 simp only [zone_c,Thera.jazz]; rw [show (joinX a b).s = a.s*b.s from rfl,det_p];
 cases p:detX a.s<;> cases q:detX b.s<;> simp only [Bool.xor_false,Bool.false_xor,Bool.xor_self, Bool.false_eq_true,ite_true,ite_false] <;> rw [← apes] <;> try rfl
 all_goals unfold ape; simp only [map_neg,map_star,star_neg,star_star,neg_neg]
lemma z_spin (a:Shape)(x: Op (Single n))(U:UNI SpinIdx)(h:JetS a.s false (detX a.s) U):ZoneH a x= Thera.jazz (detX a.s) (twist (prepU a U inert n) x):=by -- implicit arg det
 obtain ⟨z,hx,hz⟩:= kits _ U _ h (bud_s _); rw [zone_c]; unfold ape; congr 1; symm; rw [twist_formula,Ygs _ _ _ hx,twist_formula, Matrix.smul_mul,star_smul,Matrix.mul_smul,Matrix.smul_mul,smul_smul,mul_comm (star z),hz,one_smul]
lemma lag_t(x:Cover)(z:Cover): (lagX x).flee z= x+z:=by
 have he:= Shape.mote (lagX x) z; change affine _ _ _ = _ at he -- tune
 apply nsmul_right_injective (M:=Cover) (show (2:ℕ)≠0 by decide); change 2 • _= (2:ℕ) • (x+z);
 have hu : (lagX x).motion (2 • z+1)= 2 • z+1+2 • x:=by unfold lagX Shape.motion; simp
 linear_combination (norm:=abel) hu-(Shape.mote (lagX x) z) -- tune
lemma lag_p(t:Cover)(x:Site n):(lagX t).payA x=Rush.wind x t:=by unfold Rush.wind Shape.payA Shape.rent; rw [lag_t,add_comm]
lemma lag_i(t:Cover)(x:Site n): Shape.mills (lagX t) n x=x+wrap n t:=by unfold Shape.mills; rw [lag_t]; unfold Lattice.affine lagX; simp
lemma lagQ(t:Cover)(X:Op (Single n)):ZoneH (lagX t) X=twist (prepU (lagX t) 1 inert n) X:=by
 have he: detX (lagX t).s=false:=det_i; rw [z_spin _ X 1 (he.symm ▸ calmSX),he]; rfl
lemma limo(t:Cover)(x y:Site n)(i j:SpinIdx)(a b: Slot)(X:Op (Single n)): ZoneH (lagX t) X ((x,i),a) ((y,j),b)= Rush.wind x t* Rush.wind y t * X ((x+wrap n t,i),a) ((y+wrap n t,j),b):=by
 rw [lagQ]; obtain ⟨S,rfl⟩:= (love n).surjective X
 let A:=mealU (lagX t) 1 inert n; have ht: A=Aroma.clime t:=by
    apply Subtype.ext; change jump (Tofu (lagX t) n) (fun i=> (milU (lagX t) 1 inert i).val)=jump (Equiv.addRight (wrap n t)) (fun i=> Rush.wind i t • (1:Op (SpinIdx × Slot))); congr 1; exact Equiv.ext fun x=> lag_i t x
    ext1 x; change (lagX t).payA x • ((1:Op SpinIdx) ⊗ₖ (1:Op Slot))=Rush.wind _ _ • _; rw [←lag_p,Matrix.one_kronecker_one]
 have hx:sings false (prepU (lagX t) 1 inert n) (love n S)=love n (sings false A S):=wingX ..
 change sings false (prepU (lagX t) 1 inert n) (love n S) _ _= _; rw [hx,ht]; exact Aroma.creep t x y (i,a) (j,b) S
def clove (a:Shape):Shape:=⟨a.s⁻¹,- (a.s⁻¹).act a.t⟩
lemma chillI (a:Shape): joinX a (clove a)=incX 1∧ joinX (clove a) a=incX 1:=by constructor <;> simp [joinX,incX,clove]
lemma blank(U: Bkg (More n)):Yg (incX 1) U= U:=by change Lattice.pull 1 (wrap _ (2 • (0:Cover))) U=U; simp
lemma bareI (X:Op (Single n)): ZoneH (incX 1) X=X:=by
 ext ⟨⟨x,i⟩,a⟩ ⟨⟨y,j⟩,b⟩; rw [show incX 1=lagX 0 from rfl, limo]; simp only [map_zero,add_zero]; have he (x:Site n): Rush.wind x (0:Cover) =1:=by
    have hx:= infT x (0:Cover); simp only [map_zero,add_zero] at hx; have ht:=add_eq_left.mp hx; have hh: periods n (natural x)=0:= (nsmul_right_injective (M:=Cover) n.property.ne' (by simpa only [smul_zero])); simp only [Rush.wind,add_zero,hh,Rush.fee]; simp
 rw [he,he,one_mul,one_mul]
end YM.CF.Nacre
