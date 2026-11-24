import YM.CF.Gas.Flute
import YM.CF.Ione.Rake
set_option autoImplicit false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Gas
open Function Filter Metric Finset NormedSpace Fock Petal Pastry Spire Scroll Scree Ione Branch Lattice Lat Tenant
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][LinearOrder n]
def brass(P C Y :Op n):ribbon n:= hang (Tour.Kcc Y (reserve P C)) (Tour.Kcg Y (driftB P C)) (Tour.Kgg Y (weldB P C))
variable {P Q C Y:Op n}(h:IsStarProjection P)(e:IsUnit (stage P C))(S:Op n)
include h e
lemma mirrors_K (p:C∈unitary _)(g:Cᵀ= -C): Tour.Kcc S (reserve (1-P) C)= -cc (Tour.Kgg S (weldB P C))∧ Tour.Kcg S (driftB (1-P) C)= -star (Tour.Kcg S (driftB P C)) ∧ Tour.Kgg S (weldB (1-P) C)= -cc (Tour.Kcc S (reserve P C)):=by
 have hx (A:Op n): cc Aᵀ= star A:= by rw [← ccT]; rfl
 have hh: IsUnit (stage (1-P) C):=by rw [stage,show 1-(1-P)=P by abel,add_comm]; exact e
 have hz := mir_V h.one_sub hh p g; rw [show 1-(1-P)=P by abel] at hz; have ht:=congrArg cc hz; rw [cc_neg,cc_cc] at ht -- tune implicit name
 unfold Tour.Kcc Tour.Kcg Tour.Kgg; rw [mir_A h e p,mir_V h e p g]; constructor
 · rw [cc_mul,cc_mul, hx, ccT,mul_neg,neg_mul]
 rw [mul_neg,neg_mul, show weldB (1-P) C= -(cc (reserve P C)) from (by rw [ht,neg_neg])] -- tune
 simp only [star_mul,hx,cc_mul,cc_cc,mul_neg,neg_mul]; have hk: star (cc S)= Sᵀ :=by rw [← cc_star,cc,star_star]
 rw [hk,show star Sᵀ=cc S from rfl]; simp only [mul_assoc,and_self]
omit h e
lemma false_u(U:UNI n)(D J K:Op n): paintR false false U (hang D J K)=hang (Tour.Kcc U.val D) (Tour.Kcg U.val J) (Tour.Kgg U.val K):=Uniform.run U D J K -- may order
-- nc-unit orbit of simultaneous P C Y
include e
lemma brass_X (U:UNI n): paintR false false U (brass P C S)=brass (twist U P) (congrC U C) (twist U S):=by
 unfold brass; rw [false_u,reserve_cov e,drift_cov e,weld_cov e]; unfold Tour.Kcc Tour.Kcg Tour.Kgg; rw [cc_twist, twist_formula,twist_formula]
 let V:=ccU U; have he: V.val=cc U.val:=rfl
 have hu (F:Op n)(V:UNI n): (V.val*F*star V.val)*V.val=V.val*F:=by rw [mul_assoc (V.val*F), V.property.1,mul_one]
 have hz (F:Op n)(V:UNI n): V.valᵀ*(V.val*F*star V.val)ᵀ=(V.val*F)ᵀ:=by rw [←Matrix.transpose_mul,hu]
 have hf(X F G:Op n)(U V:UNI n): U.val*(F*X*Gᵀ)*V.valᵀ=(U.val*F*star U.val)*(U.val*X*V.valᵀ)*(V.val*G*star V.val)ᵀ:=by
    rw [←mul_assoc _ (U.val*X),←mul_assoc _ U.val, hu,mul_assoc ((U.val*F)*X), hz,Matrix.transpose_mul]; simp only [mul_assoc]
 simp_rw [← he]; congr 1<;> exact hf .. -- tune congrArg₃
lemma windy_stage(z:Bool) : stage (windX z P) (windX z C)=windX z (stage P C):=by cases z <;> simp only [windX,Bool.false_eq_true,↓reduceIte,stage,body,cc_mul,cc_sub,cc_one,cc_add]
lemma live_w (z:Bool):IsUnit (windX z (stage P C)):=by cases z; exact e; exact ⟨Units.map ({toFun:=cc,map_one':=cc_one,map_mul':=cc_mul}:Op n→*Op n) e.unit, congrArg cc e.unit_spec⟩ -- tune
lemma windN (b:Bool) : windX b (reserve P C) =reserve (windX b P) (windX b C):=by
 let H:= stage P C; unfold reserve; rw [windy_stage e,win_m]
 suffices v:windX b H⁻¹=(windX b H)⁻¹ by rw [v] -- tune transparent
 simpa only [singT, Fock.one_des] using singsUnit b 1 H e -- may need one
end YM.CF.Gas
