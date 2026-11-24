import Gingham.Ruff.Tassel

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n] [Fintype n]


/-! Covariance. In the general theta slot the spin travels by U and
    C'=1+F' with F' = -twist U F*. In the algebraic lemmas weight can
    travel by dagger; the W in use is self-adjoint. -/
lemma twistTr (U:UNI n) (X:Op n) : Matrix.trace (twist U X)=Matrix.trace X := by
  rw [twist_formula, Matrix.trace_mul_comm,←mul_assoc, U.property.1,one_mul]
lemma wind_𝒜 (U : UNI n) (S A W : Op n) :
    𝒜 (twist U S) (twist U A) (twist U W) = 𝒜 S A W := by
  rw [𝒜,←map_sub,←map_mul,twistTr]
  rfl
lemma wind_sheaf (U:UNI n) (S T W:Op n) :
    sheaf (twist U S) (twist U T) (twist U W)=twist U (sheaf S T W) := by
  simp only [sheaf, seam,𝒞,𝒞',ℱ,Kennel.capT,map_mul,map_sub,map_add,map_one]
lemma wind_𝒪 (U:UNI n) (S T W:Op n) :
    𝒪 (twist U S) (twist U T) (twist U W)=twist U (𝒪 S T W) := by
  rw [𝒪,𝒪,wind_sheaf,map_sub]
lemma wind_𝒵 (U : UNI n) (S T W:Op n) :
    𝒵 (twist U S) (twist U T) (twist U W)=twist (quantU U) (𝒵 S T W) := by
  rw [𝒵,←map_mul,twistTr,wind_sheaf,𝒵,map_sub,dg_cov,twist_scalar,map_one]


lemma wind_gable (U : UNI n) (A W : Op n) :
    gable (twist U A) (twist U W) = twist (quantU U) (gable A W) := by
  rw [gable,←map_mul,twistTr,gable,map_sub,dg_cov,twist_scalar,map_one]
lemma wind_facade (U : UNI n) (A W : Op n) (a : ℂ) (O : Op n) :
    facade (twist U A) (twist U W) a (twist U O)=twist (quantU U) (facade A W a O) := by
  rw [facade,wind_gable,facade,map_sub,map_add,dg_cov,twist_scalar,map_one]
lemma wind_𝒿 (U : UNI n) (A J : Op n) :
    𝒿 (twist U A) (twist U J)=twist (quantU U) (𝒿 A J) := by
  rw [𝒿,←map_mul,twistTr,𝒿,map_add, dg_cov,twist_scalar,
    map_mul (twist U) (A*J),map_sub,map_one,map_one]
lemma wind_portico (U : UNI n) (A : Op n) (a : ℂ) (O : Op n) :
    portico (twist U A) a (twist U O)=twist (quantU U) (portico A a O) := by
  rw [portico,wind_𝒿,portico,map_add,twist_scalar,map_one]

variable {S A : Op n}

lemma turn_ℱ (h : IsStarProjection S) (T : Op n) :
    ℱ (1-S) (-(star T)) = -star (ℱ S T) := by
  unfold ℱ Kennel.capT
  rw [sub_sub_cancel,star_mul,h.isSelfAdjoint,star_mul,h.one_sub.isSelfAdjoint,
    mul_neg,neg_mul,mul_assoc]


lemma turn_seam (h : IsStarProjection S) (W:Op n) :
    seam (1-S) (star W) = star (seam S W) := by
  simp only [seam,sub_sub_cancel,star_add,star_mul,h.isSelfAdjoint.star_eq,
    h.one_sub.isSelfAdjoint.star_eq,mul_assoc]
  rw [add_comm] 
lemma turn_sheaf (h : IsStarProjection S) (T W : Op n) :
    sheaf (1-S) (-(star T)) (star W) = star (sheaf S T W) := by
  rw [sheaf,sheaf,turn_seam h]
  unfold 𝒞 𝒞'
  rw [turn_ℱ h T,star_mul,star_mul,star_sub,star_add,star_one,
    sub_neg_eq_add,sub_eq_add_neg,mul_assoc]
lemma turn_𝒜 (h : IsStarProjection S) (g : IsStarProjection A) (W : Op n) :
    𝒜 (1-S) (1-A) (star W)= -star (𝒜 S A W) := by
  unfold 𝒜
  rw [sub_mul,sub_mul,sub_mul,sub_mul]
  simp only [Matrix.trace_sub,star_trace_mul h,star_trace_mul g,star_sub]
  abel
lemma turn_𝒪 (h : IsStarProjection S) (T W : Op n) :
    𝒪 (1-S) (-(star T)) (star W)= star (𝒪 S T W) := by
  rw [𝒪,turn_sheaf h,𝒪,star_sub]


lemma turn_𝒵 (h : IsStarProjection S) (U:UNI n) (T W:Op n) :
    theta U (𝒵 S T W)= -(𝒵 (twist U (1-S)) (twist U (-(star T))) (twist U (star W))) := by
  rw [𝒵,theta_sub,theta_smul,theta_one,theta_dg,sheaf_trace h,𝒵,
    ←map_mul,twistTr,wind_sheaf,turn_sheaf h,sub_mul,one_mul,Matrix.trace_sub,
    star_trace_mul h,star_trace,sub_smul]
  abel
lemma turn_gable (h : IsStarProjection A) (U:UNI n) (W:Op n) :
    theta U (gable A W)= -(gable (twist U (1-A)) (twist U (star W))) := by
  rw [gable,theta_sub,theta_smul,theta_one,theta_dg,gable,←map_mul,twistTr,
    sub_mul,one_mul,Matrix.trace_sub,star_trace_mul h,star_trace,sub_smul]
  abel

-- scalar slot gets a trace from flipping, can matter for truncated J's
def residuum (a : ℂ) (O : Op n) := -(star a + star (Matrix.trace O))
lemma turn_facade (h : IsStarProjection A) (U : UNI n) (W : Op n) (a : ℂ) (O : Op n) :
    theta U (facade A W a O)=
    -(facade (twist U (1-A)) (twist U (star W))
       (residuum a O) (twist U (star O))) := by
  rw [facade,theta_sub,theta_add,theta_smul,theta_one,theta_dg,turn_gable h,facade,
    residuum,neg_smul,add_smul]
  abel



lemma turn_portico (h : IsStarProjection A) (U : UNI n) (a : ℂ) (O : Op n) :
    theta U (portico A a O)=
    -(portico (twist U (1-A)) (residuum a O) (twist U (star O))) := by
  have he : Matrix.trace (A*O*(1-A)) = 0 := by
    rw [Matrix.trace_mul_comm,←mul_assoc,P'orth h,zero_mul,Matrix.trace_zero]
  rw [portico,theta_add,𝒿,theta_add,theta_dg,theta_smul,theta_smul,theta_one]
  rw [portico,wind_𝒿,𝒿,map_add,twist_scalar,map_one,dg_cov,he,star_zero,zero_smul,
    star_mul,h.one_sub.isSelfAdjoint,star_mul,h.isSelfAdjoint,
    ←mul_assoc (1-A) (star O) A,
    sub_sub_cancel]
  -- trace
  have hp : Matrix.trace ((1-A)*star O) = star (Matrix.trace O) - star (Matrix.trace (A*O)) := by
     rw [sub_mul,one_mul,Matrix.trace_sub,star_trace_mul h,star_trace]
  rw [hp]
  rw [residuum,neg_smul,add_smul,sub_smul]
  abel

end YM.CF.Gingham.Ruff

