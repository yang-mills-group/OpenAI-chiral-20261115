import YM.CF.Thera.Jolt
import YM.CF.Matter.Anomaly
import Mathlib.Tactic.Module

/-!
# Color input to the g/f/x class calculation

Use the **actual** Color, `SU.group`, and its fundamental and matter
representations and their normalizations (primary project). U1 speaks of an
intertwiner on Color, with complex-linear extension. We will classify
invariant *and flavor* slots on these types, extending maps Color→ₗ[ℝ] Op Sheet
to work throughout with traceless complex matrices. Only differentiate for
the **same** SU action. No second gauge or reference representation and in
particular no assumption that Flavor acts on the interacting state without R4.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open Gauge SU Function Set
open Complex (I)
open scoped Matrix Kronecker Topology BigOperators Matrix.Norms.Frobenius
-- warning: scoped complex etc

abbrev Col := SU.group.Color
abbrev Fund := Op F
abbrev Sl (n : Type*) [Fintype n] := (Matrix.traceLinearMap n ℂ ℂ).ker -- maybe adjust

def basic (u : SU.E) := SU.fund u
def conjA {n : Type*} [Fintype n] [DecidableEq n] (A U : Op n) := A*U*star A
variable {n : Type*} [Fintype n] [DecidableEq n]
lemma conj_add (g A B : Op n) : conjA g (A+B) = conjA g A + conjA g B := by simp [conjA,mul_add,add_mul]
lemma conj_sub (g A B : Op n) : conjA g (A-B) = conjA g A - conjA g B := by simp [conjA,mul_sub,sub_mul]
lemma conj_smul (g A : Op n) (c : ℂ) : conjA g (c • A) = c • conjA g A := by simp [conjA]
lemma conj_star (g A : Op n) : star (conjA g A) = conjA g (star A) := by simp [conjA,mul_assoc]
lemma conj_one (u : E) : conjA (basic u) 1 = 1 := by unfold basic conjA; rw [mul_one]; exact (fund_U u).2
lemma conj_trace (u : E) (A : Fund) : (conjA (basic u) A).trace=A.trace := by
  unfold basic conjA; rw [Matrix.trace_mul_cycle,show star _ * _ = (1:Fund) from (fund_U u).1,one_mul]

-- complexification of real `SU.group.Color` (erase trace on $5$)
def plain : Fund →ₗ[ℂ] Fund where
  toFun X := X - (X.trace / 5) • 1
  map_add' X Y := by simp [add_smul, add_div]; abel
  map_smul' c X := by simp [smul_sub, smul_smul,mul_div_assoc]
lemma plain_self {X : Fund} (h : X.trace = 0) : plain X = X := by simp [plain,h]
lemma plain_zero (X : Fund) : (plain X).trace = 0 := by
  simp [plain,F,Matrix.trace_one]
lemma plain_conj (u : E) (A : Fund) : plain (conjA (basic u) A) = conjA (basic u) (plain A) := by
  simp [plain,conj_trace,conj_sub,conj_smul,conj_one]


-- Transport notation to `Fin 5` rather than `Fin (Gauge.group.n+1)`.
abbrev embedC : Col →ₗ[ℝ] Fund := group.colorMat
abbrev projectC : Fund →ₗ[ℝ] Col := group.projectColor
def Lie : Submodule ℝ Fund := SU.group.lie
lemma belongs (X:Fund) : X∈Lie ↔ star X = -X ∧ X.trace=0 := Thera.league
lemma embedC_mem (c : Col) : embedC c ∈ Lie := group.colorMat_mem _
lemma embedC_skew (c : Col) : star (embedC c) = -embedC c := group.colorMat_skew _
lemma embedC_project_self {X : Fund} (h : X∈Lie) : embedC (projectC X) = X := group.colorMat_project_self h
lemma embedC_injective : Injective embedC := group.colorMat_injective
@[simp] lemma project_back (c : Col) : projectC (embedC c)=c := embedC_injective (embedC_project_self (embedC_mem _))
lemma carries_su (g : E) {X : Fund} (p : X ∈ Lie) : conjA (basic g) X ∈ Lie := group.conjugate_mem g p

lemma trace_clear (c : Col) : (embedC c).trace=0 := ((belongs _).mp (embedC_mem c)).2
lemma moved (u : E) (x : Col) : embedC (group.adjoint u x)=conjA (basic u) (embedC x) :=
  group.mat_adjoint ..

-- Useful exact splitting, even without trace hypothesis (on all End(fund)). q second sign matters.
def axis1 (A : Fund) := (1/2:ℂ) • (A-star A)
def axis2 (A : Fund) := (-I/2) • (A+star A)
lemma axis1_mem {X : Fund} (h : X.trace=0) : axis1 X ∈ Lie := by
  rw [belongs]; constructor
  · simp [axis1,star_sub, ← smul_neg]
  simp [axis1,h,Matrix.star_eq_conjTranspose]
lemma axis2_mem {X : Fund} (h : X.trace=0) : axis2 X ∈ Lie := by
  rw [belongs]; constructor
  · simp [axis2,add_comm _ (star X)]; module
  simp [axis2,h,Matrix.star_eq_conjTranspose]
lemma two_axes (X : Fund) : axis1 X + I • axis2 X = X := by 
  unfold axis1 axis2; rw [smul_smul, show I * (-I/2) = (1/2 : ℂ) by rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]]; module
lemma twist_1 (X : Fund) : axis1 (I • X) = -axis2 X := by simp only [axis1,axis2,star_smul]; rw [Complex.star_def,Complex.conj_I]; module
lemma twist_2 (X : Fund) : axis2 (I • X) = axis1 X := by
  simp only [axis1,axis2,star_smul]; rw [Complex.star_def,Complex.conj_I]
  -- normalize with complex identities also
  match_scalars <;> ring_nf <;> norm_num

lemma axis1_add (X Y) : axis1 (X+Y) = axis1 X + axis1 Y := by unfold axis1; rw [star_add]; module
lemma axis2_add (X Y) : axis2 (X+Y) = axis2 X + axis2 Y := by unfold axis2; rw [star_add]; module
lemma axis1_real (c : ℝ) (X) : axis1 ((c:ℂ) • X) = (c:ℂ) • axis1 X := by
  unfold axis1; rw [star_smul,Complex.star_def,Complex.conj_ofReal]; module
lemma axis2_real (c : ℝ) (X) : axis2 ((c:ℂ) • X) = (c:ℂ) • axis2 X := by
  unfold axis2; rw [star_smul,Complex.star_def,Complex.conj_ofReal]; module
lemma axis1_stays (u : E) (x : Fund) : axis1 (conjA (basic u) x)=conjA (basic u) (axis1 x) := by
  simp only [axis1,conj_smul,conj_sub,conj_star]
lemma axis2_stays (u : E) (x : Fund) : axis2 (conjA (basic u) x)=conjA (basic u) (axis2 x) := by
  simp only [axis2,conj_smul,conj_add,conj_star]
lemma axis1_self (x : Col) : axis1 (embedC x)=embedC x := by
  unfold axis1; rw [embedC_skew]; module
lemma axis2_self (x : Col) : axis2 (embedC x)=0 := by
  unfold axis2; rw [embedC_skew]; simp

section
variable {U : Type*} [AddCommGroup U] [Module ℂ U] [Module ℝ U] [IsScalarTower ℝ ℂ U]

def spread (f : Col →ₗ[ℝ] U) (X : Fund) := f (projectC (axis1 X)) + I • f (projectC (axis2 X))
lemma spread_real (f : Col →ₗ[ℝ] U) (X : Fund) (c : ℝ) : spread f ((c:ℂ) • X) = (c:ℂ) • spread f X := by
  have e (x:Fund) : (c:ℂ) • x = c • x := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c x).symm
  have u (x:U) : (c:ℂ) • x = c • x := (RCLike.real_smul_eq_coe_smul (K:=ℂ) c x).symm
  simp only [spread,axis1_real,axis2_real]; simp only [e,map_smul,← u,smul_add,smul_comm I (c:ℂ)]
omit [IsScalarTower ℝ ℂ U] in
lemma spread_add (f : Col →ₗ[ℝ] U) (X Y : Fund) : spread f (X+Y)=spread f X+spread f Y := by
  simp only [spread,axis1_add,axis2_add,map_add,smul_add]; abel
omit [IsScalarTower ℝ ℂ U] in
lemma spread_i (f : Col →ₗ[ℝ] U) (X : Fund) : spread f (I • X)=I • spread f X := by
  simp only [spread,twist_1,twist_2,map_neg]; simp only [smul_add,smul_smul,Complex.I_mul_I]; simp [add_comm]

def extend (f : Col →ₗ[ℝ] U) : Fund →ₗ[ℂ] U where
  toFun X := spread f (plain X)
  map_add' x y := by rw [map_add, spread_add]
  map_smul' c x := by
    rw [RingHom.id_apply, map_smul,← Complex.re_add_im c]
    simp only [add_smul,mul_comm _ I,mul_smul,spread_add,spread_real,spread_i] -- simp comm direction?
lemma extend_starts (f : Col →ₗ[ℝ] U) (x : Col) : extend f (embedC x)=f x := by
  simp [extend,plain_self (trace_clear x),spread,axis1_self,axis2_self]
end
lemma project_sways (g : E) (u : Fund) (p : u∈Lie) :
    projectC (conjA (basic g) u)=group.adjoint g (projectC u) := by
  apply embedC_injective; rw [embedC_project_self (carries_su g p),moved,embedC_project_self p]
lemma extend_carries {t : E → Op n} (f : Col →ₗ[ℝ] Op n) (h : ∀ x g, f (group.adjoint g x)=conjA (t g) (f x)) (g X) :
    extend f (conjA (basic g) X) = conjA (t g) (extend f X) := by
  change spread f (plain _) = conjA _ (spread f (plain X))
  rw [plain_conj]; simp only [spread,axis1_stays,axis2_stays,conj_add,conj_smul, project_sways g _ (axis1_mem (plain_zero _)),project_sways g _ (axis2_mem (plain_zero _)), h]
end YM.CF.SatinStressData
