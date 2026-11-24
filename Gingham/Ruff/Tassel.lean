import Gingham.Ruff.Ruffle
import YM.CF.Sedge.Craft

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


/-! Bra reduction (127). -/

def 𝒿 (A J : Op n) : FC n := Matrix.trace (A*J) • 1 + dg (A*J*(1-A))

lemma 𝒿_zero (A : Op n) : 𝒿 A 0 = 0 := by
 rw [𝒿,mul_zero,Matrix.trace_zero,zero_smul,zero_mul,dg_zero,add_zero]
lemma 𝒿_add (A X Y : Op n) : 𝒿 A (X+Y) = 𝒿 A X + 𝒿 A Y := by
 rw [𝒿,mul_add,Matrix.trace_add,add_smul,add_mul,dg_add,𝒿,𝒿]
 abel
lemma 𝒿_sub (A X Y : Op n) : 𝒿 A (X-Y) = 𝒿 A X - 𝒿 A Y := by
 rw [𝒿,mul_sub,Matrix.trace_sub,sub_smul,sub_mul,dg_sub,𝒿,𝒿]
 abel
lemma 𝒿_sum {ι : Type*} (A : Op n) (i : Finset ι) (Y : ι → Op n) :
    𝒿 A (∑ a∈i, Y a) = ∑ a∈i, 𝒿 A (Y a) := by
 classical
 induction i using Finset.induction_on with
 | empty => rw [sum_empty,sum_empty,𝒿_zero]
 | insert a i k ih=> rw [sum_insert k,sum_insert k,𝒿_add,ih]

variable {A : Op n} {x : Wave n}



lemma star_trace (M:Op n) : Matrix.trace (star M) = star (Matrix.trace M) := by
  simp only [Matrix.star_eq_conjTranspose,Matrix.trace_conjTranspose]
lemma star_trace_mul {S : Op n} (h : IsStarProjection S) (W : Op n) :
    Matrix.trace (S * star W) = star (Matrix.trace (S * W)) := by
  rw [←star_trace,star_mul,h.isSelfAdjoint,Matrix.trace_mul_comm]

private lemma morning (h : IsStarProjection A) (s : Sea A x) (X : Op n) :
    acts (dg (X*(1-A))) x = 0 := by
  let H := 1-A
  have z := prizeUV X H
  rw [h.one_sub.isSelfAdjoint] at z
  rw [z,act_sum]
  apply sum_eq_zero
  intro i _
  have m := tars h s.1 (v:=acts H (basisKet i)) (by rw [←act_mul,Porth h,act_zero])
  rw [act_mul,m,map_zero]

private lemma daytime (h : IsStarProjection A) (s : Sea A x) (V : Op n) :
    acts (dg V) x = Matrix.trace (A*V) • x + acts (dg ((1-A)*V*A)) x := by
  have e : V = seam A V + (1-A)*V*A + A*V*(1-A) := by
    rw [seam]
    noncomm_ring
  have z := Sault.loft_v _ (seam_comm h V) h x s
  rw [seam_trace h] at z
  nth_rw 1 [e]
  rw [dg_add,dg_add,act_add,act_add,z,morning h s,add_zero]


lemma left_suture (h : IsStarProjection A) (s : Sea A x) (J : Op n) :
    acts (star (dg J)) x = acts (star (𝒿 A J)) x := by
  rw [←dg_star,daytime h s,star_trace_mul h,𝒿,star_add,act_add,star_smul,
    star_one,act_smul,act_one,←dg_star,star_mul,h.one_sub.isSelfAdjoint,star_mul,
    h.isSelfAdjoint,mul_assoc (1-A)]
lemma 𝒿_reads (h : IsStarProjection A) (s : Sea A x) (J : Op n) (y : Wave n) :
    inner ℂ x (acts (𝒿 A J) y) = inner ℂ x (acts (dg J) y) := by
  rw [←act_inner,←act_inner (dg J),left_suture h s]

lemma close_gable (h : IsStarProjection A) (s : Sea A x) (W : Op n) (z : Commute A W) :
    acts (star (gable A W)) x = 0 := by
  rw [gable,star_sub,act_sub,left_suture h s,𝒿,z.eq,mul_assoc,Porth h,
    mul_zero,dg_zero,add_zero]
  -- avoid trace rewrite


  exact sub_self _

/-- Physical RC formula (combine all truncated/masked J contributions first). -/
def portico (A : Op n) (a : ℂ) (L : Op n) :=
    a • (1 : FC n) + 𝒿 A L

/-- Can take W = W or masked version (incl 0). -/
lemma facade_reads (h : IsStarProjection A) (s : Sea A x) (W : Op n) (z : Commute A W)
    (a : ℂ) (L : Op n) (y : Wave n) :
    inner ℂ x (acts (portico A a L) y) = inner ℂ x (acts (facade A W a L) y) := by
  rw [portico,facade,act_add,act_sub,act_add,inner_sub_right,
    ←act_inner (gable A W),close_gable h s W z,inner_zero_left,sub_zero,inner_add_right,
    inner_add_right,𝒿_reads h s]

