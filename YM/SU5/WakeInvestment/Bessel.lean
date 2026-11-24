import YM.CF.Flare.Wits
import YM.SU5.WakeInvestment.Generator

/-!
Hilbert-square cost of excitation fragments through the *true* tilt N=flat-projection both halves.
Torus is finite here; the currency bound applies to summing the prices at all sites (degree and
budget in powers of p_X to be charged separately), hence no loss even when routing later an
unguarded letter to every single such address. Applies before paying the logarithmic Ward weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.WakeInvestment
open Function Set Filter Fock Lattice Finset NormedSpace Matrix
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I]
variable {A P:Op I} (x:Wave I)

/-- Particle booked over and above Flat. Its projection will be $1-P$. -/
def plusCost (A : Op I) := (inner ℂ x (acts (dg A) x)).re

def minusCost (A : Op I) : ℝ := A.trace.re*‖x‖^2 - plusCost x A

def heatCost (P : Op I) := (inner ℂ x (acts (excit P) x)).re

theorem costs_add (P : Op I) : plusCost x (1-P) + minusCost x P = heatCost x P := by
  unfold minusCost plusCost heatCost excit
  rw [show dg (1-P-P) = dg (1-P)-dg P from dyad_sub (1-P) P .., act_add,act_sub,realScalarActs,act_one,
    inner_add_right, ←Complex.coe_smul (Matrix.trace P).re x, inner_smul_right,
    inner_sub_right, Complex.add_re,inner_self_eq_norm_sq_to_K,Complex.sub_re]
  simp [←Complex.ofReal_pow]; ring

theorem particleGram (A : Op I) : plusCost x (A*star A) = ∑ i, ‖acts (Fock.remove (acts A (basisKet i))) x‖^2:=by
  unfold plusCost; rw [prizeUV,act_sum,inner_sum,Complex.re_sum]; apply sum_congr rfl
  intro i _; rw [act_mul,←act_inner, inner_self_eq_norm_sq_to_K]; simp [←Complex.ofReal_pow]

theorem holeGram (A : Op I) : minusCost x (A*star A) = ∑ i, ‖acts (create (acts A (basisKet i))) x‖^2:=by
  unfold minusCost; rw [particleGram]; symm; apply eq_sub_of_add_eq; rw [←sum_add_distrib]
  simp_rw [fun (i:I)=>(show ‖acts (create (acts A (basisKet i))) x‖^2+‖acts (Fock.remove (acts A (basisKet i))) x‖^2 = _ from Flare.snow _ _)] -- type tune
  rw [←sum_mul]; apply congr_arg (· * ‖x‖^2); rw [Matrix.trace_mul_comm,Matrix.trace,Complex.re_sum]; apply sum_congr rfl
  intro i _; rw [Matrix.diag_apply,←basis_act (star A*A),←basis_inner,act_mul,←act_inner,star_star,inner_self_eq_norm_sq_to_K]; simp [←Complex.ofReal_pow]

theorem positiveCosts (h : 0 ≤ A) : 0 ≤ plusCost x A ∧ 0 ≤ minusCost x A := by
  let V:= CFC.sqrt A; have he:star V=V:= (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
  have ht:V*star V=A:= by rw [he]; exact CFC.sqrt_mul_sqrt_self A h
  rw [←ht,particleGram,holeGram]; exact ⟨sum_nonneg fun _ _=> sq_nonneg _, sum_nonneg fun _ _=> sq_nonneg _⟩

lemma scaleCosts (A:Op I)(u:ℝ) : plusCost x (u • A)= u*plusCost x A ∧
    minusCost x (u • A)= u*minusCost x A := by
  have he : plusCost x (u • A)= u*plusCost x A := by
    unfold plusCost; rw [dg_scale,realScalarActs,← Complex.coe_smul u (acts _ x),inner_smul_right]; simp
  constructor; exact he
  unfold minusCost; rw [he, trace_smul]; simp [Complex.real_smul]; ring

lemma monoCosts (h : A ≤ P) : plusCost x A ≤ plusCost x P ∧ minusCost x A ≤ minusCost x P := by
  obtain ⟨a,b⟩:= positiveCosts x (sub_nonneg.mpr h)
  have he : plusCost x (P-A)=plusCost x P - plusCost x A := by
    unfold plusCost; rw [show dg (P-A)=dg P - dg A from dyad_sub ..,act_sub,inner_sub_right,Complex.sub_re]
  rw [he] at a; unfold minusCost at b; rw [trace_sub,Complex.sub_re,he] at b
  refine ⟨sub_nonneg.mp a,?_⟩; unfold minusCost; linarith only [b]

omit x in
private theorem holds (p : IsStarProjection P) (A: Op I) (C:ℝ) (h:‖A‖ ≤ C) :
    P*A*star (P*A) ≤ C^2 • P := by
  have he : A*star A ≤ C^2 • (1:Op I) := by
    rw [←Algebra.algebraMap_eq_smul_one]
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C) (mul_star_self_nonneg A)).1
    rw [CStarRing.norm_self_mul_star,←sq]; exact pow_le_pow_left₀ (norm_nonneg _) h _
  rw [star_mul,p.isSelfAdjoint.star_eq]
  apply le_trans _ ((star_right_conjugate_le_conjugate he P).trans_eq ?_); · exact le_of_eq (by rw [p.isSelfAdjoint.star_eq]; noncomm_ring)
  rw [p.isSelfAdjoint.star_eq,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,p.isIdempotentElem.eq]

def both (P : Op I) (v : Ket I) := ‖acts (Fock.remove (acts (1-P) v)) x‖^2 + ‖acts (create (acts P v)) x‖^2
lemma both_ge (P : Op I) (v : Ket I) : 0 ≤ both x P v := by unfold both; positivity

theorem wakeBessel (p : IsStarProjection P) (A:Op I) (C:ℝ) (h:‖A‖ ≤ C) :
    ∑ i, both x P (acts A (basisKet i)) ≤ C^2*(heatCost x P) := by
  unfold both
  simp_rw [sum_add_distrib,←act_mul]; rw [←particleGram,←holeGram,←costs_add,mul_add,
    ←(scaleCosts x (1-P) _).1,←(scaleCosts x P _).2]; exact add_le_add (monoCosts x (holds p.one_sub _ _ h)).1 (monoCosts x (holds p _ _ h)).2

theorem heat_nonneg (p:IsStarProjection P) : 0 ≤ heatCost x P := by
  rw [←costs_add]; exact add_nonneg (positiveCosts x p.one_sub.nonneg).1 (positiveCosts x p.nonneg).2

#print axioms wakeBessel
end YM.CF.WakeInvestment
