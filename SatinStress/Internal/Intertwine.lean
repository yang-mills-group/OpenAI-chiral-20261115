import SatinStress.Internal.ColorLine

set_option autoImplicit false
noncomputable section
namespace YM.CF.SatinStressData
open Gauge SU Function Set
open Complex (I)
open NormedSpace Matrix
open scoped Matrix Kronecker Topology BigOperators Matrix.Norms.L2Operator
-- Match Matter.Anomaly.eachD for derivative
attribute [local instance] opCStarAlgebra

abbrev SheetEnd := Op Sheet
-- $\wedge^2$ and $\bar 5$ generators extended to complexified traceless matrices.
def upper (x : Fund) := ExTwo.gen x
def lower (x : Fund) := -xᵀ

def scheme (a b : ℂ) : Fund →ₗ[ℂ] SheetEnd where
  toFun x := Join.both (a • upper x) (b • lower x)
  map_add' x y := by
    have he : upper (x+y) = upper x + upper y := by
      unfold upper; ext i j; simp [gen_entry,mul_add, add_mul]; abel
    unfold lower
    rw [he, transpose_add,neg_add,smul_add,smul_add,Join.both,Join.both,Join.both,fromBlocks_add]; simp
  map_smul' c x := by
    have he : upper (c • x)=c • upper x := by unfold upper; ext i j; simp [gen_entry]; ring
    rw [he,smul_comm a,lower,transpose_smul,← smul_neg,smul_comm b,RingHom.id_apply]
    unfold lower Join.both; rw [fromBlocks_smul]; simp

def spinRep := scheme 1 1
lemma real_generator {x : Fund} (h : x ∈ Lie) : spinRep x=sheetD x := by
  have e : star x = -x := ((belongs _).mp h).1
  simp only [spinRep, scheme, LinearMap.coe_mk, AddHom.coe_mk,one_smul,sheetD,cc]; rw [e]; simp; rfl

def holds (X Y : SheetEnd) := X*Y=Y*X
abbrev mat (u : E) : Op Sheet := each (fund u)
lemma firstU (u : E) : (mat u) ∈ unitary _ := each_mem u

/-- SU-fixed PH Slot matrix (for one generation block). -/
def FixedS (A : SheetEnd) := ∀ u : E, holds (mat u) A
/-- adjoint weight for the one occurrence of Color in a Mixed entry, complexified version. -/
def AdjS (f : Fund →ₗ[ℂ] SheetEnd) := ∀ g A, A.trace=0 →
   f (conjA (basic g) A) * mat g = mat g * f A

lemma commute_to {g A X : SheetEnd} (p : g∈unitary _) (z : A=conjA g X) : A*g=g*X := by rw [z,conjA,Matrix.mul_assoc,p.1,mul_one]
lemma commute_from {g A X : SheetEnd} (p : g∈unitary _) (z : A*g=g*X) : A=conjA g X := by rw [conjA,← z,mul_assoc,p.2,mul_one]
section scheme
open ExTwo
lemma sector_scheme (a b) : AdjS (scheme a b) := by
  intro g A h
  let U := fund g
  have e : conjA (basic g) A * U = U*A := by
    unfold conjA; rw [show basic g=U from rfl, mul_assoc, (fund_U g).1,mul_one]
  have hU : cc U * Aᵀ = (conjA U A)ᵀ * cc U := by
    unfold conjA cc; rw [← transpose_mul, ← transpose_mul];
    congr 1; rw [← mul_assoc, ← mul_assoc,(show star U * U = 1 from (fund_U g).1),one_mul]
  have hv : gen (conjA U A) * wedgeOp U = wedgeOp U * gen A := by
    apply q_inj; rw [← Matrix.mul_assoc,gen_tensor,Matrix.mul_assoc,← wedgeTensor,← Matrix.mul_assoc (Q F), ← wedgeTensor, Matrix.mul_assoc _ (Q F),gen_tensor,← Matrix.mul_assoc,← Matrix.mul_assoc]
    congr 1
    unfold current; rw [add_mul,mul_add]
    change (conjA U A ⊗ₖ 1) * (U ⊗ₖ U) + _ = _ -- syntax dims maybe impossible
    simp only [op_kron_mul,one_mul,mul_one,show conjA U A * U = U*A from e]
  change Join.both (a • gen (conjA U A)) (b • -((conjA U A)ᵀ)) * Join.both (wedgeOp U) (cc U) = Join.both (wedgeOp U) (cc U) * Join.both (a • gen A) (b • -(Aᵀ))
  rw [Join.both_mul,Join.both_mul]; simp [hv,hU]

lemma rep_adjoint {g : E} {A : Fund} (h : A∈Lie) : spinRep (conjA (basic g) A) = conjA (mat g) (spinRep A) :=
  commute_from (firstU g) (sector_scheme 1 1 g A (((belongs _).mp h).2))
end scheme

private lemma currency (X : Fund) (t : ℝ) (he : X∈Lie) : ∃ u : E, fund u = exp (t•X) := (Gauge.mem_lie _).mp he t

private lemma moving (X : Fund) : HasDerivAt (fun t : ℝ => exp (t • X)) X 0 := by simpa using! hasDerivAt_exp_smul_const X (0:ℝ)
private lemma movingRep (X : Fund) (he : X∈Lie) : HasDerivAt (fun t : ℝ => each (exp (t • X))) (spinRep X) 0 := by
  rw [real_generator he]; exact eachD (by simp) (moving X)

-- extend equations along each complexified direction traceless. -- Real tuple X,Y use exp.
def commuteCost {n : Type*} [Fintype n] [DecidableEq n] (X Y : Op n) := X*Y - Y*X
private lemma evolve_fixed (T : SheetEnd) (e : FixedS T) {X : Fund} (p : X∈Lie) : holds (spinRep X) T := by
  let u (t : ℝ) := each (exp (t•X))
  have h : (fun t => u t * T)=(fun t => T * u t) := by
    funext t; obtain ⟨g,hg⟩ := currency X t p; exact (show u t * T = T * u t by unfold u; rw [← hg]; exact e g)
  have hd := (movingRep X p).mul_const T
  change HasDerivAt (fun t => u t * T) _ _ at hd
  rw [h] at hd
  exact hd.unique ((movingRep X p).const_mul T)
lemma differentiate_fixed (T : SheetEnd) (e : FixedS T) {X : Fund} (h : X.trace=0) :
    holds (spinRep X) T := by
  have h1 : Commute (spinRep (axis1 X)) T := evolve_fixed T e (axis1_mem h)
  have h2 : Commute (spinRep (axis2 X)) T := evolve_fixed T e (axis2_mem h)
  rw [← two_axes X,map_add,map_smul]
  exact (h1.add_left (h2.smul_left I)).eq

private lemma evolve_adj (f : Fund →ₗ[ℂ] SheetEnd) (e : AdjS f) {X : Fund} (p : X∈Lie) {A : Fund} (h : A.trace=0) :
    f (commuteCost X A)=commuteCost (spinRep X) (f A) := by
  let u (t : ℝ) := exp (t•X)
  have h1 : u 0 = 1 := by simp [u]
  have h0 : conjA (u 0) A=A := by simp [conjA,h1]
  have he : (fun t => f (conjA (u t) A) * each (u t)) = (fun t => each (u t) * f A) := funext fun t => by
    obtain ⟨g,hg⟩ := currency X t p; change fund g = u t at hg; rw [← hg]; exact e g A h
  let r := f.restrictScalars ℝ
  have hv : HasDerivAt (fun t => conjA (u t) A) (commuteCost X A) 0 := by
    have pt := moving X; change HasDerivAt u X _ at pt
    unfold conjA commuteCost
    simpa [sub_eq_add_neg,((belongs X).mp p).1,h1] using! (pt.mul_const A).fun_mul pt.star
  have hh := ((LinearMap.toContinuousLinearMap r).hasFDerivAt.comp_hasDerivAt _ hv).fun_mul (movingRep X p)
  -- choose explicit args `Y` below for simplification rather than unfold r
  have hD : HasDerivAt (fun t => f (conjA (u t) A)*each (u t))
      (f (commuteCost X A)*each (u 0)+ f (conjA (u 0) A)*spinRep X) 0 := hh
  rw [he,h0,h1,each_one,mul_one] at hD
  have H := hD.unique ((movingRep X p).mul_const (f A)); unfold commuteCost; -- can't unfold inside lhs?
  exact eq_sub_of_add_eq H

lemma differentiate_adj (f : Fund →ₗ[ℂ] SheetEnd) (e : AdjS f) {X A : Fund} (p : X.trace=0) (h : A.trace=0) :
    f (commuteCost X A)=commuteCost (spinRep X) (f A) := by
  have h1 := evolve_adj f e (axis1_mem p) h
  have h2 := evolve_adj f e (axis2_mem p) h
  rw [← two_axes X]
  have hs {n : Type} [Fintype n] [DecidableEq n] (A B C : Op n) : commuteCost (A + I • B) C =
        commuteCost A C + I • commuteCost B C := by simp [commuteCost,mul_add,add_mul,smul_sub]; abel
  rw [hs,map_add,map_smul,h1,h2,map_add,map_smul,hs]
end YM.CF.SatinStressData
