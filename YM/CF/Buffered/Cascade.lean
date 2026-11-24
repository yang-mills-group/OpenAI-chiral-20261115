import YM.CF.Buffered.Pylon
/-! An ordered Trotter formula; cost at this fixed cutoff and sizes. -/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Trotter
open Function Fock NormedSpace Finset Filter MeasureTheory Lattice Reflect
open Stack
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction
attribute [local instance] opCStarAlgebra
section many
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
lemma many_steps (X : ℕ→ A) (F : ℕ→ ℝ → A) (n:ℕ) (v:∀ i<n,LinearLayer (F i) (X i)) :
 LinearLayer (fun t=> run (fun i=> F i t) n) (∑ i∈range n, X i) := by
 induction n with
 | zero=> refine ⟨0,le_rfl,fun t _=>by simp [run]⟩
 | succ n ih=>
    rw [sum_range_succ,show (fun t=> run (fun i=> F i t) (n+1))= _ from (funext (fun t=>run_succ (fun i=>F i t) n))]; exact (ih fun i h=>v i (by omega)).multiply (v n (by omega))
def braid (X F: ℕ→ A) (n:ℕ) (t:ℝ) := run (fun i=> exp (t • X i)) n * run (fun i=> 1+ t • F i) n
def plays (X F: ℕ→ A) (n:ℕ):ℕ→A := fun i=> braid X F n ((i+1:ℝ)⁻¹)^(i+1)
def ends (X F: ℕ→ A) (n:ℕ) := ∑ i ∈ range n,(X i+F i)
theorem tat (X F: ℕ→ A) (n:ℕ) : LinearLayer (braid X F n) (ends X F n) := by
 rw [ends,sum_add_distrib]; exact (many_steps X (fun i t=> exp (t • X i)) n (fun i _=> LinearLayer.exponential _)).multiply (many_steps F (fun i t=> 1+ t • F i) n fun i _=> LinearLayer.euler _)
theorem rises (X F: ℕ→ A) (n:ℕ): Tendsto (plays X F n) atTop (𝓝 (exp (ends X F n))) := (tat X F n).iterate
-- marked proof with continuity in generator. Need L∞ bounds in the theorem, Envelope enough. easiest assume each Fock generator on ANY x continuous (matrix H and split parts and hops). no weights. use bounded-continuous uniform norm
section cont
variable {Y:Type*}[TopologicalSpace Y][Nonempty Y][CompactSpace Y]
lemma runEval (F:ℕ→ Y →ᵇ A)(x:Y) (n:ℕ): run F n x=run (fun i=>F i x) n :=by induction n with| zero=> rfl| succ n ih=> rw [run_succ,run_succ]; exact congrArg (· * F n x) ih
open BoundedContinuousFunction
theorem bounded {I : Type*}[LinearOrder I][Fintype I](F G:ℕ→ Y → FC I)(p:∀ i,Continuous (F i)) (q:∀ i,Continuous (G i))(n:ℕ) :
    (∀ i,Continuous (fun x=> plays (fun j=> F j x) (fun j=> G j x) n i)) ∧ ∃ C:ℝ,∀ i x, ‖plays (fun j=> F j x) (fun j=> G j x) n i‖≤ C := by
 let f i := BoundedContinuousFunction.mkOfCompact (⟨F i,p i⟩); let g i := BoundedContinuousFunction.mkOfCompact (⟨G i,q i⟩)
 let K(i):=plays f g n i; have hz:=rises f g n; have hp (i x): K i x= plays (fun j=> F j x) (fun j=>G j x) n i := by
    unfold K plays braid; rw [BoundedContinuousFunction.pow_apply, BoundedContinuousFunction.mul_apply,runEval,runEval]; simp_rw [eval_exp]; rfl
 constructor; · intro i; simp_rw [←hp i]; exact (K i).continuous
 obtain ⟨C,c⟩:= hz.norm.bddAbove_range; exact ⟨C,fun i x=>hp i x ▸ ((K i).norm_coe_le_norm x).trans (c ⟨i,rfl⟩)⟩
end cont
end many
end YM.CF.Buffered.Trotter
