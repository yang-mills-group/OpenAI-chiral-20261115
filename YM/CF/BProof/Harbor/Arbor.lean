import YM.CF.BProof.Harbor.Glance
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory ProbabilityTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Skye Regard Vogue Mesh Shore
open Wager
namespace Arbor
variable {I E D:Type} [Fintype I][DecidableEq I]
-- Forest merge used internally in product identity. Keep native cache Fintype.
variable {n f:Side} {S: Ratio n f} {T:Support n}
attribute [local instance] Wager.measureVal Wager.billVal
scoped instance (g:Ratio n f) : MeasurableSpace (Forest g):= ⊤
scoped instance (g:Ratio n f): MeasurableSingletonClass (Forest g):= ⟨fun _=> trivial⟩
lemma idem{c f:Side}{S:Ratio c f}(A B:Forest S)(a:A.up=B.up)(b:A.height=B.height): A=B:=by cases A; cases B; congr
def blend (S:Ratio n f)(T:Support n) (Y Z:Forest S):Forest S where
 up i:= if S.parent i∈ T then Y.up i else Z.up i
 height i:= if S.parent i∈T then Y.height i else Z.height i
 bound i:= by split <;> first| apply Y.bound | apply Z.bound
 rise i p:= by by_cases g:S.parent i∈T; simp only [g,ite_true,Y.stays i p]; exact Y.rise i p; simp only [g, ite_false,Z.stays i p]; exact Z.rise i p
 stays i p:=by split <;> first | apply Y.stays i p| apply Z.stays i p
lemma budget(T:Support n)(X Y:Forest S): blend S T (blend S T X Y) (blend S T Y X)=X:=by
 apply idem <;> funext i <;> unfold blend <;> dsimp only <;> by_cases h:S.parent i∈T <;> simp only [h, ↓reduceIte] -- tune
abbrev visits (X:Type)(F:Forest S → X)(D : Support n) := ∀ i j:Forest S,(∀ x,S.parent x∈D→ i.up x=j.up x)→F i=F j
def ride (S:Ratio n f) (T:Support n)(x:Forest S × Forest S):Forest S × Forest S:= (blend _ T x.1 x.2,blend _ T x.2 x.1)
def pens (S:Ratio n f)(T:Support n): Equiv.Perm (Forest S × Forest S):= ⟨ride S T,ride S T, fun ⟨x,y⟩=>Prod.ext (budget T x y) (budget T y x),fun ⟨x,y⟩=>Prod.ext (budget T x y) (budget T y x)⟩
def grove (T:Ratio n f):=paperMeas (Forest T)
instance (T:Ratio n f)[Nonempty (Forest T)]: IsProbabilityMeasure (grove T):=by unfold grove; infer_instance
open Wager
variable [Nonempty (Forest S)]
lemma vote(F G:Forest S→ℂ){X Y:Support n}(h:Disjoint X Y)(v:visits _ F X)(q:visits _ G Y): meanS (grove S) (fun x=>F x*G x)= meanS (grove S) F*meanS (grove S) G:=by
 refine shake _ _ _ (pens S X) ?_ (measurable_of_countable _) (measurable_of_countable _) (fun x=> congrArg₂ (·*·) (v _ _ (fun i p=> if_pos p)) (q _ _ fun i p=> if_neg (fun t=> Finset.disjoint_left.mp h t p)))
 unfold grove; rw [←Vogue.parcelPair]; apply Vogue.orderMP
lemma voteP (F G:Forest S→Op I){X Y:Support n}(h:Disjoint X Y)(v:visits _ F X)(q:visits _ G Y): meanS (grove S) (fun x=>F x*G x)= meanS (grove S) F*meanS (grove S) G:= factorM (mean_f F) (mean_f G) (fun i j k=>vote _ _ h (fun x y z=> congrArg (penny i k) (v x y z)) (fun x y z=>congrArg (penny k j) (q x y z)))
lemma likely [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](F:Forest S→ E): meanS (grove S) F=(Fintype.card (Forest S):ℝ)⁻¹ • ∑ i,F i:=by
 rw [meanS,integral_fintype (Law.pay (ν:=grove S) (mean_f F)),Finset.smul_sum]; refine Finset.sum_congr rfl ?_; intro i _; simp [Measure.real,grove, ENNReal.toReal_inv] -- tune
end Arbor
end YM.CF.BProof.Bide
