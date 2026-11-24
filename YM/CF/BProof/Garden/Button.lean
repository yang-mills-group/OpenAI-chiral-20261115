import YM.CF.BProof.Garden.Tube
namespace YM.CF.BProof.Garden
open Function Filter NormedSpace Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder InnerProductSpace
attribute [local instance] opCStarAlgebra
open MeasureTheory
variable {I:Type}[LinearOrder I][Fintype I]{B:Type*}[MeasurableSpace B]
lemma worker{E V:Type}[TopologicalSpace E][TopologicalSpace V][SecondCountableTopology E][SecondCountableTopology V]{B:Type*}[MeasurableSpace B](f:E × V→ ℂ)(h:Continuous f)(A:B→ E)(T:B→ V)(a:@Measurable _ _ _ (borel _) A)(v:@Measurable _ _ _ (borel _) T):Measurable (fun x=> f (A x,T x)):=by borelize E V; exact h.measurable.comp (a.prodMk v)
lemma button(S T:Finset I)(A:B→Op I)(V:B→ Fock.FC I)(p:@Measurable _ _ _ (borel _) A)(q:@Measurable _ _ _ (borel _) V) : Measurable (fun x=> coeffJ S (A x) T (V x)):=by
 exact worker _ (coeff_cont S T) A V p q
end YM.CF.BProof.Garden
