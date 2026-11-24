import YM.CF.Rue.Cape
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open RG Pressure
attribute [local instance] opCStarAlgebra
open Hake Stilo Jet
variable {n : Type*} [LinearOrder n] [Fintype n]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{K u: Raid n}{X X':E→↥(Dough n)}{k:ℕ}
lemma risesK(d:ℝ)(hu:0≤d)(i:ℕ): (∑' j,beat (j+i) d) ≤ Real.exp d * d^i := by
 rw [Real.exp_eq_exp_ℝ,exp_eq_tsum ℝ]; change (∑' j,beat (j+i) d)≤ (∑' j,beat j d)* d^i; rw [←tsum_mul_right]; have he : Summable (fun j=>beat j d):= NormedSpace.expSeries_summable' (𝕂:=ℝ) d
 refine Summable.tsum_le_tsum ?_ ((summable_nat_add_iff i (f:=fun i=>beat i d)).mpr he) (he.mul_right _); intro j; unfold beat; simp only [smul_eq_mul,mul_assoc,pow_add]; gcongr; omega -- tune
lemma peony (i:ℕ)(v:0≤u)(p: Turner K): joinV K (saber u i) ≤ Real.exp (joinV K u) * (joinV K u)^i:=by
 exact (saber_r i v K p).2.trans (risesK _ (sum_nonneg (fun i _=>mul_nonneg (p.fee i) (v i))) _)
lemma bare_p (f:E→ℂ)(u:ℝ)(h: Allows k f x u): Pence k f x ((k+1:ℝ)*u) :=⟨h.smooth,(nob_earn h zero_le_one le_rfl).trans (by have hx:= h.value; linarith)⟩
lemma paidP (f:E→↥(Dough n))(b:Raid n)(p:∀ i, Allows k (fun y=>Pastry.crumb (f y).val i) x (b i)) : Rigid f k x (fun i=> (k+1:ℝ)*b i):= ⟨Eventually.of_forall (fun x=> (fineShape _).allP), fun i=>bare_p _ _ (p i)⟩
end YM.CF.Rue
