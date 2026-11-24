import YM.CF.BPress.Habitat.Keys
/-! ℓ - Pigment, primary. Real calculus equals each exact real site trace including Pigment from ONLY Ū repeated Page divide. Trace-log costs on any Inputs Pose.
Variant: It's convenient (though can make three first real trace expansions with reader H and X fees removed as indicated in manuscript) to assemble as one matrix *before* decomposing at fixed node root. Take no dependence on X and H in the evaluate formula for the three real terms other than Loss, but don't require each support summand in a **decomposition** of this site-rooted sum individually ignore these data. We'll bound the omission error in the short test with that permission on all terms, by roots, unchanged power cost (this makes it unnecessary, e.g., to fix decomposition choices across different pricing domains).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf -- tune
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Grid
variable {N:Side}{U:Driver N}{A B C:Pledge}
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]{P Q: Finset I}
namespace Shale
abbrev degZ := Complex.I
abbrev RealC(A:Op I):Op I:= (1/2:ℂ) • (A+cc A)
abbrev ImC(A:Op I):Op I:= A-RealC A
theorem realc(A:Op I)(i j): RealC A i j= ((A i j).re:ℂ):=by apply Complex.ext <;> all_goals simp [RealC,mul_comm] <;> first | ring | rfl -- tune div
lemma imc(A:Op I)(i j) : ImC A i j=((A i j).im:ℂ)*degZ:=by rw [ImC,Matrix.sub_apply,realc]; apply Complex.ext <;>simp [degZ] -- tune
abbrev oxide (P Q:Finset I)(A T C:Op I):=permit A T+permitX P A T+permitY P Q A T+billZ P Q A T C
abbrev shale(P Q: Finset I)(A T: Op I)(C C':ℝ→Op I):= RealC (oxide P Q A T (C 2)) + ImC (streamR P Q A T C C')
lemma real_trace(A:Op I): (RealC A).trace=(A.trace.re:ℂ):=by
 unfold RealC; rw [Matrix.trace_smul,Matrix.trace_add]; have he: (cc A).trace= (starRingEnd _) A.trace:=by unfold Matrix.trace; simp [Matrix.diag]; -- tune
 rw [he]; apply Complex.ext <;> simp [mul_comm] <;> ring
lemma im_trace(A:Op I): (ImC A).trace=(A.trace.im:ℂ)*degZ:=by rw [ImC,Matrix.trace_sub,real_trace]; apply Complex.ext <;> simp [degZ]
lemma trace_sh(A T:Op I)(C C':ℝ→Op I)(t:(streamR P Q A T C C').trace=sweepR P Q A T C C'): (shale P Q A T C C').trace=totalBill P Q A T C C':=by
 unfold shale totalBill; rw [Matrix.trace_add, ←t, real_trace, im_trace]; rfl
variable (P0 B0 S Y K:Pledge)(A B T:Op I)(C C':ℝ→Op I)(r ε d:ℝ)
variable {X D Z:Type}[TopologicalSpace D][Fintype Z][DecidableEq Z]
def limestone(X:Pledge):Pledge:= (X.plus X).scales ‖(1/2:ℂ)‖
abbrev performer(P:Pledge)(Q:Pledge):= (limestone P).plus (Q.plus (limestone Q))
variable {b:Stage Z I D Empty}{F G:D→Finset I}{A' T':Raw D I}{S S':D→ ℝ→ Op I}
structure Grant (U:Pledge) (P L B C:Pledge)(r ε d:ℝ) :Prop where
 to_χ : ∀ {I D Z:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Z][DecidableEq Z][TopologicalSpace D]{b:Stage Z I D Empty}{F G:D→Finset I}{A' T':Raw D I}{S S': D→ℝ→Op I}, Stoke F G A' T' S S' b P L B C ε r d→ U.Costs b (fun x=>shale (F x) (G x) (A' x) (T' x) (S x) (S' x))∧∀ x,(shale (F x) (G x) (A' x) (T' x) (S x) (S' x)).trace= totalBill (F x) (G x) (A' x) (T' x) (S x) (S' x)
lemma lease (p:0<ε)(u:ε≤1)(h:0≤d)(g:0≤r)(y:r<1)(P L B C:Pledge): ∃ V:Pledge, Grant V P L B C r ε d:=by
 obtain ⟨T0,w⟩:=Brooks.feeds P L B C h p g y; obtain ⟨W,w'⟩:= reality p u h B P L; obtain ⟨A,a⟩:= defray C P L B h p g y; let X:= ((W.plus W).plus W).plus A; let M:=Brooks.quadruple T0
 refine ⟨performer X M,⟨?_⟩⟩; intro I D Z _ _ _ _ _ _ b F G A' T' S S' V; let H(z:D):=oxide (F z) (G z) (A' z) (T' z) (S z 2); have hp:= w' V.cap (fun i => (V.peak i).proj) (fun i=>(V.peak i).she) (fun i=>(V.peak i).near) (fun i=>(V.peak i).rails) V.am V.wm V.pA V.pB; let U:=w V; have ht:= Brooks.sell U; have he: X.Costs b H:= Costs.plus (Costs.plus (Costs.plus hp.1 hp.2.1) hp.2.2) (a V); have h(W:Pledge)(X:Raw D I)(p:W.Costs b X): (limestone W).Costs b (fun i=> RealC (X i)):=Costs.smul (Costs.plus p (Costs.stars p)) _
 exact ⟨Costs.plus (h X H he) (Costs.sub ht (h M _ ht)),fun i=>trace_sh _ _ _ _ (Brooks.road U i)⟩ -- tune operand order treasury
end Shale
end YM.CF.BPress.Primary
