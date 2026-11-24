import YM.CF.Buffered.Glimmer
/-! Torus recipe from lemma Loomloc. We keep its Basic sampler implementation property, since not implied by `LoomLaw.lawn` alone! No proof required of constructing any of these samples or the legal Basic map, etc. because the corollary uses *this choice* of Loom. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory ProbabilityTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py Mail.Unison Mail Scree
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal NNReal
attribute [local instance] opCStarAlgebra
variable {T:Type}[MeasurableSpace T] {S:Finset Cover}{μ:List Pont.Ink→ℝ≥0∞}{ν: Measure T}[IsProbabilityMeasure ν]
structure Sensor (Q: Calibration) (C: Conveyor Q) (S:Finset Cover)(T:Type)[MeasurableSpace T](μ: List Pont.Ink→ℝ≥0∞)(ν:Measure T)[IsProbabilityMeasure ν] where
 reads (m:Side)(i:ℕ)(h: Q.takes m) : Pont.Colors S T μ ν (cell m Q.B Q.R.L i) Q.w (C.loom m i)
 vote (m k:Side)(h: Q.takes m) (p:m=Q.q*k) (i:ℕ) : Pont.Replicable (C.loom m i) (C.loom Q.q i) (certV Q i p) (reads m i h) (reads Q.q i (big_one Q))
variable {Q:Calibration}(C:Conveyor Q){J:Tiling Q}
lemma Sensor.wake (V:Sensor Q C S T μ ν): LacePoint Q C J:=by
 constructor; intro m k i hM p; let d:= J.qcount m; let A:= certV Q i p; let a:= J.native_ord m hM i; let b:= J.native_ord Q.q (big_one Q) i;
 refine Pont.under_one (C.loom m i) (C.loom Q.q i) A _ _ (a.sugar Q.B) (b.sugar Q.B) _ (Pont.dv_up a Q.B) (Pont.dv_up b Q.B) ?_ (V.vote m k hM p i)
 have he:= Burn.rim Q
 apply Subset.trans _ (solid_pad (a.sugar Q.B) 0 (by omega:1+Q.w≤ Q.w+1)); exact Corona.halo_mono le_rfl (solid_pad (a.sugar Q.B) 0 (by omega:Q.w+1+nearZero Q.D ≤ Q.ℓ))
-- Use with sizes/price grants, just the ones needed.
variable {V:SpanCal Q}{e:ℝ}{z:ℤ}(v:Venue V e)
structure Backed (K:Calibration) (C: Conveyor K) (J:Tiling K)(v:SpanCal K): Prop where
 sponsor : ∀ᶠ x in atTop,Nonempty (Sponsor K C J x)
 enroll : enrollment v ≤ K.x
 price1 : under v K.q
 price3 : under v (K.q*3)
lemma Backed.print (W: Backed Q C J V) : Printed Q C J V:= ⟨W.sponsor.mono (fun _ h=>⟨Mail.Unison.book h.some⟩),W.enroll,W.price1,W.price3⟩
lemma certainly (t:Rates v J)(b:Rented v J z)(g:Sensor Q C S T μ ν) (p:Backed Q C J V): BillInput (p.print C).narrative.hist e:= billE (p.print C) v t z b (Sensor.wake C g)
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.certainly
