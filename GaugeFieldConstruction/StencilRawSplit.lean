import YM.SU5.Six.SplitPredict
/-! # Test same-price calibrated comparison also on the pure Ink stencil prices

Use pure raw *both Pane* scalar marks, and the pure even matter-word
polynomials on the Dome (including their linear extension). Ward on either
pure algebra suffices. These are one-level comparisons, at every fine
consultation; NOT testing factorization in dressed/gauge-fixed variables.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
variable (K:Calibration)
local notation "A"=> Dome K

-- in that order. Pure gauge commutes pointwise BEFORE taking even the common Price.
lemma PureGauge.commutesTestSt {x:A}(h: PureGauge K x)(y:A): Commute x y :=by
 obtain ⟨s,f,g,H⟩:=h; change x*y=y*x;
 apply Subtype.ext; change x.val*y.val=y.val*x.val; rw [H]
 funext a b; simp only [Pi.mul_apply,scalar,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,mul_one]
theorem Comparison.firstMatterSt {x y:A} (h:PureGauge K y)(g:PureMatter K x){E F:A→ₗ[ℂ]ℂ}(e:Comparison K E F) : F (x*y)= E x * E y:=by
 rw [(PureGauge.commutesTestSt _ h x).eq.symm,e.factors y x h g,e.link y h,e.matter x g,mul_comm]
#print axioms Comparison.firstMatterSt
end YM.CF.Buffered.Afterglow.Six
end
