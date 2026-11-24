import YM.CF.Buffered.Ages
/-!
# Buffered corollary. Entry if using detailed receipt version

Mathematical hypotheses on the **same regulator diagram** with prescribed estimates of preceding results.
See `the construction notes`. Assumes the hypotheses of THAT corollary: in particular not proving existence of
calibrations, calendar, conductors, supports fitting any small period or any limiting expectation.
The reads in the conclusion are literal sharp CapP ones. -/
set_option autoImplicit false
set_option synthInstance.maxSize 23000
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Buffered.Concert
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory ProbabilityTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py Mail.Unison Mail Scree
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal NNReal ComplexConjugate
attribute [local instance] opCStarAlgebra
open Lobby
open Bilinear
variable {K: Calibration}{C:Conveyor K}{J:Tiling K}{V:SpanCal K} (W:Backed K C J V)
variable {e:ℝ} (p:Tol e)
local notation "Y"=> Purchase V.spanX p.pos K.vertex -- proof defaults implicit?
local notation "P"=> Printed.narrative (Backed.print C W)
-- assume pivot exceeds stated thresholds and G clocks arranged. supply stronger output ❤
variable (h:(Purchase V.spanX p.pos K.vertex).v' ≤ K.h)
variable (z:ℤ)(u: Ballad.Melody.Budget (Ballad.Venue.towards K.B (Lobby.origin K.B K.vertex) z) (Domain J.d' K.B) (K.ℓ+(Purchase V.spanX p.pos K.vertex).w+1) 0)
variable (Lr: howR V.spanX p.pos ≤ K.vertex) (Lq: longitude K V p.pos Lr ≤ K.c K.q)
variable (x:h_g V.spanX p.pos K.J K.η K.vertex K.a K.p K.i K.N0 (Purchase V.spanX p.pos K.vertex) K.h K.R0 K.δ V.c V.k V.portX K.positive_h V.enough_h h ≤ K.x)
variable (x':h_a V.spanX K.J K.η K.a K.p K.i K.N0 J.d' K.h K.R0 K.δ V.c V.k K.positive_h ≤ K.x)
variable (H:(Real.log K.x)^4 ≤ (K.q.val:ℝ))(Z:onAge (plusV (opens K V p.pos (Purchase V.spanX p.pos K.vertex) h J)) (creditA (opens K V p.pos (Purchase V.spanX p.pos K.vertex) h J)+1) K.B J.d'≤ J.qcount K.q)
variable {T:Type}[MeasurableSpace T] {S:Finset Cover}{μ:List Pont.Ink→ℝ≥0∞}{ν: Measure T}[IsProbabilityMeasure ν]
-- earlier unverified input includes the special Loom implementation & its law conditions; not inferred from just saying 'every Month' or 'every cap'.
variable (α: Sensor K C S T μ ν)
include W p h x x' H Z Lr Lq z u α
-- pin input in W (Budget, ScaleK), `x` fixed in K. Criterion `forall m∈..` really level0 of bill-E for all m. here phrase even slightly stronger than Burn.Budget states.
lemma sharp_billE_cone : ∀ᶠ n in atTop, ∀ m:Side, K.takes m → m.val^5 ≤ n → (∀ j≤n,partitionZ (C.sharp m n j) K.P (C.loom m j)≠0) ∧
   0 < partitionZ (C.warm m n 0) K.P (C.loom m 0) ∧
   ‖atZero K.P (C.sharp m n) (C.loom m) (word K m)-P20‖< e ∧ ‖atZero K.P (C.sharp m n) (C.loom m) ((word K * thetaK K (word K)) m)-(compared:ℂ)‖<e:=by -- same x
 have ht := fields K V p.pos Y h J Lr Lq x x' H Z; have hx := buy_here K V p.pos Y h J z u; filter_upwards [certainly C (opens K V p.pos Y h J) ht hx α W,Corollary.cuts (Comparisons.hist P),K.sides] with n t v w; intro m h' a; have he:K.Allowed m n := ⟨h', w.2 m h' (le_trans (by nth_rw 1 [←pow_one m.val]; exact pow_le_pow_right₀ m.property (by decide)) a),a⟩ -- tune
 exact ⟨(v m he).2.1,(v m he).2.2,t m he⟩

variable {s: Process K}{E:Family K→ℂ}{wide:Bool}(B:Settled (Comparisons.hist (Printed.narrative (Backed.print C W))) s wide E)
omit h x x' H Z Lr Lq z u α p
include B
-- Same E. Also can invoke on `Settled` for any Histories or weaker Rates input `Printed`.
theorem whole : E 1=1 ∧
    (∀ f g:eligible K wide, E (thetaK K f.val * g.val)=star (E (thetaK K g.val*f.val))) ∧
    (∀ f:eligible K wide,0 ≤ E (thetaK K f.val*f.val)) ∧
    (∀ (I:Type)[Fintype I] (f:I→eligible K wide), Matrix.PosSemidef (Matrix.of fun i j=> E (thetaK K (f i).val * (f j).val))) := by
 obtain ⟨v,r,t⟩:= Corollary.positive _ _ B; exact ⟨v,fun f g=>(r f g).symm,t,fun _ _ F=> Corollary.matrix _ _ B F⟩ -- tune
include h x x' H Z Lr Lq z u α p
lemma conclude : E (word K) ≠ 0 ∧ Eligible K wide (Corollary.centered B) ∧ 0 < E (thetaK K (Corollary.centered B)*Corollary.centered B) ∧ 0 < Real.sqrt (E (thetaK K (Corollary.centered B)*Corollary.centered B)).re := by
 apply Corollary.output p B
 filter_upwards [sharp_billE_cone W p h z u Lr Lq x x' H Z α] with n b; intro m t; exact (b m t.1 t.2.2).2.2
end YM.CF.Buffered.Concert
#print axioms YM.CF.Buffered.Concert.conclude
#print axioms YM.CF.Buffered.Concert.whole
