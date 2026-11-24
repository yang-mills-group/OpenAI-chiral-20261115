import YM.SU5.SatinWard.Resolution.Mimic
import YM.SU5.Reconstruction.Oblique.RollStep
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}
open Tap Waxy Ione.Clock StressFlux SU
namespace SignSlot
open Buffered Swell Porticus Hest Nacre StressExchange Merino.Brooch
local notation "K0"=> Op SU.Slot
open Advance Buffered.Afterglow.Tower Tilted
open Lampshade
-- single travel proofs around W calls, retain Ramp exact at gauge/clover and arm directions.
variable (s:Sweep N)(Z:Tilted.Ramp)(i:Axis)(z:ℤ)
lemma fly_scale (q:ℝ)(U:Mark N): flyMark s (q • U)= q • flyMark s U:=by simpa only [BodyPull,LinearMap.coe_mk,AddHom.coe_mk,inv_inv] using map_smul (BodyPull s⁻¹) q U
lemma spin_shift(f:Op SU.Slot)(h: star f=f) (x y:Site N)(v:Earlier s x y)(p:s.charge=false) : let U(i:Axis)(o:Site N):= onsiteSensor o (petal i ⊗ₖ f); flyMark s (U (s.s.perm i) x)= StressFlux.sign s.s i • U i y:=by
 intro U; apply spot_line s v; rw [castPet (spinZ ..),p,sign_hush,hush_false]; cases detX s.s; rfl; exact congrArg (fun z=> (hush (s.s.flip i) (petal i ⊗ₖ z))) h
local notation "T"=> Z.advance_tag N
local notation "p_"=> Advance.tagMove i z N
local notation "M"=> (plane i z)
local notation "L"=> Levier.ray (N:=N) false Z.plan
lemma turned_plumb (x:Site N): Earlier T x (Z.plan.mills N x):=by
 have hv(y:Site N) : Earlier T (Z.plan.mills N y) y:=by
    unfold Earlier; have ht:T=L:=by change Sweep.mk _ _ _= Sweep.mk _ (wrap _ (0:Cover)) _; rw [map_zero]; rfl
    rw [ht,sitA,Levier.ray,(assembly N).embed_wrap]; exact (Shape.nodex ..).symm
 have h:=hv (Z.plan.mills N x); rw [Z.fence] at h; exact h
lemma turned_m (x:Site N): Earlier (tagMove i z N) x ((M).mills N x):=by
 have ht(y:Site N): Earlier (tagMove i z N) ((M).mills _ y) y:=by unfold Earlier; rw [sitA,tagMove,(assembly N).embed_wrap]; exact (Shape.nodex (plane i z) y).symm
 have h:=ht ((M).mills N x); rw [matter_invol] at h; exact h
lemma rampFly {F:Mark N} {S:Support (More N)}(g:AtSupport false S F): Z.bill F=flyMark T F:=by
 funext u; unfold flyMark Ramp.bill; have he(x:Pane N): flashA T⁻¹ x=Z.turnLink N x:=by nth_rw 1 [← Z.turnover x]; rw [← Z.turn_prior (Z.turnLink N x), revB]; -- precedence T⁻¹
 rw [he,he]; let V':=F (Z.both N u); let Q:= paritySale.checked (g.allV (Z.both N u)).sector
 have ht:T=L:=by change Sweep.mk _ _ _= Sweep.mk _ (wrap _ (0:Cover)) _; rw [map_zero]; rfl
 change Fock.theta (Z.vehicle N) V'=teen T V'; rw [ht,show teen L V'= _ from (hono false Z.plan V' Q)]; unfold yodel; have hv:detX Z.plan.s=true:= Z.proper_pin
 rw [stag_s false _ _ Z.reel _ Q (spinZ ..) (by rw [hv]; exact Z.jet),hv]; rfl
-- Optional tolerance.Enrollees for general Gauge Field plumb.Start Room after supports.What
end SignSlot
end YM.CF.QuadClock
