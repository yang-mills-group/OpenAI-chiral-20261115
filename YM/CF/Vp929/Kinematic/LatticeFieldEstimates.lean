import YM.CF.Vp929.Kinematic.Lid
import YM.CF.Vp929.Bank.Pour
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
local notation "G5"=> SU.group
local notation "S'"=> w.step V
local notation "y"=> Scales.y SU.group R.L x
local notation "ι" => Scree.mid m B
local notation "η" => Scree.mid n B
local notation "z'" => (coming D.Z 105 5*radiusB x)
variable {o : Pitching w D x}
local notation "Bs" v:max F:max => base (q:=q) (J:=J) (w:=w) p' v F
local notation "Ys" β:max F:max=> Pitching.input (V:=V) (w:=w) p' β F
local notation "Xs" β:max => Pitching.start (V:=V) (w:=w) p β
local notation "A'"=> o.muster
local notation "P'"=> D.pilot
local notation "Up" v:max=> (tint_z o.muster v)
local notation "Jq"=> (w.Φ (V:=V))
namespace Lid
variable (H: Lid o p p' f)
variable {F F': Corr (Scree.mid n B)}
local notation "τ"=> radiusB x
variable (Mk: Monk SU.group (w.step V))(A₀:Ids (Scree.mid m B))(T₁:Ids (Scree.mid n B))
local notation "Rc" v:max=> poleY Mk v (Scales.y SU.group R.L x)
local notation "Δ" => (o.muster.post+90)*radiusB x
local notation "Δ₀"=> (D.pilot.hat R x)
local notation "χ"=> (shotM o.muster.vita)
include H
lemma rune_enroll (hb:β∈ Year R x): 1/2 ≤ (Cay.rune β y)^2 ∧ Cay.rune β y ≤ 2:= by
 let s:=Cay.rune β y; have p:=rune_s (H.pos hb) H.night; have U:(2:ℝ)≥β/y:= (div_le_iff₀ H.night).2 hb.2; exact ⟨p ▸ ((le_div_iff₀ H.night).2 (by linarith [show y/2≤β from hb.1])), by nlinarith [H.night]⟩
lemma scaling_p (hb:β∈ Year R x): 0<Cay.rune β y:= rune_p (H.pos hb) H.night
/- set Hβ=H/2 * rune -/
def scaler (hb:β∈ Year R x): Dilation:= ⟨Cay.rune β y/2, ⟨by nlinarith [(H.rune_enroll hb).1,H.scaling_p hb], by linarith [(H.rune_enroll hb).2]⟩⟩
abbrev ZoomB (hb:β∈Year R x):=(P').zoom (H.scaler hb)
lemma hat' (hb:β∈ Year R x): (H.ZoomB hb).hat R x=Cay.rune β y*(Δ₀/2):=by change ((Cay.rune β y/2)*D.pilot.large)*_=Cay.rune β y* ((D.pilot.large*_)/2); ring
lemma park : 0<Δ₀/2:= half_pos (mul_pos D.pilot.high (Scales.pos ..))
abbrev intensity (hb:β∈Year R x):ℝ:= χ ((H.ZoomB hb).hat R x) β
def latticeFieldEstimatesB (o :Pitching w D x) (z:ℂ):ℂ := (shotM o.muster.vita (Δ₀/2) y:ℂ) * Appel.Rate.jug SU.group (Δ₀/2) (z/y)
lemma latticeFieldEstimates_real (hb:β∈Year R x): latticeFieldEstimatesB o (β:ℂ)=(H.intensity hb:ℂ):=by
 let t:= Cay.rune β y; have ht:= Appel.Rate.change_shot (H.scaling_p hb) H.park y β H.night (H.pos hb) rfl o.muster.vita; rw [Cay.rune_s (H.pos hb) H.night] at ht
 unfold latticeFieldEstimatesB intensity; rw [H.hat',←Complex.ofReal_div,Appel.Rate.jug_real]; norm_cast; exact ht.symm
lemma latticeFieldEstimates_entire : Differentiable ℂ (latticeFieldEstimatesB o):= by have h:= (Appel.Rate.jug_entire (G:=G5) H.park).comp (show Differentiable ℂ (fun z=> z/(y:ℂ)) by fun_prop); exact (differentiable_const _).mul h
lemma intensity_pos (hb:β∈Year R x):0<H.intensity hb:= H.shot_p hb _ (H.fend hb _)
end Lid
end Pitching
end YM.CF.Py.Rate
