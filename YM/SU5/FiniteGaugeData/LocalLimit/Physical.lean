import YM.SU5.FiniteGaugeData.LocalLimit.Voyage
import YM.CF.Girt.Oar

/-!
# Dictionary of regulator objects (volume theorem)

These statements apply on the actual `Tape` sessions bought here. In particular
this is *not* input gauge or family from an interval-comparison substitute, nor
does `texture` use a real-probability density other than the given **base**
`city`. Kets in this read are at the indicated effective level in the *same*
system, constructed by `Pull_P` all the way from launch using its very given cap at
the UV top. See `Brioche.note`, `.hot`, `.wear` under `note`; observations of several
resolutions simultaneously remain extra prescriptions. No positivity assertion on
ordinary signed/complex FiniteGaugeData density made here. Antiperiodic cuts are in all four
coordinates; `More` lattice is gauge, `cell` lattice (`CSide`) fermions.
Not a statement about continuum matter.
-/
set_option autoImplicit false
set_option quotPrecheck false
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
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open FullBill Window Marks
open Pyx
open Girt

namespace Preparation
local notation "q₀" => Chi.canonical
variable {P : Preparation} {F : (s:Side)→ Scree.Loom s → Prop} (Y:Course P F)

namespace Course
variable (i k j : ℕ)
local notation "Ξ" => Y.voyage i
local notation "U₀" => P.U
local notation "N₀" => (Ξ).funds
local notation "m₀" => Y.ir i
local notation "CS" => P.Ctor (Y.ir i)
local notation "kt" => Y.uv k
local notation "Xv" => (Ξ).X (Y.uv k)
local notation "Χ" j => (Xv).gram j
local notation "Qv" => (Ξ).CapeT
local notation "T" => Y.meter
local notation "Yr" => Vale.mesh m₀ P.R.L

lemma history : Brioche P.V 1 2 6 P.N0 T m₀ N₀ kt (Xv).pilot P.J q₀ P.h P.R0 P.δ
      (Xv).gram Qv (Xv).wave (Xv).fee := Parcel.hasBrioche P.V Xv Y.paidM (Ξ).ownership

lemma whole (v : Orbit (CS kt)) : denZ (Χ kt) P.U (Qv kt) v=Vale.capP (K:=P.K) P.U (Χ kt).beta (Y.meter.a kt) v.1 :=
    ((Y.history i k).hot P.V _ P.J q₀ P.h P.direct).2 v

-- At precisely the top with those CapP beta and BudgetPoint at this n, *same*
-- Guard as this Loom and Grasp. The projector in all further contractions on the
-- cap is the given `anticut` projector, not an external heat or mass ansatz.
lemma equity (V : Pane (CS kt))(h : flags (Y.meter.a kt).threshold V=∅) :
    spar P.K.j Vale.babyM V=portW (Tulip.helix _).symm (projector (frame SU.matter (Cube.links V) (anticut _)).H) ∧ Sea (spar P.K.j Vale.babyM V) (changeM (m:=Yr kt) P.U V Vale.babyM) := by
  let M:= Y.history i k
  have he:=(M.roof kt).paid
  exact Vale.Grace.Robes.markSeas _ { he with paid:=fun x=>(he.paid x).shrink P.J.hr.le }
    (Y.meter.a kt) (M.pole kt) (P.J.gran.trans (M.roof kt).size) h

-- Gauge covariance at *every* field (no need to omit `FleetS`-exceptional set).
lemma color (h : j ≤ Y.uv k) (x : Orbit (CS j)) (g: Site (More (CS j)) → SU.E) :
    denZ (Χ j) P.U (Qv j) (gird g x) = acts (quantU (tradew _ g)).val (denZ (Χ j) P.U (Qv j) x) := by
    let X:= Xv
    let p:= (X.pull.owns j h)
    let e:= (X.pull.note j h).lot_p le_rfl le_rfl
    let m:= Y.history i k
    have v:InterestX P.W.C _ (X.gram j).J := p.taste ▸ ((P.W.arm ..).sound j)
    have he : (X.gram j).path.Bounds (X.gram j).funds P.K.top.width P.K.top.paths P.V.W.bar := by rw [← p.path,← p.fund]; exact P.V.L.mood _
    let hx := ward_m he e
    have hv:= (m.roof j).paid
    refine Girt.sweep _ hx (Stake.tollX P.V P.W v) (Qv j) P.J.n { hv with paid:=fun x=>(hv.paid x).shrink P.J.hr.le } x g P.W.pearl P.V.note (P.J.gran.trans (m.roof _).size) ?_
    rw [P.kJ]; decide

lemma invariant_read (h : j ≤ Y.uv k) (f : allObs (CS j)) (x:Orbit (CS j))
    (g : Site (More (CS j)) → SU.E) : readLinear f.val (gird g x) (denZ (Χ j) U₀ (Qv j) (gird g x)) = readLinear f.val x (denZ (Χ j) U₀ (Qv j) x) := by
  rw [Y.color i k j h x g]
  let U := quantU (tradew (CS j) g)
  let X:= denZ (Χ j) U₀ (Qv j) x
  let A := acts (f.val x.1) X
  change inner ℂ _ (acts (f.val (gauge g x.1)) (acts U.val X)) = inner ℂ _ A
  rw [((mem_allObs _).mp f.property).2.2 g, ← Fock.swivel]; let hp:=act_unit_inner U (mateK _) A
  have he:= hp; rw [show acts U.val (mateK _)= _ from mastC g] at he; exact he

lemma one_city (g : Site (More (CS j)) → SU.E) : MeasurePreserving (gird g) (city _) (city _) := by exact (Wilson.prior_gauge g).prod (threads g)

theorem true_read (f : allObs (CS j)) (h:(Y.voyage i).kick ≤ k) (p : j ≤ Y.uv k) :
    Integrable (fun x:Orbit (CS j)=>inner ℂ (mateK _) (acts (f.val x.1) (denZ (Χ j) P.U (Qv j) x))) (city _) ∧
    partitionZ (Χ j) P.U (Qv j) ≠ 0 ∧
    Y.texture i k j f = (∫ x:Orbit (CS j),inner ℂ (mateK _) (acts (f.val x.1) (denZ (Χ j) P.U (Qv j) x)) ∂city _) / partitionZ (Χ j) P.U (Qv j) := by
  have hp := Y.each_level i k j h p
  exact ⟨Window.integrable_read (can_read _ _ _ _ hp) f.val ((mem_allObs _).mp f.property).1, hp.valid,by_denominator ..⟩
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
