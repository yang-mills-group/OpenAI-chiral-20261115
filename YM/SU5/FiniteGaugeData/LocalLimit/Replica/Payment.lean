import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Budget
import YM.SU5.FiniteGaugeData.LocalLimit.Replica.Stroll

/-! # Volume-independent Sup estimate for scalar gauge observations.

Application on the FiniteGaugeData Course and the *sharp* measurement `texture`, by
horizontal transfer paid on the level. Displacement is of the support; observe
columns and ordered product anywhere. Probe spec below is constant on tags.
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
open Window SquareScalar
open FullBill
namespace Donor
open Mir Reflect Spark
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x : ℝ} {C D Q : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {F0:Scrolls B} (Y:Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0)
local notation "Xj" => Vale.mesh m R.L
local notation "kT" => trunkY n b
variable {A r v:ℝ} (hp:∀ m,ScaleK A r (F0 m)) (hw:Budget B d v)
local notation "ξ" => cell m B R.L
local notation "Φ…" => probe ht Y
-- moved evaluations use displacements by `2*B`
include hp hw ht
variable {v₀ v₁:ℝ}(d':ℕ)(hd:2*B.val∣d')(p:0<d') (j:ℕ)(h₀:j ≤ trunkY n b)(Hf:Priced V (Y.gram j) U (W0 j) v₀ v₁)
include h₀ Hf
lemma frame_bill : FrameBill R (mesh m R.L j) B (Y.probe ht j) :=
  ⟨Window.reads_mass V.U U _ _ Hf.valid,fun x X=> Y.stroll ht hp hw j h₀ x X,fun s X u=> Y.PSD_buffered ht hp hw s j h₀ Hf.valid X u⟩

-- useful displacement on this probe syntax. No meaning of torus projection
-- of support views on other volumes yet; prove in common-local test section.
variable (w:ℝ)(F: Pane (cell m B R.L j)→ℂ)(y: Cover)
include hd p
omit hp hw h₀ Hf hd p ht
lemma tag_width {N:Side} (F:Pane N→ℂ)(w:ℝ)(h:∀ x, ‖F x‖ ≤ w)(x:Orbit N): ‖bosonic N F x.1‖ ≤ w:=by unfold bosonic; rw [norm_smul,norm_one,mul_one]; exact h _
include hp hw h₀ Hf hd p ht
lemma sup_bill (h:boxed R d' 0 w F)(e:d' ≤ (cell m B R.L j).val) :
    ‖Φ… j (bosonic _ (F ∘ traceOfWalk B _ y))‖ ≤ w*mural d' v₁ := by
 rw [stroll ht Y hp hw j h₀ y F ⟨h.localB.borel,h.localB.cost⟩]; apply quiltCharge d' (Y.probe ht j) (Y.frame_bill ht hp hw j h₀ Hf) F h hd p e v₁; intro F w k s
 unfold probe
 rw [←Marks.identify]; exact Marks.upper V U (Y.gram j) (W0 j) _ Hf (tag_width F w s)
end Donor
namespace Preparation
open Marks Donor
variable {P: Preparation}{F : (s:Side)→ Scree.Loom s→Prop} (Y:Course P F)
namespace Course
local notation "Ξ" i:max => Y.voyage i
local notation "Gₛ" i:max k:max h:max => (Ξ i).Q k h
local notation "Xj" i:max j:max => cell (Y.ir i) P.block P.R.L j
local notation "γF" i:max j:max => Pane (Xj i j)
local notation "G₀" i:max k:max => (Ξ i).X (Y.uv k)
local notation "Xm" i:max j:max => (Ξ i).CapeT j
abbrev thermal (j:ℕ) := thermalCost P.C P.R P.x Y.τ j+|serviceCost Y.meter j|
variable (j:ℕ)
/-- Applies to existing probes on *any* such buffered translated box; contains
arbitrarily large fixed boxes despite the allocated buffer constant.
Uses the **actual** main system. Its cutoff threshold includes the transfer
and chooses denominators both sides; no dependence here on size of these boxes.
-/
theorem gauge_bill : ∀ᶠ k in atTop, j < buoy (Y.ivory k) ∧ ∀ i, ∀ _p:(Y.voyage i).kick ≤ k, ∀ d:ℕ, 2*P.block.val∣d → 0<d → d ≤ (Xj i j).val → ∀ (w:ℝ) (A:Pane (Xj i j)→ℂ) (_q:boxed P.R d 0 w A) (x:Cover),
    ‖Y.texture i k j (bosonic (Xj i j) (A ∘ traceOfWalk P.block _ x))‖ ≤ (1+mural d (Y.thermal j))*w := by
 filter_upwards [Y.heatGap j,Y.thaw j 1 one_pos] with k v a; refine ⟨v.1,?_⟩; intro i s d p l u w B h x; let K:= Gₛ i k s; let t:= v.2 i s
 let X:= (bosonic (Xj i j) (B ∘ traceOfWalk P.block _ x)); let Q(z:Orbit (Xj i j)):= X z.1
 have hx : ‖Donor.probe _ K j X‖ ≤ w*mural d (Y.thermal j):=sup_bill _ _ P.scale P.budget d p l j (v.1.trans (deeper ..)).le t.priceH w B x h u
 have he:Measurable X := (show Continuous (fun v:ℂ=>v • (1: FC (Single (cell (Y.ir i) P.block P.R.L j)))) from continuous_id.smul continuous_const).measurable.comp (h.localB.borel.comp (continuous_pull ..).measurable)
 have ht: ‖Y.texture i k j X - Donor.probe _ K j X‖ ≤ 1*w := by
    change ‖finiteForm P.V.U P.U _ _ X-finiteForm P.V.U P.U _ _ X‖ ≤ _; rw [←identify,←identify]; exact a i s Q w (Marks.lift_meas X he) (Donor.tag_width _ _ (fun k'=>h.costs _))
 change ‖Y.texture i k j X‖ ≤ _
 linarith [norm_sub_norm_le (Y.texture i k j X) (Donor.probe _ K j X)]
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
