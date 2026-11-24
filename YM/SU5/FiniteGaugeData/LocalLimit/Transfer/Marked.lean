import YM.CF.Vp929.EveryLevel

/-!
# Use normalizations on exactly one law with marked reads

Work even on the enlarged measurable mark space including dependence on the tags.
This does *not* assert reflection positivity. `moment` uses the same upper-spin
bra as the rates in this project. No new weight or change of measure.
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

open Window
variable {s : Side} {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
    {d : ℝ} {m B : Side} (U : Grasp V.U B d)
    {a b ε : ℝ}
namespace Marks

abbrev Tagged (s : Side) := Orbit s → FC (Single s)
local notation "Ms" => Tagged s
local notation "Ω" => mid m B

def read (F : Tagged s) (x : Orbit s) : Phys s→L[ℂ]ℂ :=
  (innerSL ℂ (mateK s)).comp (acts (F x))

def evaluate (Y : Orbit s → Phys s) (F : Tagged s) : ℂ :=
  ∫ x, read F x (Y x) ∂city s

variable (Y : GramM (mid m B)) (Z : Scree.Loom (mid m B)) -- Loom conflict?

def ratio (F : Tagged Ω) := evaluate (denZ Y U Z) F / partitionZ Y U Z

variable (F : Tagged s) (F' : Tagged (mid m B))

lemma identify (F : Window.Evaluation (mid m B)) : ratio V U Y Z (fun x=> F x.1) = finiteForm V.U U Y Z F := (by_denominator ..).symm

lemma lift_eq_evaluate (Y : Orbit s→ Phys s) (F : Window.Evaluation s) : evaluate Y (fun x=> F x.1) = Window.moment Y F := rfl

scoped instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I) := borel _
scoped instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I) := ⟨rfl⟩
lemma lift_meas (F : Evaluation s) (h : Measurable F) : Measurable (fun x:Orbit s => F x.1) := h.comp measurable_fst

lemma lift_env (F : Evaluation s) (h : RG.Envelope F) : RG.Envelope (fun x:Orbit s=> F x.1) :=
  ⟨lift_meas F h.meas, h.cost.choose,fun _=> h.cost.choose_spec _⟩

variable {Q P : Orbit s → Phys s} (Hq : Integrable Q (city s))

lemma read_within (x : Orbit s) (c : Phys s) : ‖read F x c‖ ≤ ‖F x‖ * ‖c‖ := by
  refine (norm_inner_le_norm (mateK _) (acts (F x) c) (𝕜:=ℂ)).trans ?_
  rw [(Dial.tickB _).2,one_mul]; simpa only [acts,Matrix.l2_opNorm_toEuclideanCLM] using (ContinuousLinearMap.le_opNorm (acts (F x)) c)

include Hq in
lemma read_int (h : RG.Envelope F) : Integrable (fun x=>read F x (Q x)) (city s) := by
  obtain ⟨c,hc⟩:=h.cost
  have hx : Continuous (fun i:FC (Single s) × Phys s=> inner ℂ (mateK s) (acts i.1 i.2)) := continuous_const.inner ((acts_cont.comp continuous_fst).clm_apply continuous_snd)
  change Integrable (fun i=> inner ℂ (mateK s) (acts (F i) (Q i))) _
  refine Integrable.mono' (Hq.norm.const_mul c) ?_ (Eventually.of_forall fun i=> (read_within F i (Q i)).trans (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg (Q i))))
  let K := fun i:FC (Single s) × Phys s=> inner ℂ (mateK s) (acts i.1 i.2)
  change AEStronglyMeasurable (K ∘ fun x=> (F x,Q x)) (city s)
  have H : AEStronglyMeasurable F (city s) := h.meas.aestronglyMeasurable
  exact Continuous.comp_aestronglyMeasurable (g:=K) hx (H.prodMk Hq.aestronglyMeasurable)

lemma action_price (h : ∀ i, ‖F i‖ ≤ b) (hp : ∀ i, ‖Q i‖ ≤ ε) : ‖evaluate Q F‖ ≤ b * ε := by
  unfold evaluate
  have he: 0≤b := le_trans (norm_nonneg _) (h (1, Classical.arbitrary _))
  exact (norm_integral_le_of_norm_le (integrable_const (b*ε)) (Eventually.of_forall (α:=Orbit s) fun i=>
    (read_within _ i _).trans (mul_le_mul (h _) (hp _) (norm_nonneg _) he))).trans_eq (by rw [integral_const, probReal_univ, one_smul])

include Hq in
lemma read_charge (h : RG.Envelope F) (Hp : Integrable P (city s)) (hb : ∀ i, ‖F i‖ ≤ b) (he : ∀ i, ‖Q i-P i‖ ≤ ε) : ‖evaluate Q F-evaluate P F‖ ≤ b * ε := by
  have hP : evaluate Q F - evaluate P F = evaluate (fun i=> Q i-P i) F := by
    unfold evaluate; simp_rw [map_sub]; rw [←integral_sub (read_int F Hq h) (read_int F Hp h)]
  rw [hP]; exact action_price F hb he

lemma scale_ket (x : ℂ) : evaluate (fun i=> x • Q i) F=x*evaluate Q F := by
  unfold evaluate; simp_rw [map_smul]; exact integral_const_mul ..

lemma one (e:partitionZ Y U Z ≠ 0) : ratio V U Y Z 1=1 := by
  rw [ratio, show evaluate (denZ Y U Z) 1 = _ from lift_eq_evaluate (denZ Y U Z) (1:Evaluation Ω), read_beam]; exact div_self e
lemma quantum (Q : Orbit s → Phys s) : evaluate Q 1 = ∫ x, beamZ s (Q x) ∂city s := read_beam Q

local notation "wZ" => ratioField V Y Z U
variable (p : FullBill.Priced V Y U Z a b)

lemma normalized : ratio V U Y Z F'= evaluate (ratioField V Y Z U) F' := by unfold ratio ratioField; rw [scale_ket,div_eq_mul_inv,mul_comm]

include p
lemma can_read : Integrable (denZ Y U Z) (city Ω) :=
    Integrable.of_bound p.permits.meas.aestronglyMeasurable p.permits.cost.choose (Eventually.of_forall p.permits.cost.choose_spec)
include p
lemma can_evaluate : Integrable wZ (city Ω) := (can_read V U Y Z p).smul (partitionZ Y U Z)⁻¹
lemma upper (hp : ∀ i,‖F' i‖ ≤ ε) : ‖ratio V U Y Z F'‖ ≤ ε * Real.exp (b*sites (mid m B)) := by
  rw [normalized]; exact action_price F' hp p.rate
end Marks
end LocalLimit
end YM.CF.Py.Rate
