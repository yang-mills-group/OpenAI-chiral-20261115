import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Marked

/-!
# Pricing with the unsquared, complex FiniteGaugeData denominator
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

open Marks FullBill
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} (V : Grace K R L)
    {d : ℝ} {m B N : Side} {U : Grasp V.U B d}
    {a b c d' e v ε : ℝ} {LQ : Scree.Loom (mid m B)} -- Scree qualify
    {Q Q' : GramM (mid m B)}
local notation "Ω" => mid m B
local notation "W" => field U Q LQ
local notation "W'" => field U Q' LQ
local notation "A" => compensated U Q LQ
local notation "At" => compensated U Q' LQ
local notation "nK" => sites (mid m B)
local notation "vZ" => ratioField V Q LQ U
local notation "vY" => ratioField V Q' LQ U

lemma exp_half_extra (c:ℝ) (h:1 ≤ a) :
    Real.exp (-(c+1)*a) ≤ Real.exp (-c*a)/2 := by
  rw [show -(c+1)*a= -c*a + -a by ring, Real.exp_add, Real.exp_neg, ←div_eq_mul_inv]
  exact (div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) (le_trans (by linarith) (Real.add_one_le_exp a)))

variable (p : Priced V Q U LQ a b)
include V p
lemma vacuum_compare (hQ:Envelope (denZ Q' U LQ)) (hh:∀ i, ‖field U Q LQ i-field U Q' LQ i‖ ≤ ε) : ‖A - At‖ ≤ ε := by
  have he : Integrable (field U Q LQ) (city Ω) := (Marks.can_read V U Q LQ p |>.smul (Complex.exp (-Q.v))) -- metavars
  have huv : Integrable (denZ Q' U LQ) (city Ω) :=
    Integrable.of_bound hQ.meas.aestronglyMeasurable hQ.cost.choose (Eventually.of_forall hQ.cost.choose_spec)
  have hu : Integrable W' (city Ω) := huv.smul (Complex.exp (-Q'.v))
  let H : Tagged Ω := fun _=> 1
  have ht := Marks.read_charge H he (show Envelope H from by constructor; exact measurable_const; exact ⟨1,fun _=> (norm_one.le)⟩) hu (b:=1) (fun x=>((show ‖H x‖=1 from norm_one).le)) hh
  rw [one_mul] at ht; rw [←integral_beam,←integral_beam]; exact (by rw [← Marks.quantum,← Marks.quantum]; exact ht)

lemma compare_price (hQ:Envelope (denZ Q' U LQ)) (hh:∀ i, ‖field U Q LQ i-field U Q' LQ i‖ ≤ ε)
    (hv: ∀ i,‖field U Q' LQ i‖ ≤ Real.exp (v*nK)) 
    (he : ε ≤ Real.exp (-a*nK) / 2) : Priced V Q' U LQ (a+1) (a+1+|v|) := by
  have hx := p.lower
  refine produced V _ ?_ hQ hv (by linarith [le_abs_self v]); refine (exp_half_extra a (sites_pos _)).trans ?_
  linarith [norm_sub_norm_le A At, vacuum_compare V p hQ hh]

omit p
include V
lemma funded_ratio (j:Orbit Ω) (h:A ≠ 0) : W j = A • vZ j:= by
  have he : partitionZ Q U LQ ≠ 0 := right_ne_zero_of_mul h
  unfold ratioField compensated field; rw [smul_smul,mul_assoc,mul_inv_cancel₀ he,mul_one]

include p
lemma strip_difference (p' : Priced V Q' U LQ c d')
    (he : ∀ x, ‖field U Q LQ x-field U Q' LQ x‖ ≤ ε) (i : Orbit Ω) :
    ‖vZ i-vY i‖ ≤ (1+Real.exp (b *nK)) * ε * Real.exp (c*nK) := by
  have hg:0<‖At‖:=(Real.exp_pos _).trans_le p'.lower
  let A':= compensated U Q' LQ; let x:= ratioField V Q LQ U i; let y:= ratioField V Q' LQ U i
  have hf:A≠0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) p.lower)
  have h: A' • (x-y) = field U Q LQ i - field U Q' LQ i +(A'-A) • x := by rw [funded_ratio V i hf,funded_ratio V i (norm_pos_iff.mp hg), sub_smul, smul_sub]; change _ = _ • x - A' • y + (A' • x - _ • x); abel
  have H:= norm_add_le (field U Q LQ i-field U Q' LQ i) ((A'-A) • x); rw [←h,norm_smul,norm_smul] at H
  let u:= Real.exp (b*nK)
  have hh: ‖At - A‖ ≤ ε := (norm_sub_rev ..).trans_le (vacuum_compare V p p'.permits he)
  have hw : ‖A'‖ * ‖x-y‖ ≤ ε + ε * u := H.trans (add_le_add (he i) (mul_le_mul hh (p.rate _) (norm_nonneg _) ((norm_nonneg _).trans hh)))
  let U:= Real.exp (c*nK); have ht:0<U:=Real.exp_pos _
  have hv: U⁻¹*‖x-y‖ ≤ ε+ ε*u := le_trans (mul_le_mul_of_nonneg_right (show U⁻¹ ≤ ‖A'‖ from by unfold U; rw [←Real.exp_neg, ←neg_mul]; exact p'.lower) (norm_nonneg (x-y))) hw
  exact ((inv_mul_le_iff₀ ht).1 hv).trans_eq (by change _=(1+u)*ε*U; ring)
end LocalLimit
end YM.CF.Py.Rate
