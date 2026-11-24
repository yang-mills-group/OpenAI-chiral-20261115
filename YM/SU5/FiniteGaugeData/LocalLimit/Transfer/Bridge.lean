import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Divide
import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Prices

/-!
# The bridge for the actual-first normalization route

This version yields uniform price loss *on the cone* from real horizontal rates.
Apply it after each-period elections at the common pivot; it does not extend
CapP pricing to unsampled periods or cutoffs.
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

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x
open FullBill Marks
namespace Donor
variable (H : Service V U W J q h D C Q P N0 delay) (hh : 1 ≤ h) {τ ε : ℝ}
    {ρ : ℕ → ℝ} {F0 : Scrolls B}
local notation "pβ" i:max => expense C R x τ i
local notation "Ds" i:max => (expense C R x τ i + |serviceCost T i|)
local notation "Ψ" i:max => (expense C R x τ i + 1 + |serviceCost T i|)
local notation "Ξ" i:max => sites (cell m B R.L i)
local notation "ZT" => (Real.log 2)


-- Estimates uniform over ALL solutions meeting the cited conditions, in these periods.
def thermalCost (C:ℝ→ℝ)(R:Patch)(x τ:ℝ) (i:ℕ) := expense C R x τ i+1

def outage (T : Month x 1 6 2 N0 V W)(i:ℕ)(n:ℕ)(m:Side) :=
  horizontalPrice T i * decay n (Real.log 2) * Real.exp ((volumePrice T i+1)*game m)

private lemma half_room (i b:ℕ) : ∀ᶠ n in atTop, ∀ m:Side,
    cone b n m → outage T i n m ≤ Real.exp (-expense C R x τ i*sites (cell m B R.L i))/2 := by
  let A:=expense C R x τ i
  let V':= volumePrice T i + 1; let v:= A*postage B R.L i
  filter_upwards [collapse b (Real.log_pos (by norm_num : (1:ℝ)<2)) (by norm_num:(0:ℝ)<1/2) (horizontalPrice T i) (V'+v)] with n h m p
  specialize h m p
  unfold outage; rw [sites_postage, ←mul_assoc,neg_mul,neg_mul,Real.exp_neg]; -- typo -neg_mul
  rw [add_mul, Real.exp_add,←mul_assoc] at h
  have he:= (le_div_iff₀ (Real.exp_pos _)).2 h
  apply he.trans_eq
  unfold v A; field_simp

include H hh
lemma stationed (i b:ℕ)(p:0≤τ) : ∀ᶠ n in atTop, i < buoy n ∧ ∀ m:Side, ∀ (ht:T.q ≤ m.val)
    (W0:Cape m B R.L) (ρ:ℕ→ℝ) (B0 f:ℕ→ℝ) (F: Scrolls B) (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F)
    (X:Parcel J q h D C Q T ht W0 ρ f (trunk b n)), FromShot P delay X →
    Real.exp (-τ*sites (cell m B R.L 0)) ≤ ‖compensated U (X.gram 0) (W0 0)‖ → cone b n m →
    Priced V (Y.gram i) U (W0 i) (expense C R x τ i+1) (expense C R x τ i+1+|serviceCost T i|):= by
  filter_upwards [half_room (T:=T) (C:=C) (τ:=τ) i b, profound i] with n p₀ he -- include issue
  refine ⟨he,fun m ht W0 ρ B0 f F Y X hX g v=> ?_⟩
  have hx := (hX.paid.prices x le_rfl).grade
  -- bound divisor here
  have hp := cap_price ht H hh X hX p g (he.trans (deeper n b)).le
  obtain ⟨hY,w⟩:= permits_chill ht hh Y he hx
  exact compare_price V hp hY (horizontal ht H Y hh i he X hX) w (p₀ m v)

def divisionBill (T : Month x 1 6 2 N0 V W) (C:ℝ→ℝ)(τ:ℝ) (i n:ℕ)(m:Side) :=
    (1+Real.exp ((expense C R x τ i + |serviceCost T i|)* sites (cell m B R.L i))) * outage T i n m * Real.exp (thermalCost C R x τ i * sites (cell m B R.L i))
variable {i : ℕ}
omit H hh
lemma shrinks (i:ℕ) (b:ℕ) (he:0 < ε) : ∀ᶠ n in atTop, ∀ m:Side,
    cone b n m → divisionBill T C τ i n m ≤ ε := by
  let Vq:= volumePrice T i+1; let t:= thermalCost C R x τ i*postage B R.L i; let v:= Ds i * postage B R.L i
  have p := collapse b (c:=Real.log 2) (Real.log_pos (by norm_num)) (half_pos he) (horizontalPrice T i)
  filter_upwards [p (Vq+t),p ((Vq+t)+v)] with n h0 h1 m u
  specialize h0 m u; specialize h1 m u
  let x:= horizontalPrice T i * decay n (Real.log 2); let M:=game m; let V':= Real.exp (Vq*M); let T':= Real.exp (t*M); let C':= Real.exp (v*M)
  have hT : x*(V'*T') ≤ ε/2 := by rw [add_mul,Real.exp_add] at h0; exact h0
  have hC : x*(V'*T'*C') ≤ ε/2 := by simp only [add_mul,Real.exp_add] at h1; exact h1
  change (1 + Real.exp ((Ds i) *_)) * (x*V') * Real.exp (thermalCost C R _ τ i * _) ≤ _; rw [sites_postage,←mul_assoc (thermalCost ..),←mul_assoc (Ds i)]
  change (1 + C') * (x * V') * T' ≤ _
  linarith only [hT,hC]

local notation "ηφ" i:max => outage T i n m
local notation "Ψε" i:max => divisionBill T C τ i n m

/-- The transfer at stated prices at a given cutoff and fixed period.
No claim that such prices are uniformly attainable in cutoff across
periods; need the actual lower bound on `Priced` branch. -/
structure Gap (T:Month x 1 6 2 N0 V W) (ht:T.q ≤ m.val) (C D Q:ℝ→ℝ) (τ:ℝ)
    (X : Parcel J q h D C Q T ht W0 ρ f (trunk b n))
    (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0) (i:ℕ) : Prop where
  priceA : Priced V (X.gram i) U (W0 i) (expense C R x τ i) (expense C R x τ i+|serviceCost T i|)
  priceH : Priced V (Y.gram i) U (W0 i) (thermalCost C R x τ i) (thermalCost C R x τ i+|serviceCost T i|)
  compare_density : ∀ y,‖field U (X.gram i) (W0 i) y-field U (Y.gram i) (W0 i) y‖ ≤ outage T i n m
  ratio_transfer : ∀ y, ‖ratioField V (X.gram i) (W0 i) U y-ratioField V (Y.gram i) (W0 i) U y‖ ≤ divisionBill T C τ i n m

include H hh
lemma charged_transfer (X : Parcel J q h D C Q T ht W0 ρ f (trunk b n)) (pX : FromShot P delay X)
    (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0) (hi:i < buoy n)
    (hx : Priced V (X.gram i) U (W0 i) (pβ i) (Ds i))
    (hy : Priced V (Y.gram i) U (W0 i) (pβ i+1) (pβ i+1+|serviceCost T i|)) : Gap T ht C D Q τ X Y i := by
  let δ:= horizontal ht H Y hh i hi X pX
  exact ⟨hx,hy,δ, strip_difference V hx hy δ⟩

omit ht
lemma paired (i b:ℕ) (p:0≤τ) : ∀ᶠ n in atTop, i < buoy n ∧ ∀ m:Side, ∀ (ht:T.q ≤ m.val)
    (W0:Cape m B R.L) (ρ:ℕ→ℝ) (B0 f:ℕ→ℝ) (F: Scrolls B) (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F)
    (X:Parcel J q h D C Q T ht W0 ρ f (trunk b n)), FromShot P delay X →
    Real.exp (-τ*sites (cell m B R.L 0)) ≤ ‖compensated U (X.gram 0) (W0 0)‖ → cone b n m → Gap T ht C D Q τ X Y i := by
  filter_upwards [stationed (T:=T) H hh i b p] with n t
  exact ⟨t.1,fun m g w ρ B0 f F Y X hX pX q=> charged_transfer g H hh X hX Y t.1 (cap_price g H hh X hX p pX (t.1.trans (deeper ..)).le) (t.2 m g _ _ _ _ _ Y X hX pX q)⟩

omit H hh
include ht
lemma Gap.mark_bound {X : Parcel J q h D C Q T ht W0 ρ f (trunk b n)}
    {Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0} (g : Gap T ht C D Q τ X Y i)
    (F : Tagged (cell m B R.L i)) (u:Measurable F)(e: ∀ y, ‖F y‖ ≤ ε) :
   Integrable (fun y=> read F y (denZ (X.gram i) U (W0 i) y)) (city _) ∧
   Integrable (fun y=> read F y (denZ (Y.gram i) U (W0 i) y)) (city _) ∧
   ‖Marks.ratio V U (X.gram i) (W0 i) F-Marks.ratio V U (Y.gram i) (W0 i) F‖ ≤ ε*divisionBill T C τ i n m := by
  let h : Envelope F := ⟨u, ε,e⟩
  rw [Marks.normalized, Marks.normalized]
  refine ⟨Marks.read_int _ (can_read _ _ _ _ g.priceA) h, Marks.read_int _ (can_read _ _ _ _ g.priceH) h,?_⟩
  exact Marks.read_charge _ (can_evaluate _ _ _ _ g.priceA) h (can_evaluate _ _ _ _ g.priceH) e g.ratio_transfer
end Donor
end LocalLimit
end YM.CF.Py.Rate
