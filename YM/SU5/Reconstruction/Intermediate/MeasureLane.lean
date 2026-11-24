import YM.SU5.Reconstruction.Intermediate.Furnish
import YM.SU5.Reconstruction.Intermediate.Tuition
import YM.SU5.Reconstruction.Intermediate.ThermalEstimates
/-! Now returns the spent PRICE at any of these high consultations. Adapts LocalLimit/Transfer/Horizontal,Prices,Bridge. Need not equate upper offset with a history - uses true Hart price. -/
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
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {x delay : ℝ} {C R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
    (A : Branch W m k x N0)
local notation "Ω" => cell m B R.L
local notation "Xc" => A.T.a
local notation "Xh" => hat R.L x
local notation "Xs" => A.last.Q
local notation "Xr" => A.loom
local notation "X₀" => A.toSpine.address
local notation "Yb" i => dleaf R.L (hat R.L x i)
local notation "Xm" => A.last.move
namespace Intermediate
variable (s:ℕ) {D:ℝ→ℝ} {h:ℝ} (F:Room s→ Corr (cell m B R.L s))
variable (u:Room s) (H : Service V U W J q h D C R0 P N0 delay) (pP:ResponsiveService J q N0 h delay P) (a:Bon J q h D delay A) (hh:1≤h)(τ:s ≤ k)(pS:Qualified A s D h F)
variable (r:Settles P A s D F u)
local notation "Z" => cooled P A s D F
local notation "X" i:max => (Z).guess i u
local notation "β" => temper A s D
open VolumeRate Donor Window Graph.Diff Graph.Angle FullBill
variable (b : Bet k) (t : Solved P A 0 b) (n:ℕ) (hv:buoy n≤ s)
local notation "Y" i:max => A.gram P b i
local notation "Dk" i:max => dleaf R.L (Xh i)
local notation "C₁" i:max => A.chargeLevel P b i
local notation "C₂" i:max => (Z).G i u
include H pP a hh τ pS r t
lemma compare_here (i r':ℕ) (hi:i+r'<s) (y':Orbit (cell m B R.L i)) :
    ‖field U (Y i) (Xr i) y'-field U (X i) (Xr i) y'‖ ≤ 2*(shapeMass A.T i * decline r' * game m)*Real.exp (volumePrice A.T i * game m) := by
  have p:i<s:=by omega
  have hi':i ≤ k := p.le.trans τ
  obtain ⟨w,t'⟩ := same_shelf P A s F u H pP a hh τ pS r b t _ _ hi
  let y:= (cooled P A s D F).G i u; have he:= (Intermediate.earns P A s a F H pP τ hh pS i p).1.cost u
  have hp:= a.clocks i; have hβ:= matched_of_enters hp (a.beta_ok H t.toRealQ i hi').2
  have hT: 0 ≤ (Y i).beta ∧ (Y i).beta ≤ 2*Xh i:= ⟨by have e:Xh i/2≤ (Y i).beta:= hβ.1; linarith [hp.grade],hβ.2⟩
  obtain ⟨f,g⟩:= boundedOf A s u a τ p.le
  rw [←price_formula (T:=A.T), ←pace_shape]
  let W':= (a.can.cape i).paid
  exact transfer_record (a.charged H t.toRealQ i hi').toCost he.toCost w t' hh (div_nonneg hp.leaf.le (by norm_num)) (mul_nonneg hp.leaf.le (show 0 ≤ decline r' by unfold decline; positivity)) (A.last.sound i) { W' with paid:=fun i=>(W'.paid i).shrink J.hr.le } (J.gran.trans (a.can.cape i).size) hT.1 f hT.2 g y'
lemma long_offset (i:ℕ) (p:i< buoy n)(hs:buoy n ≤ s)(y: Orbit (cell m B R.L i)) :
    ‖field U (Y i) (Xr i) y-field U (X i) (Xr i) y‖ ≤ outage A.T i n m := by
  let j:=buoy n -(i+1); have hx:j+(i+1)=buoy n:= Nat.sub_add_cancel p; let f:=game m
  have hf:0 ≤ f:=by unfold f game; positivity
  have ht':0 ≤ horizontalPrice A.T i:=by unfold horizontalPrice; positivity
  refine (compare_here P A s F u H pP a hh τ pS r b t i j (by omega) y).trans ?_
  rw [decline_decay j (i+1),hx]; let z:= decay n (Real.log 2); let e:=Real.exp (volumePrice A.T i*f); let φ:=shapeMass A.T i
  have hg:0 ≤ z:= (decay_pos ..).le; have he:0 ≤ e:=(Real.exp_pos _).le
  unfold outage; rw [add_mul,one_mul,Real.exp_add]; change 2*(φ * (2^(_+_)* z)*f)*e ≤ horizontalPrice A.T i * z * (e * Real.exp f)
  calc
    _ ≤ 2*(|φ| * (2^(i+2)*z)*f)*e := by gcongr; exact le_abs_self φ
    _ = (horizontalPrice A.T i*z *e)*f := by unfold horizontalPrice φ; ring
    _ ≤ (horizontalPrice A.T i*z *e)* Real.exp f:= (mul_le_mul_of_nonneg_left (show f≤Real.exp f by linarith [Real.add_one_le_exp f]) (by positivity))
    _ = _:=by ring
omit r t
lemma kettle (i:ℕ) (p:i<s): ∀ y, ‖field U (X i) (A.loom i) y‖ ≤ Real.exp (serviceCost A.T i * sites (cell m B R.L i)):= by
 let hZ:= (Intermediate.earns P A s a F H pP τ hh pS i p).1.cost u
 let hv:= (a.can.cape i).paid; obtain ⟨u,v⟩:= boundedOf A s u a τ p.le -- shadow u
 exact extensive W (A.last.sound i) {hv with paid:=fun i=>(hv.paid i).shrink J.hr.le} _ (J.gran.trans (a.can.cape i).size) hh _ _ (hZ.toCost.lot _ _) u v
section
variable {v:ℝ}
include r t hv
noncomputable def MarkedUp (i:ℕ)(v:ℝ) : Prop:= Priced V (staff P A s D F u i) U (A.loom i) (thermalCost C R x v i) (thermalCost C R x v i+|serviceCost A.T i|) ∧ ∀ y,‖ratioField V (Branch.gram P A b i) (Xr i) U y-ratioField V (X i) (Xr i) U y‖≤ Donor.divisionBill A.T C v i n m -- parse bar
variable (i:ℕ)
lemma price_of (p:i < buoy n)(hq: Priced V (Y i) U (A.loom i) (expense C R x v i) (expense C R x v i+|serviceCost A.T i|))
  (he: outage A.T i n m ≤ Real.exp (-expense C R x v i*sites (cell m B R.L i))/2) : MarkedUp (C:=C) (D:=D) P A s F u b n i v :=by
 have H':= long_offset P A s F u H pP a hh τ pS r b t n i p hv; let Q:= X i
 have hZ: Priced V Q U (A.loom i) (thermalCost C R x v i) (thermalCost C R x v i+|serviceCost A.T i|) :=
      compare_price V hq (envelope_ready P A s F u H pP a hh τ pS (lt_of_lt_of_le p hv).le) H' (kettle P A s F u H pP a hh τ pS i (lt_of_lt_of_le p hv)) he
 exact ⟨hZ, strip_difference V hq hZ H'⟩
end
end Intermediate
end LocalLimit
end YM.CF.Py.Rate
