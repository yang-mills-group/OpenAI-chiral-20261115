import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Bridge
/-! Re-expose working estimates, from Transfer/Horizontal,Bridge (proofs copied) -/
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


open Graph.Diff Graph.Angle Window
namespace Intermediate
section trace
variable {F : BudgetPoint} {I : Interest (mid m B)} {A B'c : Corr (mid m B)} {l : ℕ}
    {LQ : Scree.Loom (mid m B)} {c₁ c₂ : ℂ} {δz z₁ z₂ a d₁ b' u : ℝ}
local notation "πF" => construct F (V.L.path l) K.top.clip I
local notation "Cn" => K.top.paths
local notation "ΦA" => πF z₁ A c₁
local notation "ΦB" => πF z₂ B'c c₂
local notation "Λ" => mid m B
local notation "EC" => earnings W F a δz
local notation "Ψ" => Record.paceZ F (mid m B) K.top.clip K.top.paths d₁ b'

private lemma measure_law 
    (T' : Orbit (mid m B)) (hβ : 0≤z₂) (he : z₂≤a) : Graph.past ΦB T'.1 * Real.exp (flagBill (mid m B) δz δz (cashU W.C)) ≤ Real.exp (EC*sites (mid m B)) := by
  let hv:=V.L.mood l
  have hp : - (V.L.path l).inChannels K.top.clip F z₂ T'.1 ≤ taxPart V F a * sites (mid m B) := by
    have ht := Window.energy_low F (V.L.path l) K.top.clip hv hβ T'.1; exact ((neg_le.mp ht).trans (tax_price V (mid m B) he)) -- tune
  rw [Graph.past,←Real.exp_add]; apply Real.exp_monotone
  change -(V.L.path l).inChannels _ _ _ _+_≤ _
  refine (add_le_add_left hp _).trans_eq ?_; rw [flagBill_eq]; unfold earnings sites; change _+_= _ * ((((mid m B).val*2:ℕ):ℝ)^4); push_cast; ring

lemma transfer_record {k : ℕ} (hA : Cost F h δz A) (hB : Cost F h δz B'c)
    (p : Cost F h b' (A-B'c)) (δP : |z₁-z₂| ≤ d₁) (hh:1≤h) (hq:0 ≤ δz) (hp:0 ≤ b')
    (hw : InterestX W.C (mid m B) I) (H : Roof (mid m B) u d k LQ) (hc : U.roundZ ≤ (mid m B).val)
    (hx : 0≤z₁)(hy : 0≤z₂)(h1 : z₁≤a)(h2 : z₂≤a)(T' : Orbit (mid m B)) :
    ‖field U ΦA LQ T' - field U ΦB LQ T'‖ ≤ 2 * Ψ * Real.exp (EC * sites (mid m B)) := by
  have hg:= V.L.mood l; let v:= levelQ W.C; let w:= cashU W.C
  have pT := paths_nonneg V
  let g:= d₁ * jumpTax F (More Λ) K.top.clip Cn; let f:= Graph.Diff.rankV Λ b'
  have hf: 0 ≤ f := by unfold f Graph.Diff.rankV; positivity
  have hG : 0 ≤ g := mul_nonneg ((abs_nonneg _).trans δP)
    ((abs_nonneg _).trans (kinetic_P (T'.1) hg pT))
  let x := Record.paceZ F (mid m B) K.top.clip K.top.paths d₁ b'; let s:= Real.exp (EC* sites (mid m B)); have he: 0<s:=Real.exp_pos _
  have hz : x=2*g+3*f := rfl; have hx0 : 0≤x:=by linarith
  by_cases u:g≤1/2 ∧ f≤1/2; swap
  · have hwx : 1 ≤ x := by push Not at u; by_cases h':g≤1/2; linarith [u h']; linarith
    calc
      _ ≤ s+s := (norm_sub_le ..).trans (add_le_add (extensive W hw H l hc hh _ _ (hA.lot _ _) hx h1 _) (extensive W hw H l hc hh _ _ (hB.lot _ _) hy h2 _))
      _ ≤ _ := by change s+s ≤ 2*x*s; nlinarith
  have p0 := frostQ (X:=ΦA) (hA.lot _ _) (zero_le_one.trans hh) hw
  have p1 := frostQ (X:=ΦB) (hB.lot _ _) (zero_le_one.trans hh) hw
  let Uc:Record.Cart ΦA ΦB h Cn b' d₁ := ⟨rfl,rfl,rfl,rfl,δP,rfl,rfl, ⟨⟨p.inc.weight,fun _ v=> v.elim⟩,⟨p.dark.weight,fun _ v=> v.elim⟩⟩,u.1,u.2⟩
  refine (Record.on_trace ΦA ΦB LQ H hc Uc hg p0 p1 hh hq (cash_v _) (level_p _).le pT T').trans ?_
  refine (mul_le_mul_of_nonneg_right (measure_law (I:=I) T' hy h2) hx0).trans ?_
  change s*x ≤ 2*x*s; nlinarith
end trace
variable (H : Service V U W J q h D C Q P N0 delay) (hh : 1 ≤ h) {τ ε : ℝ}
    {ρ : ℕ → ℝ} {F0 : Scrolls B}
local notation "pβ" i:max => expense C R x τ i
local notation "Ds" i:max => (expense C R x τ i + |serviceCost T i|)
local notation "Ψ" i:max => (expense C R x τ i + 1 + |serviceCost T i|)
local notation "Ξ" i:max => sites (cell m B R.L i)
local notation "ZT" => (Real.log 2)
open Donor
lemma half_room (i b:ℕ) : ∀ᶠ n in atTop, ∀ m:Side,
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
end Intermediate
end LocalLimit
end YM.CF.Py.Rate
