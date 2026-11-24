import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Donor
import YM.SU5.FiniteGaugeData.LocalLimit.Election.Chosen

/-! Common election below burn. Uniform estimates in participating period even for
sensitive quantities. Uses the Vp929 normalization; adapted from the two-index
contraction estimate `Vp929/Stage/Limsup.run_bound`. -/

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
variable {F0:Scrolls B}
local notation "μx" => hat R.L x
namespace Donor
variable (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0) (H : Service V U W J q h D C Q P N0 delay)
    {c : VolumeRate.Bet (trunkY n b)} (Z : Solved P (Actual T ht W0 f (trunkY n b)) 0 c) (a : Bon J q h D delay (Actual T ht W0 f (trunkY n b)))


local notation "Zp" => Branch.gram P BT c
local notation "Zu" => Branch.chargeLevel P BT c
local notation "ζc" i:max => (Branch.fee P BT i c).re
local notation "Eδ" => Y.gram
local notation "AC" i:max => (((Eδ i).F,(Eδ i).K) : Corr (Ω i))
local notation "t" => strip

include Y
private lemma donor_tilt (i:ℕ)(hp:i ≤ trunkY n b) : (Y.gram i).beta-B0 i=∑ j∈range i,Y.tilt j := by
  induction i with
  | zero => rw [sum_range_zero,Y.pull.color]; simp
  | succ j ih => rw [sum_range_succ,←ih (le_of_lt hp),←Y.pull.shift _ hp]; ring
omit Y
include Z
private lemma cap_tilt (i:ℕ)(hp:i ≤ trunkY n b) : ((Zp) i).beta-((B').pilot x i)=∑ j∈range i, ζc j := by
  let U:= Actual T ht W0 f kT
  have hv := congrFun Z.fixp.symm (⟨i,by omega⟩:Fin (kT+1))
  change (c.read i).re - _= _; rw [VolumeRate.Bet.read_of_le c hp,hv]
  dsimp only [VolumeRate.updateBet]; rw [Complex.add_re,Complex.add_re,Complex.ofReal_re,Complex.ofReal_zero,Complex.zero_re,add_zero,add_comm, add_sub_cancel_right,Complex.re_sum]

omit Z
include a
private lemma means (i:ℕ) : (∑ j∈range i, D (μx j)) ≤ (t (μx i)) * (1/400) := by
      let T (j:ℕ) := t (μx j)
      have p(j) : 0 < T j := strip_pos (a.clocks j).grade
      apply le_trans _ (mul_le_mul_of_nonneg_left (prices_sum a.prices i) (p i).le)
      rw [mul_sum]; refine sum_le_sum fun j h=>?_; set y:= D (μx j); have hY:0 ≤ y:=(a.clocks j).bank; let b:=T (j+1); have hx':0<b:=p _
      change y ≤ T i*(y/b); rw [←mul_div_assoc]; exact (le_div_iff₀ hx').2 (le_trans (mul_le_mul_of_nonneg_left ((a.clocks _).increase _ (hat_mono (mem_range.mp h))) hY) (le_of_eq (mul_comm ..)))

include H Z Y
lemma cooldown (r : ℕ) (i : ℕ) (hk : i+r < buoy n) : Cost (T.a i) h (Yb i * decline r) ((Zu i) - AC i) ∧
       |(Zp i).beta - (Y.gram i).beta| ≤ strip (hat R.L x i)*decline r := by
  have hv := deeper n b
  induction r generalizing i with
  | zero =>
    have hi : i<kS := hk
    have h:= a.charged H Z.toRealQ i (hi.trans hv).le; have he:= Y.cool.charged i hi
    constructor
    · exact (h.toCost.sub he.toCost).mono (by simp only [decline,pow_zero,mul_one]; linarith [(a.clocks i).leaf])
    have hx:= Z.paid i (Nat.zero_le _) (hi.trans hv).le
    rw [← Z.toRealQ.coeRe i (hi.trans hv).le,←Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hx
    let u:= B0 i
    have he : |(Zp i).beta-B0 i| ≤ strip (μx i) := by rw [pilot_eq ht Y.due f W0 i (hi.trans hv).le]; exact hx.trans_eq (one_mul _)
    have hy : |(Y.gram i).beta-B0 i| ≤ strip (μx i) * (1/400) := by
      rw [donor_tilt ht Y i (hi.trans hv).le]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum fun j p=>?_).trans (means ht a _)); let hp: j<kS:=(mem_range.mp p).trans hi; exact (Y.pull.price j (hp.trans hv)).trans_eq (if_pos hp)
    have hq:= abs_sub_le (Zp i).beta u (Y.gram i).beta; rw [abs_sub_comm u (Y.gram i).beta] at hq
    -- simp only [decline,pow_zero,mul_one]
    simp only [decline,pow_zero,mul_one]; unfold u at hq; linarith [strip_pos (a.clocks i).grade]
  | succ r ih=>
    have η:0≤decline r:=by unfold decline; positivity
    have stars (j) (u : j+1+r < kS) : Cost (T.a j) h (Yb j * ((decline r+decline r)/4)) (Zu j-AC j) ∧
         |ζc j-(Y.tilt j)| ≤ 100* D (μx j)*(decline r+decline r) := by
      have hu: j+1 < kS := by omega
      have hv: j< kT := by omega
      let Op:= Branch.op P BT j
      obtain ⟨hf,hY⟩:= ih (j+1) u
      obtain ⟨p,p',s,hx⟩:= Y.cool.related j (by omega)
      rw [a.corr_successor H Z.toRealQ j hv, (show AC j= Op.realArr _ _ from s), ←a.fee_eq H Z.toRealQ j hv, p,Complex.ofReal_re]
      refine (a.certified H j hv).stars _ _ _ _ _ _ ?_ η η (hat_step j ▸ hf) (hat_step j ▸ hY)
      rintro u ht; obtain rfl|ht:= ht
      · exact ⟨hat_step j ▸ (a.beta_ok H Z.toRealQ _ hv).1, hat_step j ▸ a.charged H Z.toRealQ _ hv⟩
      rw [Set.mem_singleton_iff] at ht; subst u
      exact ⟨hat_step j ▸ Y.cool.enters _ hu.le, hat_step j ▸ Y.cool.charged _ hu⟩
    constructor
    · exact (stars i (by omega)).1.mono (by unfold decline; rw [pow_succ]; exact le_of_eq (by ring))
    have hi : i ≤ kT := by omega
    have he: (Zp i).beta-(Y.gram i).beta = ∑ j∈range i, (ζc j-Y.tilt j) := by
      rw [Finset.sum_sub_distrib,←donor_tilt ht Y i hi, ←cap_tilt ht Z i hi,pilot_eq ht Y.due f W0 i hi]; ring
    rw [he]; refine (Finset.abs_sum_le_sum_abs ..).trans <| le_trans (sum_le_sum fun j p=> (stars j (by have hx:= mem_range.mp p; omega)).2) ?_
    rw [←sum_mul,←mul_sum]; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (means ht a _) (by norm_num : (0:ℝ)≤100)) (add_nonneg η η)) (le_of_eq ?_); unfold decline; rw [pow_succ]; ring

end Donor
end LocalLimit
end YM.CF.Py.Rate
