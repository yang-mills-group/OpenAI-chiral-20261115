import Weft.MonthPay
import Weft.Wage
import Knotwise.Epoch
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option quotPrecheck false
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d h x : ℝ}
  {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} (J : Robes N V W) (q : Chi) (h : ℝ) (D C R0 : ℝ→ℝ) {N0 : ℕ} (T : Month x 1 6 2 N0 V W) (ht : T.q ≤ m.val)
  (S : Cape m B R.L) (ρ : ℕ→ℝ) (f : ℕ→ℝ) (k i : ℕ)
namespace Parcel
open Branch
open Pitching Pitching.Focus
variable {J q h D C R0 T S ρ f i}
variable (s:Parcel J q h D C R0 T ht S ρ f k)
variable {delay:ℝ}{P:Prescription R B}(H:Service V U W J q h D C R0 P N0 delay)(t:s.Prepared P delay)
variable (G:Morn K)(Q:Diary)(sk:G.After R)(Lq:ShelfTh G Q R0 D C J q h P N0 delay)
local notation "Yc"=> (hat R.L x i)
local notation "Ar"=> G.armor
local notation "w0"=> ((Actual T ht S f k).toSpine.address i)
local notation "fϕ"=> thinAllot G.Mult R Yc
local notation "fZ"=> (3*dleaf R.L Yc)

open Tune Roots Oath Bake Neon
attribute [-instance] instDecidableEqLex
variable {I:Type}[Fintype I][LinearOrder I]{Aρ qv ε:ℝ}(CA:Καlendar R G.armor qv Aρ G.Mult ε)
local notation "Nc" j:max=> cell m B R.L j
variable (xs:Site (cell m B R.L i)) -- unused
-- ABI
open Compass Dyad Lattice.PlaqAxes AnalyticBridge.VerifiedReset ThinGauge Moto
local notation "xk"=>Yc
local notation "m_"=> thinAllot G.Mult R xk
local notation "rP"=> allotΨ R.L (hat R.L x (i+1))
local notation "rC"=> allotΨ R.L xk
-- φ price allowed cap. 
include H t G sk Lq CA
variable (h0:1≤h)(hm:Real.exp 1 ≤ Aρ)(hu:ThinGauge.Open (G.armor).g0 (G.armor).delta (Ione.duty_Q 6 2) Aρ ((R.L.val:ℝ)⁻¹))(hr:4*(Aρ+1)≤ G.Mult)(vκ:2*Ione.strive_E 6 ≤ (G.cap:ℝ))
include h0 hm hu hr vκ
-- Uniform horizon, any terminal top >= intermediate.Creu.Harmony.
variable (WZ:Q.fits R)
include WZ
omit t
lemma eventualStep:
    ∀ᶠ i:ℕ in atTop,∀ k>i,∀ (m:Side)(hτ:T.q ≤ m.val)(S:Cape m B R.L)(ρ f:ℕ→ℝ)(s:Parcel J q h D C R0 T hτ S ρ f k),s.Prepared P delay→
    let z:= ((Actual T hτ S f k).toSpine.address i)
    KnollStep V U J.d h (s.gram i) (s.gram (i+1)) (Location.step V z) z.G (S i) (S (i+1)) (s.wave i).val q (allotΨ R.L (hat R.L x (i+1))) (allotΨ R.L (hat R.L x i)) Aρ G.Mult ∧ Ready_K R.L (hat R.L x i):=by
 filter_upwards [Dyad.pay_C R Q WZ x V,largeEligible V G Q WZ CA x,eventuallyZ (T:=T) H G Q sk Lq h0] with i p hr v k qx m hτ S ρ f s hp z
 obtain ⟨e,c,l,Y',d,Xp⟩:=v m _ qx hτ S ρ f s hp
 -- `hr` shadow earlier hr:4*.. in tactic.V
 exact ⟨minister hτ k s H hp G Q sk Lq CA h0 hm hu (by assumption) vκ qx p d Y' hr.1,hr.1⟩
end Parcel
open Tune Roots Oath Bake Neon
open Compass Dyad Lattice.PlaqAxes AnalyticBridge.VerifiedReset ThinGauge
open Pitching Pitching.Focus
variable (G:Morn K)
-- extra elections. ``cap ≥8`` asks universally.G0.M equality respects. Compute $Aρ.lower.κ.Initial.S.Declare η≥ any before.Source.
abbrev Fees (x:ℝ):ℝ:= max (max (max 1 x) (Real.exp 1)) (4*(Bmain * ThinGauge.yolk (G.armor).delta (Ione.duty_Q 6 2)))
abbrev requests(_G:Morn K):ℕ:= 8+ ⌈2*Ione.strive_E 6⌉₊
lemma request_p:8≤ requests G∧ 2*Ione.strive_E 6 ≤ (requests G:ℕ):= by constructor;exact Nat.le_add_right ..; exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_add_left ..)) -- expected cast? 2*ℝ≤ (n:ℕ) coercion
lemma feesL (x Aε:ℝ)(p:Fees G x≤Aε):∀ᶠ k:ℕ in atTop,∀ L:Side, k≤L.val→ ThinGauge.Open G.armor.g0 G.armor.delta (Ione.duty_Q 6 2) Aε (L.val:ℝ)⁻¹:=by
 unfold Fees at p; have h:1≤Aε:=by calc
    _ ≤ max 1 x:= le_max_left ..
    _ ≤ max (max 1 x) (Real.exp 1):= le_max_left ..
    _ ≤ max (max (max 1 x) (Real.exp 1)) _:= le_max_left ..
    _ ≤ Aε:= p
 have hp: Bmain * ThinGauge.yolk G.armor.delta (Ione.duty_Q 6 2) ≤ Aε/4:=by have he:4*(Bmain* ThinGauge.yolk G.armor.delta (Ione.duty_Q 6 2)) ≤ Aε:= (le_max_right ..).trans p; exact (le_div_iff₀ (by norm_num)).mpr ((mul_comm ..).le.trans he)
 obtain ⟨k,v⟩:=eventually_atTop.mp (sunL G.armor.g0 G.armor.delta _ Aε h hp)
 filter_upwards [eventually_ge_atTop k] with L hL; exact fun i hi=>v _ (hL.trans hi)
noncomputable def minAir (G:Morn K)(x Aε:ℝ):ℕ:=if h:Fees G x≤ Aε then Classical.choose (eventually_atTop.mp (feesL G x Aε h)) else 1
lemma horizon (x Aρ:ℝ)(p:Fees G x≤ Aρ)(N:Side)(t:minAir G x Aρ≤N.val):ThinGauge.Open G.armor.g0 G.armor.delta (Ione.duty_Q 6 2) Aρ (N.val:ℝ)⁻¹:=by unfold minAir at t; rw [dif_pos p] at t; exact Classical.choose_spec (eventually_atTop.mp (feesL G x Aρ p)) _ t _ le_rfl
lemma horizon2 (T:Morn K) (h:T={G with cap:=max (requests G) (Fintype.card Ξθ), Mult:=T.Mult}) (Aρ x qv ε:ℝ)(l:Καlendar R T.armor qv Aρ T.Mult ε)(p:Fees G x≤ Aρ)(N:Side)(t:minAir G x Aρ ≤N.val): Real.exp 1 ≤Aρ ∧4*(Aρ+1)≤ T.Mult∧ThinGauge.Open T.armor.g0 T.armor.delta (Ione.duty_Q 6 2) Aρ (N.val:ℝ)⁻¹∧2*Ione.strive_E 6 ≤ (T.cap:ℝ):=by
 let e0:=horizon G x Aρ p N t
 have hP:Real.exp 1≤Aρ:= (show Real.exp 1 ≤ Fees G x from (le_max_right ..).trans (le_max_left ..)).trans p
 have hR:=e0.asset; have hN:8≤T.cap:=by rw [h]; exact (request_p G).1.trans (le_max_left ..)
 have hm: 2*Ione.strive_E 6≤ (T.cap:ℝ):= by rw [h]; exact (request_p G).2.trans (Nat.cast_le.mpr (le_max_left ..))
 refine ⟨hP,?_, ?_,hm⟩
 · have he:=l.sold; change (T.cap:ℝ)*Aρ+_+_+_ ≤T.Mult at he; have hh:(8:ℝ) ≤ T.cap:=by exact_mod_cast hN -- coercion annotation? expect
   have hyv: 0≤MF:=mul_nonneg (Real.exp_pos _).le hPπ; nlinarith only [he,hyv,mul_le_mul_of_nonneg_right hh (zero_le_one.trans hR),hR]
 rw [h]; exact e0
#print axioms Parcel.eventualStep
#print axioms horizon2
end YM.CF.Py.Rate
