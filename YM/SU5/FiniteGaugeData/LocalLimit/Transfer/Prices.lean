import YM.CF.Vp929.EveryLevel
import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Horizontal
/-!
# Pricing on the commissioned branch

Objects from the proof of `DActual.Ratevol`. `level_secured` below is the
same proof as `apply_level` exported with the recursive constant named here.
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


open Graph.Diff Graph.Angle Window


variable {ρ : ℕ → ℝ}
local notation "S₀" => cell m B R.L
section lower
variable {l₀ : ℕ}(F0 : Parcel J q h D C Q T ht W0 ρ f l₀)
local notation "Xc" => F0.gram
local notation "Σπ" i:max => partitionZ (F0.gram i) U (W0 i)
private lemma mono_sites (i:ℕ) : sites (S₀ i) ≤ sites (S₀ (i+1)):=by
 unfold sites; apply pow_le_pow_left₀ (by positivity); norm_cast; change (Domain (mesh m R.L i) B).val ≤ (Domain (mesh m R.L (i+1)) B).val; rw [mesh_succ]; set v:=Vale.mesh m R.L i; change _*2*B.val*2 ≤ v.val*R.L.val*2*B.val*2; gcongr; exact Nat.le_mul_of_pos_right _ R.L.property
def expense (C:ℝ→ℝ) (R:Patch) (x b:ℝ) :ℕ→ℝ
 | 0=>b
 | n+1=>expense C R x b n+|C (hat R.L x n)|
variable (v:ℝ)
local notation "Cs" j:max=> expense C R x v j
lemma posExpense (t:0 ≤ v)(j:ℕ) :0≤ expense C R x v j:=by induction j with | zero=> exact t | succ n ih=> exact add_nonneg ih (abs_nonneg _)
local notation "pS" i:max=> sites (cell m B R.L i)
lemma level_secured (t:0 ≤ v)(p₁:Real.exp (-v * sites (cell m B R.L 0)) ≤ ‖compensated U (F0.gram 0) (W0 0)‖) (j:ℕ)(p:j ≤ l₀) : Real.exp (-expense C R x v j*pS j) ≤ ‖compensated U (Xc j) (W0 j)‖:=by
 induction j with
 | zero => exact p₁
 | succ j ih=>
    have he:= ih (Nat.le_of_lt p); let V0:= pS j; let Vp:=pS (j+1); let Z:= ‖Σπ j‖; let a:= Xc j; let b:=Xc (j+1); have ht:=F0.perSite j p; change |a.v.re-b.v.re| ≤ _ at ht
    simp only [compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at *; rw [(F0.balance (j+1) p).trans (F0.balance j (le_of_lt p)).symm]; change Real.exp (- Cs (j+1)*Vp) ≤ Real.exp (- b.v.re)* Z
    let w:= Cs j; let α:= C (hat R.L x j); change Real.exp (- w*V0) ≤ Real.exp (- a.v.re)*Z at he; have hCp:0 ≤ w+|α|:=posExpense v t (j+1); have hc:V0 ≤Vp:=mono_sites j; have hx:0 ≤ V0:=zero_le_one.trans (sites_pos _)
    calc _ ≤ Real.exp (- (w+|α|)*V0):= (Real.exp_monotone <| mul_le_mul_of_nonpos_left hc (neg_nonpos.mpr hCp))
         _ = Real.exp (-|α| *V0)*Real.exp (-w*V0):=by rw [←Real.exp_add]; ring_nf
         _ ≤ Real.exp (-|α| *V0)*(Real.exp (- a.v.re)*Z) := mul_le_mul_of_nonneg_left he (by positivity)
         _ ≤ _ := by
            rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; obtain q: -(|α| *V0)≤ a.v.re-b.v.re:=le_trans (neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self α) hx)) ((abs_le.mp ht).1); linarith
end lower

local notation "vol" i:max => sites (cell m B R.L i)
local notation "Yc" i:max => dleaf R.L (hat R.L x i)
def serviceCost (T:Month x 1 6 2 N0 V W)(i:ℕ) := earnings W (T.a i) (2* hat R.L x i) (dleaf R.L (hat R.L x i)/1000)
variable {w : ℝ}

private lemma field_price {i:ℕ} (F:GramM (Ω i))(hp:1≤ h)(ht:1≤x) (t:Scree.Loom (Ω i))
    (S : Month x 1 6 2 N0 V W)
    {u : ℝ} {k : ℕ} (L:InterestX W.C (Ω i) F.J) (Hr : Roof (Ω i) u d k t)
    (size : U.roundZ ≤ (Ω i).val) (l:ℕ)
    (p : F=construct (S.a i) (V.L.path l) K.top.clip F.J F.beta (F.F,F.K) F.v)
    (hc : LotR F h (Yc i / 1000) (Yc i / 1000))
    (hβ : matchedX (hat R.L x i) F.beta) :
    Envelope (denZ F U t) ∧ ∀ x, ‖field U F t x‖ ≤ Real.exp (serviceCost S i * sites (cell m B R.L i)) := by
  let g:= construct (S.a i) (V.L.path l) K.top.clip F.J F.beta (F.F,F.K) F.v
  have e:0 ≤ F.beta:= le_trans (le_trans (div_nonneg (le_trans (zero_le_one.trans ht) (Vale.crown ..)) (by norm_num)) hβ.1) le_rfl
  rw [p]; exact ⟨denInt W Hr l size F.beta F.v (show LotR g h _ _ from p ▸ hc), extensive W L Hr l size hp F.beta F.v (p ▸ hc) e hβ.2⟩

open FullBill
variable {i l : ℕ} (H : Service V U W J q h D C Q P N0 delay) (hh : 1≤h)
include ht H hh
lemma cap_price (A : Parcel J q h D C Q T ht W0 ρ f l) (pA : FromShot P delay A) (u : 0 ≤ w)
    (hA : Real.exp (-w * sites (cell m B R.L 0)) ≤ ‖compensated U (A.gram 0) (W0 0)‖)
    (hi : i ≤ l) : Priced V (A.gram i) U (W0 i) (expense C R x w i) (expense C R x w i+|serviceCost T i|) := by
  obtain ⟨uC,c,s,p,v⟩ := pA
  have e:=uC.can.cape i
  have ey:=uC.charged H s.toRealQ i hi
  have hr:Roof (Ω i) J.k d J.n (W0 i):={ e.paid with paid:=fun x=>(e.paid.paid x).shrink J.hr.le }
  have hx:1≤x:= (uC.prices x le_rfl).grade
  have he:= level_secured ht A w u hA i hi; have hf:= A.pull.sift i hi; rw [p] at he hf ⊢
  obtain ⟨g,v⟩ := field_price (Branch.gram P (Actual T ht W0 f l) c i) hh hx (W0 i) T ((W.arm ..).sound i) hr (J.gran.trans e.size) (l-i) rfl (ey.toCost.lot _ _) hf
  refine produced V _ he g v ?_; linarith [le_abs_self (serviceCost T i)]

namespace Donor
variable {F0 : Scrolls B} (Y : Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0)
omit H
lemma permits_chill (he : i < buoy n) (hx:1 ≤ x) :
    Envelope (denZ (Y.gram i) U (W0 i)) ∧
    ∀ t, ‖field U (Y.gram i) (W0 i) t‖ ≤ Real.exp (serviceCost T i * sites (cell m B R.L i)) := by
  have hp:= (Y.cape i).paid; have E:= Y.cool.represented i; have p:= (Y.pull.owns i (he.trans (deeper ..)).le).taste; let F:=Y.gram i
  have hs: (W.arm (T.large.trans ht) kT).Q i=F.J := p
  have hQ : LotR F h (Yc i /1000) (Yc i /1000):= by unfold F; rw [E]; exact (Y.cool.charged i he).toCost.lot F.beta F.v
  rw [hs] at E; exact field_price (Y.gram i) hh hx (W0 i) T (hs ▸ (W.arm ..).sound i) { hp with paid:=fun i=>(hp.paid i).shrink J.hr.le } (J.gran.trans (Y.cape i).size) (kT-i) E hQ (Y.pull.sift i (he.trans (deeper ..)).le)
end Donor
end LocalLimit
end YM.CF.Py.Rate
