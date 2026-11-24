import YM.SU5.FiniteGaugeData.LocalLimit.Election.Ledger
import YM.SU5.FiniteGaugeData.LocalLimit.Transfer.Bridge

/-!
# Pairs of trajectories, at same pivot x

These volumes and cutoffs are from the release `DActual` election, with
extra resources retained and exposed. This is the *actual-first* price bridge.
An auxiliary heat donor at each participating fixed period; on the common subsequence
price costs for CapP nonvanishing and enrollment of these donors still use lower
cutoff thresholds allowed to depend on period. Once paid, uniform on the cone
(and even in tests on the whole period with fixed bounds).

This does not attain the *equal bare* common period prescription of 503.
`Tape.X` are Parcel histories. The cutoff depth at each admissible pair of
indices is **identical** (`trunk`-rule applied to shared `ivory`), but `X` and
hence the fields beta, wave, pilot (= B₀ in the manuscript, computed using the
size-dependent Last from `P.W.arm`) need not agree across periods.
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

namespace Preparation
open FullBill Window Marks
local notation "q₀" => Chi.canonical
variable {P : Preparation}
abbrev Cal (P:Preparation) := Month P.x 1 6 2 P.N0 P.V P.W
abbrev Ctor (P:Preparation) (s:Side) := cell s P.block P.R.L
abbrev limitPrice (P:Preparation) (w:ℝ) (i:ℕ) := expense P.C P.R P.x w i
variable {F : (s:Side)→ Scree.Loom s → Prop} (T:Preparation.Cal P) (base m:Side) (w:ℝ) (u:ℕ→ℕ)

abbrev gaugeFreq (P:Preparation) (base:Side) := commonQ P.R P.block base

local notation "kT" i:max => trunk P.b (u i)
local notation "Φ" => gaugeFreq P base

structure Tape (F : (s:Side)→ Scree.Loom s → Prop) where
  funds : T.q ≤ m.val
  CapeT : Cape m P.block P.R.L
  ρ : ℕ → ℝ
  ownership : CanCape P.J q₀ m CapeT
  craft (i:ℕ) : F _ (CapeT i)
  bonus : ∀ i, 0 < ρ i
  X : ∀ l : ℕ, Parcel P.J q₀ P.h P.δ P.C P.R0 T funds CapeT ρ (gaugeFreq P base) l
  paths (l : ℕ) : FromShot P.P P.delay (X l)
  -- `kick` an index in the (common!) ivory cutoff subsequence: may depend on period
  kick : ℕ
  domain (i:ℕ) (p:kick ≤ i) : cone P.b (u i) m
  lower (i:ℕ) (p:kick ≤ i) : Real.exp (-w*sites (cell m P.block P.R.L 0)) ≤ ‖compensated P.U ((X (trunk P.b (u i))).gram 0) (CapeT 0)‖
  Q (i:ℕ) (p:kick ≤ i) : Donor P.V P.b (u i) P.N0 P.J q₀ P.h P.δ P.C P.R0 T m funds CapeT (X (trunk P.b (u i))).pilot (gaugeFreq P base) P.P P.F0


-- Note `Period`, `A`, `k`, `N` nomenclature in manuscripts varies. In this
-- application: i indexes unbounded IR periods, k indexes common unbounded UV depths.
-- The **period parameter m** is `rung R base (stage i)`. The **cutoff depth n**
-- is `trunk P.b (ivory k)`.
structure Course (P:Preparation)(F : (s:Side)→ Scree.Loom s→Prop) where
  meter : Cal P
  paidM : MeterQ P.V 1 2 6 P.N0 P.J q₀ P.h P.R0 P.δ P.x meter
  oneP : 1 ≤ P.x
  tile : Side
  ivory : ℕ → ℕ
  UV : StrictMono ivory
  stage : ℕ → ℕ
  infrared : StrictMono stage
  τ : ℝ
  revenue : 0 ≤ τ
  lease (i) : let A:=rung P.R (tile*P.M) (stage i); (∃ M:Side, A=M*P.M ∧ P.J.h ≤ M.val) ∧ 61 ≤ A.val
  voyage (i) : Tape meter (tile*P.M) (rung P.R (tile*P.M) (stage i)) τ ivory F

lemma enroll (H:P.nominated F) : Nonempty (Course P F) := by
  obtain ⟨T,_,q,u,c,v,f,h⟩ := H.earn; dsimp only at h
  obtain ⟨hv,hw,hf,h,E,hE,g⟩ := h
  let base:= c*P.M; let A(i:ℕ):=rung P.R base (f i); let z(i:ℕ):= trunk P.b (v i)
  have hp (i) : Nonempty (Tape T base (A i) E v F) := by
    obtain ⟨_,_,k,S,ρ,Ah,Th,U,X,pG,H⟩:= g i
    have path (l : ℕ) : FromShot P.P P.delay (X l) := by
      obtain ⟨bon,b,sol,eqs⟩ := pG l
      exact ⟨bon,b,sol,eqs.gramZ,eqs.waveZ⟩
    have u(i') := path (z i')
    have hz: ∀ᶠ k' in atTop, cone P.b (v k') (A i):= hw.tendsto_atTop.eventually_ge_atTop ((A i).val^5)
    have p : ∀ᶠ k' in atTop, Nonempty (Donor P.V P.b (v k') P.N0 P.J q₀ P.h P.δ P.C P.R0 T (A i) k S (X (z k')).pilot (gaugeFreq P base) P.P P.F0) := (hv.tendsto_atTop.eventually (Donor.available k P.H P.response P.height rfl P.sculpture P.early)).mono fun k e=> e _ (u k).paid (X _).due -- order
    obtain ⟨l,Q⟩:= eventually_atTop.mp (hz.and (p.and H))
    exact ⟨⟨k,S,ρ,Ah,Th,U,X,path,l,fun _ p=>(Q _ p).1,fun _ p=>(Q _ p).2.2,fun _ p=>Classical.choice (Q _ p).2.1⟩⟩
  exact ⟨⟨T,q,u,c,v,hv,f,hf,E,hE,fun i=>⟨(g i).1,(g i).2.1⟩,fun i=>Classical.choice (hp i)⟩⟩

theorem heat_election (ε : ℝ) : ∃ P : Preparation, ε < P.x ∧ Nonempty (Course P optionalLaw) := by
  obtain ⟨P,h,q⟩:= Preparation.main_election ε; exact ⟨P,h,Preparation.enroll q⟩

namespace Course
variable (Y:Course P F)
abbrev ir (i:ℕ) := rung P.R (Y.tile*P.M) (Y.stage i)
abbrev uv (k:ℕ) := trunk P.b (Y.ivory k)

lemma ir_grows : StrictMono fun i=> (Y.ir i).val := (rung_ladder (V:=P.V) _).comp Y.infrared
lemma uv_grows : StrictMono Y.uv := (trunk_up P.b).comp Y.UV

local notation "Xs" i:max => P.Ctor (Y.ir i)
local notation "Ξ" i:max => Y.voyage i
local notation "Xm" i:max j:max => (Ξ i).CapeT j
local notation "G₀" i:max k:max => (Ξ i).X (Y.uv k)
local notation "Gs" i:max k:max h:max => (Ξ i).Q k h

abbrev texture (i k j:ℕ)(A:Window.Evaluation (P.Ctor (Y.ir i) j)) := Window.finiteForm P.V.U P.U ((G₀ i k).gram j) (Xm i j) A
abbrev charge (j:ℕ) := expense P.C P.R P.x Y.τ j
abbrev debt (j:ℕ) := Y.charge j+|serviceCost Y.meter j|

theorem each_level (i k j:ℕ) (p:(Y.voyage i).kick ≤ k) (v:j ≤ Y.uv k) :
    Priced P.V ((G₀ i k).gram j) P.U (Xm i j) (Y.charge j) (Y.debt j) :=
  cap_price _ P.H P.height (G₀ i k) ((Ξ i).paths _) Y.revenue ((Ξ i).lower k p) v

-- Publication at one such i includes the full actual-theory utilization of
-- the bridge, including its support on shared cutoffs even though some elections
-- are only used starting at the respective kick. In particular it isn't asserting
-- uniform until those thresholds have been met!
theorem heatGap (j:ℕ) :
    ∀ᶠ k in atTop, j < buoy (Y.ivory k) ∧ ∀ i (p:(Y.voyage i).kick ≤ k),
     Donor.Gap Y.meter (Ξ i).funds P.C P.δ P.R0 Y.τ (G₀ i k) (Gs i k p) j := by
  filter_upwards [Y.UV.tendsto_atTop.eventually (Donor.paired (T:=Y.meter) P.H P.height j P.b Y.revenue)] with k p
  exact ⟨p.1,fun i h=> p.2 (Y.ir i) _ _ _ _ _ _ _ _ ((Ξ i).paths _) ((Ξ i).lower k h) ((Ξ i).domain k h)⟩

-- Actual sharp read on whole-period operator probes compares to heat. (No
-- geometry or gauge assumption needed on F' here.)
theorem thaw (j : ℕ) (ε : ℝ) (p : 0 < ε) :
    ∀ᶠ k in atTop, ∀ i, ∀ h : (Y.voyage i).kick ≤ k,
      ∀ F' : Tagged (P.Ctor (Y.ir i) j), ∀ w : ℝ, Measurable F' → (∀ i, ‖F' i‖ ≤ w) →
        ‖Marks.ratio P.V P.U ((G₀ i k).gram j) (Xm i j) F'-
          Marks.ratio P.V P.U ((Gs i k h).gram j) (Xm i j) F'‖ ≤ ε*w := by
  filter_upwards [Y.heatGap j,Y.UV.tendsto_atTop.eventually (Donor.shrinks (T:=Y.meter) (τ:=Y.τ) (C:=P.C) j P.b p)] with k l S i h F' w u v
  refine (((l.2 i h).mark_bound (Ξ i).funds F' u v).2.2).trans (le_trans (mul_le_mul_of_nonneg_left (S (Y.ir i) ((Ξ i).domain k h)) (le_trans (norm_nonneg _) (v (1,Classical.arbitrary _)))) (le_of_eq (mul_comm ..)))
end Course
end Preparation
end LocalLimit
end YM.CF.Py.Rate
