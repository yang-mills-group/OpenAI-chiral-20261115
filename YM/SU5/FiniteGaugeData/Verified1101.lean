import YM.CF.Vp929.EveryLevel
import YM.CF.Vp929.RateZero

set_option autoImplicit false
noncomputable section
namespace YM.CF.Py
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
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate.Release1101
open Pitching Focus CF.Mint
open Haro Window
open scoped ENNReal

/-- The exact family of fixed-level bills delivered by EveryLevel, including
its common subsequences and its period-dependent eventual cutoff thresholds. -/
abbrev AllLevelBills {N B : Side} {K : Teller SU.group} {R : Patch}
    {L : ChartRatio SU.group} {d : ℝ} (V : Grace K R L) {U : Grasp V.U B d}
    (W : GivenX V U) (J : Robes N V W) (q : Chi) (h : ℝ)
    (δ C R0 : ℝ → ℝ) (B1 N0 : ℕ) (x : ℝ)
    (F : (s : Side) → Scree.Loom s → Prop) : Prop :=
  ∃ T : Month x 1 6 2 N0 V W, MeterQ V 1 2 6 N0 J q h R0 δ x T ∧ 1 ≤ x ∧ ∃ M₀ : Side, ∃ k σ : ℕ → ℕ,
    let n := trunk B1 ∘ k
    let A := fun i=> rung R (M₀*N) (σ i)
    StrictMono k ∧ StrictMono n ∧ StrictMono σ ∧ StrictMono (fun i=> (A i).val) ∧
    ∃ E E' : ℕ→ℝ, 0 ≤ E ∧ 0 ≤ E' ∧ ∀ i,
      (∃ M : Side, A i=M*N ∧ J.h≤ M.val) ∧ 61 ≤ (A i).val ∧
      ∃ h' : T.q ≤ (A i).val, ∃ (W0 : Cape (A i) B R.L) (ρ : ℕ→ℝ), CanCape J q (A i) W0 ∧ (∀ j, F _ (W0 j)) ∧ (∀ j, 0 < ρ j) ∧
      ∃ X : ∀ l : ℕ, Parcel J q h δ C R0 T h' W0 ρ (commonQ R B (M₀*N)) l,
      ∀ᶠ t in atTop, ∀ j ≤ n t, FullBill.Priced V ((X (n t)).gram j) U (W0 j) (E j) (E' j)

/-- Construct one fixed pivot and apply the every-level estimate to that same
choice. The local moment estimates still carry the exponential in volume. -/
theorem exists_fixed_pivot_all_levels (ε : ℝ) :
    ∃ (K : Teller SU.group) (R : Patch) (L : ChartRatio SU.group),
      K.j = 4 ∧ R.J = 4 ∧ Odd R.L.val ∧ LocalRatio L ∧
      ∃ (V : Grace K R L) (b₁ : ℕ) (d : ℝ) (U : Grasp V.U (R.L^b₁) d)
        (W : GivenX V U) (M : Side) (J : Robes M V W) (N₀ : ℕ)
        (h : ℝ) (δ C Q : ℝ → ℝ) (pres : Prescription R (R.L^b₁)) (delay x : ℝ),
        ε < x ∧ 1 ≤ h ∧ DActual V W J Chi.canonical h δ C Q b₁ N₀ pres delay x optionalLaw ∧
          AllLevelBills V W J Chi.canonical h δ C Q b₁ N₀ x optionalLaw := by
  obtain ⟨K, R, L, hK, hR, odd, loc, _, V, b₁, d, _, _, U, W, M, J, _, N₀,
    h, δ, C, Q, hh, _, pres, delay, z, _, _, _, hz, _, _, c, F₀, z₀, _, _, _, x, hx, p⟩ := dactual ε
  refine ⟨K, R, L, hK, hR, odd, loc, V, b₁, d, U, W, M, J, N₀, h, δ, C, Q, pres, delay, x,
    hz.trans_le hx, hh, p, ?_⟩
  obtain ⟨T,_,q,one,M₀,k,σ,hist⟩ := DActual.ratevol V p hh
  dsimp only at hist
  obtain ⟨hk,hn,hσ,ha,E,E',he,he',hist⟩ := hist
  refine ⟨T,q,one,M₀,k,σ,hk,hn,hσ,ha,E,E',he,he',?_⟩
  intro i
  obtain ⟨lease,big,ht,W0,ρ,own,law,pos,X,_,priced⟩ := hist i
  exact ⟨lease,big,ht,W0,ρ,own,law,pos,X,priced⟩

end Rate.Release1101
end YM.CF.Py
