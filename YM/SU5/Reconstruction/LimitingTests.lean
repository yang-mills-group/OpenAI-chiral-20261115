import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.TestInteraction
import YM.SU5.Reconstruction.Berezin
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-!
# Same sequence and many equivalent read interpretations. Combine to one
unconditional *Euclidean/regulator* assertion in M1. -/
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  {t : ℕ→ℕ→Tariff} {f : ℕ→Tariff} (D : Fashion Y H i k I E L B t f)
local notation "γ" => D.toExhibition
local notation "r₀" => i ∘ G.rows
local notation "v₀" => k ∘ G.columns

lemma convergence {x : Cloud (Dome (tent Y H))} (p : x∈ FiniteGaugeDataPoly K) :
    Tendsto (fun n:ℕ=> taking Y H (r₀ n) (v₀ n) x) atTop (𝓝 (vistaTake Y H γ x)) := by
  apply Metric.tendsto_nhds.mpr; intro ε hε
  have hD:= D.allCoupon Y H p
  have hx:= Tapestry.alongRows (χ:=fun r s=>legacy Y (i r) (k s)) (fun a=> ⟨a,(D.status a a).mpr (le_refl a)⟩) (fun r s=>taking Y H (i r) (k s) x) (vistaTake Y H γ x) hD.paths ε hε
  filter_upwards [G.history.growsA.tendsto_atTop.eventually hx] with n p using p _ (G.history.gate n)

variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
variable (Q : Panel Y H V G.history G.clipped j false C) (W : Issued Y H V G.history G.clipped j false C Q)
variable (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
lemma license_pays {U : Set RSpace} {s : ℕ} {wide : Bool} {x : Cloud (Dome (tent Y H))}
    (p : x∈jetty Λ l K wide (handstamp U) (Set.Iic s)) : x∈shorter (Dome (tent Y H)) s :=
  jettyBan Λ l K wide (handstamp U) Set.univ s (by rwa [Set.univ_inter])

local notation "M" r:max => Y.uv (v₀ r)
local notation "P" r:max => (Y.voyage (r₀ r))
local notation "Ξ" r:max => partitionZ (((P r).X (M r)).gram (M r)) Λ.U ((P r).CapeT (M r))
local notation "Y₀" r:max => Journey.side Y (r₀ r) (M r)
local notation "μ" r:max => Wilson.prior SU.group (More (Y₀ r))
local notation "f₀" r:max x:max => numeratorTop Y H (r₀ r) (v₀ r) x
-- not all coordinates of η use `room`; use statement ∂P when T j given in C. adjusted x uses same starting C maybe different; for portability require only Q uses T d.

include V
lemma bare_path {U : Set RSpace} {s : ℕ} {wide : Bool} {x : Cloud (Dome (tent Y H))}
    (p : x∈jetty Λ l K wide (handstamp U) (Set.Iic s)) (d : Bornology.IsBounded U) :
    ∃ S : BillOfWork, x∈fountainHeads K S s ∧ (∀ i, silhouette Λ l i (S i) ⊆ U) ∧
    ∀ᶠ r : ℕ in atTop, Ferry Y s (r₀ r) (v₀ r) ∧ Tapestry.Pay Y s (r₀ r) (v₀ r) ∧
      (∀ n : ℕ, s≤n → let B:=frameBudget S Λ l n;
        FullDistances B (side Y (r₀ r) n) ∧ silhouette Λ l n B ⊆ U ∧
        (n ≤ M r → AtSupport false (Satin.region B (Journey.side Y (r₀ r) n)) (attire (breathing Y H n (r₀ r) (v₀ r) x)))) ∧
      AtSupport false (Satin.region (frameBudget S Λ l (M r)) (Y₀ r)) (toMark (observableTop Y H (r₀ r) (v₀ r) x)) ∧
      (x∈localEuclidean Λ l K wide U → covariant (toMark (observableTop Y H (r₀ r) (v₀ r) x))) ∧
      (∀ A : Pane (Y₀ r), ∃ z : FC (Single (Y₀ r)), Reed.Plain z ∧
        observableTop Y H (r₀ r) (v₀ r) x A=(Reed.think (Tset (Y₀ r))).eval z) ∧
      Ξ r≠0 ∧ Ξ r = (∫ v,(f₀ r 1) v ∂ (μ r)) ∧ Integrable (f₀ r x) (μ r) ∧
      taking Y H (r₀ r) (v₀ r) x=(∫ v,(f₀ r x) v ∂ (μ r)) / (Ξ r) := by
  obtain ⟨S,h,f⟩:= uniform_support p
  have p':= (V.pick.grow_i.comp G.history.growsA).tendsto_atTop.eventually (full_distances Y H d)
  refine ⟨S,f,h,?_⟩
  filter_upwards [p',G.history.finance s] with r hx hp
  let j:= r₀ r; let k:= v₀ r; let t:= M r
  have hv : Tapestry.Pay Y s j k:=⟨hp.depth,hp.enters⟩
  have hw (n : ℕ)(v:s≤n): x∈ fountainHeads K S n:= coin_mono K S S s n (fun i u=> Finset.Subset.refl _) v f
  have hF := hw t hv.2
  obtain ⟨w,v,g⟩ := bare_ledger Y H j k x hv.1 (prePrice K S (M r) hF) -- placeholders
  refine ⟨hp,hv,?_,bare_support Y H _ _ x S hv.1 hF,?_,?_,v,?_,w,g⟩
  · intro n v W; exact ⟨hx n _ (fun i x=>(supported_iff.mpr (future_budget S h n)).contains x), future_budget S h n,
      fun z=> actual_supported Y H ⟨hv.1,z⟩ S x (hw n v)⟩
  · intro u; obtain ⟨n,B,h',t,k⟩:= u
    apply top_covariant Y H _ _ x (A:=handstamp B) hv.1 (wellGrows Λ K l true _ _ _ _ (Set.subset_univ _) Set.Subset.rfl (wellWider Λ K l wide (handstamp B) _ k)) (prePrice K S (M r) hF)
  · intro A; obtain ⟨x,h,e,z⟩:= top_insertion Y H (r₀ r) (v₀ r) A hv.1 S x hF
    exact ⟨x,z,e⟩
  obtain ⟨h,q,r⟩ := physical_partition Y H (r₀ r) (v₀ r) hv.1
  exact q.trans (integral_congr_ae (Eventually.of_forall fun u=> (unmarked_top ..).symm))

lemma census_converges {x : Cloud (Dome (tent Y H))} (p : x∈ FiniteGaugeDataPoly K)
    (Q : Panel Y H V G.history G.clipped j false (T j))
    (W : Issued Y H V G.history G.clipped j false (T j) Q) :
    Tendsto (fun n:ℕ=> taking Y H (r₀ n) (v₀ n) x) atTop
      (𝓝 (∫ z, onDrawing Y H V G γ j T (resident Y H V G j false (T j) (Q.character z)) x∂Q.μ)) := by
  have h: vistaTake Y H γ x=(∫ z, onDrawing Y H V G γ j T (resident Y H V G j false (T j) (Q.character z)) x∂Q.μ):= by
    obtain ⟨n,t⟩ := Tapestry.Altitude.curve.mp p
    let y:= vistaFinish Y H n γ x; let Z : Selected.Marks (tent Y H) false := PhaseChoice.observe (show TestFamily K true y.val from y.property)
    have ht(z:Q.X): onDrawing Y H V G γ j T (resident Y H V G j false (T j) (Q.character z)) x=Selected.response Y H V n G.history G.clipped j false (T j) (Q.character z) Z:= by
       rw [drawAt Y H V G γ j T _ t]; exact (evaluates Y H V G j T (resident Y H V G j false (T j) (Q.character z)) n Z).trans (sameReading Y H V G j false (T j) (Q.character z) n Z)
    simp_rw [ht]; rw [survives_check Y H V n G.history G.clipped j false (T j) Q W]
    exact vistaCall Y H n x γ t
  rw [←h]; exact convergence Y H G D p

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.bare_path
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.census_converges
