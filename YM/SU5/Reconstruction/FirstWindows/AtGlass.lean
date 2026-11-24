import YM.SU5.Reconstruction.FirstWindows.Consistency
import YM.SU5.Reconstruction.FirstWindows.Charge
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open SlabMark Fock Altitude Exhibition
variable {L : Rack Λ l} {B : Clay Λ l} {T : ℕ → ℕ → Tariff} {t : ℕ → Tariff}
  (Z : Fashion Y H i k I E L B T t)
variable (c : ∀ j, Arena Y H G.history.circuit j 0 false)
  (P : Panel Y H V G.history G.clipped 0 false (c 0))
  (χ : displayAlgebra Y H V G.history G.clipped 0 false (c 0) →⋆ₐ[ℂ] ℂ)
local notation "V₀" => osValue Y H V G 0 (c 0) χ
local notation "D" => Domain Y H G
local notation "A" => realize Y H Z.toExhibition
set_option quotPrecheck false
local notation "f₀" f:max => (⟨realize Y H Z.toExhibition f, always_realizes Y H V G Z.toExhibition f⟩ : Domain Y H G false Set.univ)
local notation "κ" j:max => displacement Y H V G.history G.clipped 0 false (c 0) χ j (c j)
set_option maxHeartbeats 500000

/-!
# Stage for physical observables, towards step II reconstruction

One phase, arbitrary resolution. `Papal.first_windows` extends Glasshouse
with the requested *first* identification in the given even Euclidean system
(local polynomials and interpretation as physical spacetime probes,
on the very chiral prescription), common dense OS test domain, some covariance,
and survival of precise interaction (incl projection candidate; the probe
itself uses only the narrow link, and even has the required curvature mask
option). Not yet reconstructed to a local Haag-Kastler net.
-/
structure ContextsFor : Prop where
  determines (q : Bool) (U : Set RSpace) : realize Y H Z.toExhibition '' {x | x.val ∈ questions Λ l (tent Y H) q U} = (Domain Y H G q U : Set (Sky (tent Y H)))
  region_product (U W : Set RSpace) (q : Bool) (d : Disjoint U W) {x y} : x∈ Domain Y H G q U → y∈D q W → x*y∈ D q (U∪W)
  reading (f : FiniteGaugeDataPoly (tent Y H)) : V₀ (f₀ f) = PhaseChoice.onDrawing Y H V G Z.toExhibition 0 c (PhaseChoice.SameCharacter.resident Y H V G 0 false (c 0) χ) f.val
  gauge_turn (g : RSpace → SU.E) (U : Set RSpace) (x : Sky (tent Y H)) (h : x∈ D true U) : onFrame g Λ K x=x
  gauge_all (g : RSpace → SU.E) (x : Sky (tent Y H)) (h : x∈D false Set.univ) (p : onFrame g Λ K x∈ D false Set.univ) : V₀ ⟨onFrame g Λ K x,p⟩=V₀ ⟨x,h⟩
  sharp_limit (f : FiniteGaugeDataPoly (tent Y H)) : Tendsto (fun n => taking Y H (i (G.rows n)) (k (G.columns n)) f.val) atTop
      (𝓝 (∫ a, osValue Y H V G 0 (c 0) (P.character a) (f₀ f) ∂P.μ))
  joint_path (U : Set RSpace) (q : Bool) (f : FiniteGaugeDataPoly (tent Y H)) (v : f.val∈ questions Λ l K q U) :
    ∀ᶠ s in atTop,∃ S : Finset Cover, PhaseChoice.SupportedPhysically Λ l s S U ∧ ∀ᶠ r in atTop,
      Tapestry.Pay Y s (i (G.rows r)) (k (G.columns r)) ∧
        ∀ n, s+n ≤ Y.uv (k (G.columns r)) → SharpRecord Y H U f q s n (i (G.rows r)) (k (G.columns r)) S
  walls (q : Bool) (p : Selected.placement Λ) (j : Axis) (U : Set RSpace) (x : Sky (tent Y H)) (h : x∈D q U) :
    move K p x ∈ D q (slides (coordinates Λ p) U) ∧ flipMark j K x∈ D q (mirrorE j 0 '' U)
  -- gauge of value on all transformed spacetime probes. Mark semantics by `Spaces`,`Grid`,
  -- incl separated multiplication symmetries with contact-products among *one* of the marks.
  grid (p : Selected.placement Λ) (x : Sky (tent Y H)) (h : x∈D false Set.univ) (b : move K p x ∈D false Set.univ) : V₀ ⟨move K p x,b⟩=V₀ ⟨x,h⟩
  reflect (j : Axis) (x : Sky (tent Y H)) (h : x∈D false Set.univ) (b : flipMark j K x ∈D false Set.univ) : V₀ ⟨flipMark j K x,b⟩ = star (V₀ ⟨x,h⟩)
  registered (j : Axis) : osValue Y H V G j (c j) (κ j)= V₀
  reconstructedDomain (j : Axis) : DenseRange (positiveKet Y H V G j (c j) (κ j)) ∧ DenseRange (compassKet Y H V G j (c j) (κ j))
  repr (j : Axis) (x : Domain Y H G false (flank j 0)) :
    unify Y H V G 0 j c χ (OSvector Y H V G j (c j) (κ j) x)=appointVector Y H V G 0 j c χ x

lemma atGlass (p : Issued Y H V G.history G.clipped 0 false (c 0) P) : ContextsFor Y H V G Z c P χ :=
  ⟨realize_covers Y H V G Z.toExhibition,
    fun _ _ _ h _ _ a b=> domain_mult Y H G a b h,
    fun f => (realize_read Y H V G Z.toExhibition 0 c χ f _).1,
    fun g _=> physical_invariant Y H V G g Z.toExhibition,fun g=>onFrame_value Y H V G g Z.toExhibition 0 c χ,
    fun f=> along_election Y H V G Z f c 0 P p,fun U _ f v=> (questions_price Y H v).mono fun s h=> sharp_record Y H V G U f v s h,
    fun q p j U x h => ⟨moving Y H V G p x h,mirror_support Y H G j x h⟩,
    fun p _=> moving_value Y H V G 0 (c 0) χ p,
    fun j _ => reflected_read Y H V G j 0 (c 0) χ,
    fun j => os_across Y H V G 0 (c 0) χ j (c j),
    fun _ => ⟨future_dense Y H V G _ _ _, compass_domain_dense Y H V G _ _ _⟩,fun j=> carries_marks Y H V G 0 j c χ⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
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
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
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
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
open Satin Tapestry
open Lifted (nodeC node_of)
open _root_.YM.CF.Buffered.Afterglow.Tower
open Buffered.Afterglow.Tower.Selected Vacancy
open YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open YM.CF.Buffered.Afterglow.Tower.FirstWindows

/-- Glasshouse, checked for the beginning of reconstruction. *The very same witnesses*. -/
theorem first_windows (ε η:ℝ)(p:0<η)(U:Supplier) :
    ∃ (P:Preparation)(l:ℕ)(Z:ℝ),ε<P.x ∧ P.d ≤ η ∧ decorate U P l Z≤ P.h ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (H:Real.exp 1≤ P.x)(Y:Course P (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=P.δ) P.V P.W P.J P.N0 z P.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay) ∧
        (∀ i j:ℕ, Buffered.Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ q d w C, Korn Y H q d w C Z∧
        ∃ (a b:ℕ→ℕ) (I: ℕ→Buffered.Family (tent Y H)→ℕ→ℂ)(E:ℕ→Buffered.Family (tent Y H)→ℂ) (L:Rack P l)(B:Tapestry.Clay P l)(T:ℕ→ℕ→Tapestry.Tariff)(t:ℕ→Tapestry.Tariff),∃ D: Tapestry.Fashion Y H a b I E L B T t, SeasonCert Y H D∧
          ∃ (G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H)
            (c : ∀ j, Tower.Arena Y H G.history.circuit j 0 false)
            (P' : Panel Y H D.univ_ G.history G.clipped 0 false (c 0)),
            (∀ j:Axis, ∃ room:Tower.Arena Y H G.history.circuit j 0 true, Papal.mixed_in_ground Y H D.univ_ G j room q d w) ∧
            Issued Y H D.univ_ G.history G.clipped 0 false (c 0) P'∧
            -- retain barycenter explicit on E
            (∀ j F, ∫ x, response Y H D.univ_ j G.history G.clipped 0 false (c 0) (P'.character x) F ∂P'.μ = E j F.val) ∧
            ∃ (s : ℕ) (ζ : ℝ) (f f' : SU.Slot → Vacancy.observable (tent Y H) true) (x : P'.X), 0 < ζ ∧ paints_for Y H D.univ_ s G.history G.clipped (c 0) P' c q d w ζ x f f' ∧
            ContextsFor Y H D.univ_ G D c P' (P'.character x) ∧
            Appointment Y H D.univ_ G D.toExhibition 0 c (SameCharacter.resident Y H D.univ_ G 0 false (c 0) (P'.character x)) ∧
                   ∀ (z : SU.Slot) (j:Axis) (δ:ℝ), 0<δ → let r:=displacement Y H D.univ_ G.history G.clipped 0 false (c 0) (P'.character x) j (c j); let o:= CF.Pannier.Chancel.grain (payout d q w); let S:= Sen o (payout d q w)
                                                          Silence (f' z).val ∧
                                                          (∃ p q':Cover, LinkCheck Y H D.univ_ G j (c j) r s p q' S z o q d (f z) δ) ∧ ∃ p q':Cover, LinkCheck Y H D.univ_ G j (c j) r s p q' (grindscape (booty o d q) S) z o q d (f' z) δ    := by
  obtain ⟨P,l,Z,h₁,h₂,h₃,h₄,H,Y,y₁,y₂,y₃,q,d,w,C,k,a,b,I,E,L,B,T,t,D,
    season,G,c,pan,mixed,issued,mean,s,ζ,f,f',x,hζ,paint,appointment,survive⟩ := glass_with_appointment ε η p U
  refine ⟨P,l,Z,h₁,h₂,h₃,h₄,H,Y,y₁,y₂,y₃,q,d,w,C,k,a,b,I,E,L,B,T,t,D,
    season,G,c,pan,mixed,issued,mean,s,ζ,f,f',x,hζ,paint,atGlass Y H D.univ_ G D c pan (pan.character x) issued,appointment,?_⟩
  intro z j δ a'; obtain ⟨⟨p,q',h⟩,p',q'',u⟩ := survive z j δ a'
  let r' := displacement Y H D.univ_ G.history G.clipped 0 false (c 0) (pan.character x) j (c j)
  have v := (paint z).2.2
  have vu := (paint z).2.2.2.2 j
  exact ⟨silence_at_link Y H k.range hζ.le v.1,⟨p,q',validate_link Y H D.univ_ G j (c j) r' s p q' _ z (CF.Pannier.Chancel.grain (payout d q w)) q d _ δ vu.1.witness h⟩,
    ⟨p',q'',validate_link Y H D.univ_ G j (c j) r' s p' q'' _ z (CF.Pannier.Chancel.grain (payout d q w)) q d _ δ vu.2.witness u⟩⟩

end Papal
end LocalLimit
end Rate
end YM.CF.Py
