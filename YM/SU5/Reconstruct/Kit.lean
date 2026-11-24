import YM.SU5.Reconstruct.Connection
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)
variable (C : ∀ j:Axis, Tower.Arena Y H G.history.circuit j 0 false)
local notation "𝔇" i:max => displayAlgebra Y H V Q Qt i false (C i)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)

-- assembled BEFORE covariance work. Contains actual bare S extraction and both versions
-- of positivity/density on chose char. Detailed chiral & product reading: see
-- action_at, atCutoff_script, exponent_column, pairAtCutoff, footprint_check, accompanying report
-- (use on Meter credentials below with any budget). NO new Continuum claims in this CP.
local notation "π" j:max=> viewProject Y H D G C c j
local notation "B₀" j:max s:max=>openAt Y H D G C c j s
local notation "i₀" n:max=> i (G.rows n)
local notation "t₀" n:max=> k (G.columns n)

section
variable (P:Panel Y H D.univ_ G.history G.clipped 0 false (C 0))
-- use as Prop, exact individual C-star operations in Domain
set_option maxHeartbeats 600000 in
def EuclideanKit : Prop :=
  (∀ (n:ℕ)(U:Set RSpace) (f:PolAt Y H n U),
     Tendsto (fun r=> readingAtTop Y H (i (G.rows r)) (k (G.columns r)) f.val) atTop
       (𝓝 (∫ a, sch Y H D G C (P.character a) f.val ∂P.μ)) ∧
       ∀ᶠ r:ℕ in atTop, Pay Y n (i (G.rows r)) (k (G.columns r)) ∧
         taking Y H (i₀ r) (t₀ r) f.val=readingAtTop Y H (i₀ r) (t₀ r) f.val ∧
         (let m:=i (G.rows r); let w:=k (G.columns r); let s':=Y.uv w; let N:=side Y m s'; let F:=toMark (atCutoff Y H m w f.val)
          covariant F ∧ ∃ S:Finset Cover, SupportedPhysically Λ l s' S U ∧ AtSupport false (Satin.region S N) F ∧ FullDistances S N)) ∧
  (∀ (j:Axis)(s:ℕ)(f g:PolAt Y H s (flank j 0)),
      inner ℂ (locatePoly Y H D G C c j s f) (locatePoly Y H D G C c j s g)=
        sch Y H D G C c ((PhaseChoice.atZero Λ).oppose Λ j K f.val * g.val) ∧
      Dense (⋃ s:ℕ,Set.range (fun y:PolAt Y H s (upperRoom j)=> (B₀ j s) y)) ∧
      Dense (⋃ s:ℕ,Set.range (fun y:PolAt Y H s (upperRoom j)=> viewProject Y H D G C c j ((B₀ j s) y)))) ∧
   ∀ u: ((𝔇 0) →⋆ₐ[ℂ] ℂ), (∀ (s:ℕ)(R:ℝ), 0 < R → ∀ f: PolAt Y H s (Tapestry.cabin R), sch Y H D G C c f.val= sch Y H D G C u f.val) → c=u

set_option maxHeartbeats 900000 in
lemma our_domain (h: Issued Y H D.univ_ G.history G.clipped 0 false (C 0) P) :
    EuclideanKit Y H D G C c P := by
  refine ⟨fun n U f=> ⟨?_,?_⟩,fun j s f g=> ⟨poly_gram Y H D G C c j f g,genuinely_dense Y H D G C c j,compass_dense Y H D G C c j⟩, polynomial_ext Y H D G C c⟩
  · exact panel_from_readings Y H D G C P h n (inside_budget Y H f.property)
  · obtain ⟨b,v,t⟩:= pressured Y H f.property
    have hh:=unwrapSupported Y (show U∩ Tapestry.cabin b ⊆ Tapestry.cabin b from Set.inter_subset_right)
    have hm:= ((D.univ_.pick.grow_i.comp G.history.growsA).tendsto_atTop)
    filter_upwards [interior_payment Y H G n,hm.eventually hh] with r u hu
    refine ⟨u,(identifyRevenue Y H _ _ n (inside_budget Y H f.property) u).2.2,colorAtCutoff Y H _ _ n t u,?_⟩
    let N:= Y.uv (t₀ r); obtain ⟨S,p,w⟩:=top_location Y H _ _ n t u
    exact ⟨S,fun i v y w=> (p i v w).1, w, hu N S p⟩
end

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
