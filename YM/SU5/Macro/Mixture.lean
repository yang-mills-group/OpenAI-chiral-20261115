import YM.SU5.Selected.Cairn.Radio
import YM.SU5.Macro.Registration
import YM.SU5.Macro.Layout

/-!
# Curvature-mask the EARLY stencil keeping the price on both sides of selection

`Signal` authenticates little enough to reuse for processing at these widths. Here we
construct it for real in `Siam.mask_lights` from that very `Saturn` data (on THIS χ and
use same Fashion etc). There's no down-lift assertion with a regenerated margin at
another s. δ prescribed by their actual anchor seam.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selection.Home
open Function Filter NormedSpace Metric SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude
open Tower.PhaseChoice Tower.Selected Tower.Reconstruction
open CF.SatinRotation CF.Pannier.Chancel.Attic.Cairn Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel CF.Pannier.Chancel.Lantern CF.Pannier.Chancel.Lantern.Bulb
open Rubric Fern Fern.Planet
open OS.Semigroup MeshClock
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
    {L: Rack Λ l} {B:Clay Λ l} {T:ℕ→ℕ→Tariff} {t:ℕ→Tariff} (D: Fashion Y H i k I E L B T t)
    (G:SatinVerification.GroundExtension (i:=i) (k:=k) (E:=E) Y H) (room : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
    (χ:CapCharacter Y H D.univ_ G.history G.clipped 3 false (room 3))
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
namespace Siam
open Giant
variable (s:ℕ) (M:Giant)
local notation "Φ" => Torrent.fare
local notation "A" => early M
local notation "S" => M.ascX
local notation "Wz" => wall M
local notation "Mρ" z:max u:max a:max b:max c:max => Rubric.Marble K z M.Zumba M.ascX M.ascY u a b c
local notation "k₀" f:max => phaseRead Y H V Q Qt 3 (room 3) χ s f
/-- Stated native persistence criterion. Use `K` Family val, even spin, wide polynomial
and *projection space distinction*. Both know their height s independent of regulator. -/
structure Signal (f g: Dome (tent Y H)) (z:Window.Family) (ε:ℝ) : Prop where
  gaugeEarly : f∈ enclave K
  gaugeLate : g∈ enclave K
  young : f.val ∈ Mρ z (early M) 0 10 0
  aged : g.val ∈ Mρ z M.ascX 10 0 1
  seam : Setting K (declination' Y H M) (early M) (M.ascX)
  mask_pos : 0 < ε
  mask (m:Side)(x:Fields ((K).c m)) : SU.group.chord (faceValue (onC ((K).c m) x.1) (wall M))≤ ε → f.val m x=0
  elector : Φ < ‖k₀ (f.val*g.val)‖
  first : Φ < ‖E s (f.val*g.val)‖
  cold : liftCap Y H V Q Qt 3 false (room 3) s (bidding Y H g)=0

variable {z:Window.Family}(F U: M.SpireBook (tent Y H) z)(R:Voice.Tonic M)
local notation "f" => (Giant.Voice.ink M K F R).val
local notation "g" => (Giant.Voice.burnish M K F U R).val
local notation "Z" => {wall M}

lemma wash_mark (r:ℕ){o : Finset Cover}{t: Window.Family}{a b c:ℕ}{T₀:Family (tent Y H)}
    (p: faceSites (wall M) ⊆ o) (h:T₀∈ Mρ t o a b c) :
    curved K {wall M} r T₀∈ Mρ t o a b c := by
   have he : scalar K (obstruct Z r)∈ Mρ t o 0 0 0:=
      (mul_one (scalar K (obstruct Z r))) ▸ (show _*1∈ Mρ t o 0 0 0 from
        Marble.entry (PhaseChoice.cutC _ _ _ (square_in M o p)) (.polo))
   simpa only [zero_add, PhaseChoice.curved] using Marble.grip he h

lemma design : f ∈ Mρ z M.ascY 0 10 0 := (Voice.incense M K F R).tone
lemma burning (p:M.Equatorial K z F U) : g ∈ Mρ z M.ascX 10 0 1 := (Voice.burn_pt M K F U p R).tone

lemma polished (r:ℕ): curved K Z r f ∈ Mρ z A 0 10 0:=
  wash_mark Y H M r (wall_in M) (Marble.wider (design Y H M F R) (early_in M))

def scented (r:ℕ) : Dome (tent Y H) := ⟨curved K Z r f, broadCompile K A
  ((show cameo 0 10=false from by decide) ▸ ((Marble.assign (polished Y H M F R r)).widen))⟩
-- Pure late presentation kept constant through selection. SpireBook actually in Prize.
def light : Dome (tent Y H) := ⟨g, broadCompile K M.Broad (Commission.blush (Giant.Voice.burnish M K F U R)).widen⟩
lemma bill_setting {a:ℝ}(p: Planet.Saturn Y H V Q Qt room s M F U χ R a): Setting K (declination' Y H M) (early M) (M.ascX):= by
   have he(j:Axis)(i:Cover)(h:i∈A):i j+(K).ℓ≤ ruler (K).B*declination' Y H M j :=
      le_trans (add_le_add_left (early_prior M i h j) _) ((p.offsets j).1 M.anchorY M.anchor_dawn) -- orientation next
   exact ⟨he,fun i=>(p.offsets i).2⟩
local notation "μ" => phaseRead Y H V Q Qt 3 (room 3) χ s
local notation "Zc·" r:max f₀:max => PhaseChoice.curved K {wall M} r f₀

lemma mask_approach {o:Finset Cover}(w:faceSites (wall M) ⊆ o) (x:Family (tent Y H))(a: InTest K true o false x)(p:CovCover K x) :
    Tendsto (fun r:ℕ=> (μ (Zc· r x))) atTop (𝓝 (μ x)) ∧
    Tendsto (fun r:ℕ=> E s (Zc· r x)) atTop (𝓝 (E s x)) := by
  let F₀:observable K true:= ⟨x,aux_test a,fun _=> p⟩
  let c:= SameCharacter.resident Y H V G 3 false (room 3) (asDisplay Y H V Q Qt 3 false (room 3) χ)
  have h:= square_in M o w
  have r(v:observable K true): markE Y H V G false 3 (room 3) c s (restore v)=μ v.val := (phase_read Y H V Q Qt 3 (room 3) s χ (restore v)).symm
  have hw:= prices_selected Y H V G 3 o Z s (room 3) h F₀ a c
  simp_rw [r] at hw; exact ⟨hw, prices_irr Y H V G 3 o Z s (room 3) h F₀ a⟩

variable (e: M.Equatorial (tent Y H) z F U) {b: ℝ}(p: Planet.Saturn Y H D.univ_ G.history G.clipped room s M F U χ R b)
include p e
set_option maxHeartbeats 840000 in
lemma mask_lights : ∀ᶠ r:ℕ in atTop, Signal Y H D G room χ s M (scented Y H M F R r) (light Y H M F U R) z (aperture r):= by
  let B':= early M ∪ M.ascX
  have he:= Voice.incense M K F R
  have hx:= Voice.burn_pt M K F U e R
  have hs: Neutral K f:= he.neutral; have hy: Neutral K g:= hx.neutral
  let Zf(r:ℕ):= scented Y H M F R r
  have eq (r:ℕ): curved K Z r (f*g)=(Zf r).val*g:= (mul_assoc _ _ _).symm
  have hf: InTest K true M.ascY false f:= (fire_mem M false K he).widen
  have hg: InTest K true M.ascX false g:= (fire_mem M true K hx).widen
  obtain ⟨ha,hb⟩:= mask_approach Y H D G room χ s M (o:= B') ((wall_in M).trans Finset.subset_union_left)
    (f*g) ((hf.mono ((early_in M).trans Finset.subset_union_left)).mul (hg.mono (Finset.subset_union_right))) (Commission.holdsM hs hy)
  let χ':= escort Y H V Q Qt 3 false (room 3) 3 (room 3) χ
  have hp:χ'=χ:= round_here Y H V Q Qt 3 false (room 3) χ
  have hv: Torrent.fare < ‖μ (f*g)‖:= hp ▸ p.selection_ 3 -- possible no θ
  have hr : ∀ᶠ r : ℕ in atTop, Φ < ‖phaseRead Y H V Q Qt 3 (room 3) χ s (curved K Z r (f*g))‖:= ha.norm.eventually (lt_mem_nhds hv)
  have ht : ∀ᶠ r : ℕ in atTop, Φ < ‖E s (curved K Z r (f*g))‖:= hb.norm.eventually (lt_mem_nhds p.conduct)
  filter_upwards [hr,ht] with r a c
  rw [eq r] at a c
  exact ⟨curve_color K Z r _ hs,hy,polished Y H M F R r,burning Y H M F U R e, bill_setting Y H D G room χ s M F U R p,
    aperture_pos r,fun m t p=>stops K Z r f m t (mem_singleton_self _) p,a,c,(p.lairs 3).unityCost Y H V Q Qt 3 (room 3) s (bidding Y H (light Y H M F U R)) rfl⟩
end Siam
end YM.CF.Buffered.Afterglow.Tower.Selection.Home
open YM.CF.Buffered.Afterglow.Tower.Selection.Home.Siam
#print axioms design
#print axioms mask_lights
