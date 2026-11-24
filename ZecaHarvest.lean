import ZecaGallery
import ZecaGerm
import YM.SU5.FiniteGaugeData.Poin.Seal
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


open Poin Celeritas Land Leal Breve Poin.Gem Boundary Probe Flute Vp.Folio Seld.Vp Seld.Vp.Luft _root_.YM.CF.Buffered.Afterglow.Hierarchy.Vp.Caps
variable {ι:Type}{H:Hilbert}(S:OS.Semigroup H timeAxis)(G:Canopy H ι)
   (Ω:Bench S)(hΩ:∀x:E4,M S x Ω.val=Ω.val)
include hΩ
structure Frescoes (X:Boundary.Action H):Prop where
 histories : G.Earned S Ω
 w : G.Arrival S Ω X
theorem harvest (f:Filled S G Ω.val)(v:‖Ω.val‖=1)(D:G.Tile S Ω) :
     ∃ X,Frescoes S G Ω X:=by
   let k:=petals S G Ω hΩ f D
   have p:S.ℚmeasure.region Mink.coneᶜ=0:=by
      have y:=k; unfold Celeritas.Cinema at y
      rw [timeCone] at y
      exact y
   let g := fun r=>Gem.Lobby S k r
   obtain ⟨X,x⟩:=Canopy.arrivals G S Ω hΩ g D (climb_all S G Ω hΩ f)
                        v p (Fresco.fresco S G Ω hΩ D f)
   exact ⟨X, G.eldership _ _ hΩ g D,x⟩

/-- Bare survival of belief about uniqueness of translation-invariant vector in H. -/
abbrev Anchor (Ω:H.space) := ∀ x:H,(∀ p:E4,M S p x=x)→ ∃ z:ℂ,x=z • Ω
local notation "T"=>springs S G Ω.val
local notation "N"=>chapel S G Ω.val
local notation "φ"=>saint S G Ω hΩ
lemma sturdy (p:Anchor S Ω.val): Anchor T (φ).val:=by
 intro x q
 obtain ⟨z,e⟩:=p x.val (fun y=>by
   have w: (Cove S G Ω.val).subtypeL _=M S y x.val:=(crystalline S G Ω.val).trans y x
   rw [q y] at w;exact w.symm)
 exact ⟨z,Subtype.ext e⟩

theorem harvested (e:‖Ω.val‖=1)(p:G.Tile S Ω):
    ∃ X, Frescoes T N φ X:=
   harvest T N φ (safer S G Ω hΩ) (pilgrims S G Ω.val) e (pilgrims_paid S G Ω hΩ p)
#print axioms harvested
