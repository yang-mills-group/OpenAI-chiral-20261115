import SU5SatinFixedProbesAndBareFlavorNovember6
import YM.SU5.Registration.M12
import YM.SU5.Registration.Momenta.Culture
/-!
 # M13 Full locality, spectral, covariance and symbol-to-observable over M4 in raster hypothesis. 
 Keep F₀ and support actual F/U pair by their assignments thanks to M9 stencil registration.
 Also can independently investigate any family extension to justify Raster without assuming
 those estimates already (we didn't buy one covering even the M4 fields).
 Analytic proof consumer from exact RasterPrice. `all_rooms`. Uses `Momenta` files. Can supply
 citizens attached to one M4Tuple and read all six paths from parent. Not yet asserting solves
 existence goals. Still requiring those new angular estimates on these fields or other mode, and
 for theory yet more physical content measurements even on this x. No claim of (116) on whole
 point field model. Needs interaction costs: use M5--9 diagnostic.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
variable (K : P.Register) (c r : ℕ→ℕ) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose) (A : ℕ→P.Apron) (n : ℕ→ℕ) (w : Lead.Clan → Prism)
    (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (g h : ℕ)
    (X : P.HandleWith x c r A n)
    (Y : Lead.Clan → Test4→L[ℂ] (P.ManyF 3 (P.advocate 3 x 3))) (Z : Lead.Clan → Lead.Clan → Boundary.Distn E4)
local notation "Μ" => M4Tuple P K c r x R i₀ F U A n w V g h X Y Z
local notation "Λ" => P.profilesZ x V w
local notation "ρ" => 𝓝[>] (0:ℝ≥0)
local notation "B" => P.pointBill x A c r n w
local notation "W" a:max => P.soldTrumpet A c r n w a
local notation "G₀" a:max => P.gaugeTrumpet A c r n w a
variable (F₀: M4Tuple P K c r x R i₀ F U A n w V g h X Y Z)
universe ν
variable (p:PlanetaryG.{ν} P A)(T':∀ x:P.Spectrum0 3,P.Guest x c r A n)
open Swatch
local notation "aK"=> P.SalonBasis A
local notation "Zq"=> Swatch.ordinary A
local notation "Zw" a:max=> Swatch.ordinary (W a)
local notation "Zg" a:max=> Swatch.ordinary (G₀ a)
local notation "Zl" j:max=> Swatch.ordinary (P.registeredStamp A c r n w j)
open SatinWFixed Carton WView HelioRoof
-- hypothesis used further on Hpt rotations/covariant operator fields. 
section economy
variable {I:Type*}(B':I→P.Swatch)(tp:∀ i,(B' i).WPermit x 3) (R':Courts (epaulets I))
variable (S':P.RasterPrice x B' R') (h':R'.Parley (r_star I))
local notation "Y₀"=> P.store x B' tp
local notation "E"=> epaulets I
local notation "T"=> (P.store x B' tp).joinT
local notation "SE" => P.registeredField x A c r n w

-- Lab locations: eventually in ARBITRARY real-box shrinks around positions tested for Eu charges,
-- on this P placement. Gauge singlets exact per slot & assembly. No claim determining arbitrary Smear
-- on old coarse lattice test; use `full_visit_limit` & `WPermit` scopes of M8-12.
open Filter
lemma pace_margin (F₁:ℕ→P.Apron)(p:∀ k:Axis,Tendsto (fun i=>(F₁ i).allowance P k) atTop (𝓝 0))(q:Vantage) (Q:ℕ→Vantage)(t:Tendsto Q atTop (𝓝 q)) (v:ℕ→ℕ)(t':Tendsto v atTop atTop) (ε:ℝ)(h:0<ε): ∀ᶠ i in atTop, (F₁ (v i)).scenery P (Q i) ⊆ {x|∀ j:Axis, |x j- 2*q j|<ε}:=by
 have he(j:Axis): Tendsto (fun i=>2*((F₁ (v i)).realWidth P j)+|2*Q i j-2*q j|) atTop (𝓝 0):=by
     have ht:= tendsto_pi_nhds.mp t j; have hv:= NNReal.tendsto_coe.mpr ((p j).comp t');
     have h':Tendsto (fun i=> (F₁ (v i)).realWidth P j) atTop (𝓝 0):=by
        simp_rw [Apron.width_real]; exact hv
     have h'':Tendsto (fun i=> |(2:ℝ)*Q i j-2*q j|) atTop (𝓝 0):=by simpa only [_root_.sub_self, _root_.abs_zero] using (show Tendsto _ _ _ from (((ht.const_mul 2).sub_const (2*q j)).abs))
     simpa using (h'.const_mul 2).add h''
 filter_upwards [eventually_all.mpr (fun j=> (he j).eventually (gt_mem_nhds h))] with i z x t j; specialize z j; change 2*((F₁ (v i)).realWidth P j)+|2*Q i j-2*q j| < ε at z
 rw [show x j-2*q j=x j-2*Q i j+(2*Q i j-2*q j) from by ring]; exact lt_of_le_of_lt ((abs_add_le ..).trans (add_le_add_left (t j) _)) z
open Swatch
abbrev tinyGallery {k:ℕ}(ε:ℝ)(p:Points k): Set RSpace:= {x|∃ i:Fin k, ∀ j:Axis, |x j- 2*(qua p i j)|<ε}
include K tp
lemma stroll_pays {k:ℕ}(p:Points k)(v:Fin k→ E)(σ:ℕ→ Fin k→ℕ)(r:ℕ→Fin k→ Cover)(w₀:ℕ→ℕ) (v₀:P.SigReach B' v p σ r w₀)(h:∀ i, Tendsto (fun k=>σ k i) atTop atTop) (ε:ℝ)(he:0<ε): ∀ᶠ i in atTop, P.sigVisit B' v (σ i) (r i) (w₀ i) ∈ keep P.par P.width (w₀ i) P.calibration true (tinyGallery ε p):=by
 let A(f:Fin k→I×Bool)(j:Fin k):= P.school B' (f j)
 have hv(f:Fin k→I×Bool): ∀ᶠ i in atTop, ∀ j:Fin k, ((A f j).fieldA (σ i j)).scenery P (P.laysM (P.vtile (w₀ i) (r i j))) ⊆ tinyGallery ε p:=by
    refine eventually_all.mpr (fun j:Fin k=>?_); let g:= (A f j).fieldA; refine (P.pace_margin g (P.praise x B' (f j) tp).thin (qua p j) _ (v₀.time3 j) (fun i=> σ i j) (h j) ε he).mono fun t b z hz=>?_ ; exact ⟨j,b hz⟩
 filter_upwards [(eventually_all_finset (I:=seatPlan v) ..).mpr (fun i _=> hv i),v₀.prices] with i t y; apply Subalgebra.sum_mem; intro f h
 apply Subalgebra.smul_mem; unfold fullVisit; apply Subalgebra.smul_mem; exact P.slots_home (w₀ i) K _ _ _ (fun j _=> y _ h j) (fun j _=> t f h j)
-- omit: retained in further M4 parameters. 
include F₀ S' h'
-- Choosing F W doesn't require covariance. Now obtain full locality on these symbols. Includes
-- also use with operator results (chalet,regional_ritual,etc. in Momenta). Keeps on our B'.
theorem all_rooms (φ:InkWaves (epaulets I))(Rz:WView (epaulets I))(E0:InkPort (Y₀) φ Rz) : Rz.conical ∧ Rz.Localizes ∧ R'.Carriage φ ∧ (Palette.ticket Palette.blanket Rz).FullBody φ ∧
 ∃ V':Boundary.Action (Y₀).station,
  (Y₀).Joins R' V' ∧ V'.orbit=T ∧ V'.orbit.Spectrum ((Y₀).joinT.P) ∧
  (T).P.region Mink.coneᶜ=0 ∧ (∀ v:(Y₀).station,(∀ k:E4, (T).translation k v=v)→ v∈ Submodule.span ℂ {(Y₀).engaged []}) ∧
 (∀ (x y:epaulets I)(f g:Test4), Fields.causal f g→ Commute ((Y₀).pointMap x f) ((Y₀).pointMap y g)):= by
 obtain ⟨ht,hp,P',h₀,etc,σ,y,k⟩:= P.relatable x K c r R i₀ F U A n w V g h X Y Z F₀ B' tp R' S' h' φ Rz E0; let hg:= WView.isLocal E0 ht; exact ⟨hp,hg,ht,spectrum_paid E0 ht,P',h₀,etc,σ,y,k,fun x' y' f g' p=> (Y₀).supported (r_star I) E0 (P.preserves_income x B' tp) hg x' y' f g' p⟩
omit S' h'
include p T'
-- now for the actual M4 stencils map. ANY extension including parent. allows rotations for
-- rank/chiral analysis to consume `p.field*` over precisely this family if granted.
variable (q:P.CapBacked x A c r n w)(i:I)(b:B' i=Swatch.ordinary A)
local notation "u'"=> P.preserves_income x B' tp
local notation "D₀"=> (P.store x B' tp).retreat
local notation "Ω'"=> (P.store x B' tp).pointRoot
-- at all operator words in sector-budget domain, attach M4 Field (on G).
noncomputable abbrev instrumentBody (j:Instrument)(f:Test4): (Y₀).retreat→ₗ[ℂ] (Y₀).retreat:= (Y₀).chalet (r_star I) u' (sortTicket w i j f).1 (sortTicket w i j f).2
include b
lemma fitsBody (j:Instrument)(f:Test4)(x':D₀): (Y₀).charm (P.instrumentBody x w B' tp i j f x')= P.registeredField x A c r n w q j f ((Y₀).charm x'):= by
 rw [← P.attachTicket x K c r R i₀ F U A n w V g h X Y Z F₀ p T' B' tp q i b]; rfl
omit b p T' F₀ K
include S' R
-- spacelike result even on radial rooms (intersection). Don't assert rel actions on G beyond this sector.
lemma instrumentBody_local (φ:InkWaves (epaulets I))(Rz:WView (epaulets I))(E0:InkPort (Y₀) φ Rz)(j k:Instrument)(f₁ f₂:Test4)(e:Fields.causal f₁ f₂) (w₁:D₀):
 P.instrumentBody x w B' tp i j f₁ (P.instrumentBody x w B' tp i k f₂ w₁)= P.instrumentBody x w B' tp i k f₂ (P.instrumentBody x w B' tp i j f₁ w₁):= by
 let j':=sortTicket w i j f₁; let k':=sortTicket w i k f₂; exact (Y₀).regional_ritual (r_star I) u' E0 R' ((P.raster_carriages x B' tp φ Rz E0 R R').1 S') j'.1 k'.1 j'.2 k'.2 (fun i' h l k=> e _ (retest_ticket w i _ f₁ h) _ (retest_ticket w i _ f₂ k)) w₁
end economy
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
