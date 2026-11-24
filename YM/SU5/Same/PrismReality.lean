import YM.SU5.Same.StrongColors
import YM.SU5.Same.Loft
/-! # Identification via Mink positive-time distributions in the limit Profile sector -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 310000
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
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open YM.SatinEdge.RealSheet Spectral Boundary Probe
variable (P:Spine)(x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "γ"=> P.cartage 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "λ'"=> P.enter 3 ξ
variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "Λ"=> P.profilesZ x V w
local notation "W"=> P.soldTrumpet A c r n w
local notation "ℒ"=> Lead.Clan
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
local notation "θ"=> (Ε).ℚmeasure.diagonal
variable (R:P.ThinArmada x A c r n w T V g h)(J:P.Ellis 3 x)(a b:Lead.Clan)
variable (F U:SampleDose)

abbrev polarBase (p:Vantage): E4:= (Cheer.shore (spacePart p)).val
lemma cart_plank (p:Vantage): planks (Ε) (polarBase p)= P.cartage 3 ξ p:= (ConePrice.translation _ _).trans (P.cart_space ..).symm

def realQuery (p:Vantage)(a b:Lead.Clan) : ℂ:= allMoments (Ε) (Λ a) (Λ b) (polarBase p) (p 3)
lemma query_score (p:Vantage): separationPrice (Ε) (Λ a) (Λ b) (polarBase p) (p 3)= P.pointPrism x V w p a b:= by rw [separationPrice,P.cart_plank]; rfl
include R in
lemma query_charged(p:Vantage)(v:0< p 3): P.realQuery x w V p a b=P.pointPrism x V w p a b:= by
 unfold realQuery; rw [← of_all_prices (Ε) (Λ a) (Λ b) (R.energy a).2.1 (R.energy b).2.1 _ _ v, P.query_score]

def measureAccording : CrossRead:= Matrix.of fun a b : Lead.Clan=> ∫ p:Vantage, ∫ q:Vantage,(F.val p:ℂ)*(U.val q:ℂ)*P.realQuery x w V (q-p) a b
variable (s k:ℕ)(K:P.Register)
local notation "Z" => P.FullPrismLab x A c r n w V g h T 1 F U reviewEarlierBox reviewLaterBox s k K
include J
-- apply to exactly those smears. No lookup away from these boxes in price
lemma exactlyMeasured(u:Z): P.measureAccording x w V F U = P.readPrism x V w 1 F U := by
 let t:=u.armada
 have p:backwardSite F 1:= fun a t=>by linarith only [((u.supports.1 t) (3:Axis) (Set.mem_univ _)).2, u.order.2.1]
 have q:forwardSite U 1:= fun a v=> u.order.2.2.trans (((u.supports.2 v) (3:Axis) (Set.mem_univ _)).1).le
 ext1 i j; rw [P.illuminate_price x A c r n w V g h T t 1 i j F U zero_lt_one p q]; unfold measureAccording; rw [Matrix.of_apply]
 apply integral_congr_ae (Eventually.of_forall fun a => integral_congr_ae (Eventually.of_forall fun b=>?_)); by_cases hx:F.val a=0; · simp [hx]
 by_cases hy: U.val b=0; · simp [hy]
 rw [P.query_charged x A c r n w V g h T t i j]; exact (by change 0<b 3-a 3; linarith only [p a (subset_closure hx),q b (subset_closure hy)]) -- wrong dsimp?
omit J
include R
lemma strict_price(a b: ℒ)(t:ℂ): ∀ᵐ p∂ (homeMeasure (Ε) (chords (Λ a) (Λ b) t)), (0:ℝ) < p (3:Axis):=by
 apply home_strict_time (Ε); intro i
 have he(z:ℒ): (Ε).ℚmeasure.region (_root_.YM.Six.night) ((Λ z) (minute i:ℝ))=0:=((R.energy z).2.2 _ (minute_wake i)).2.2 -- NNReal coercion, .2.2 path? inspect
 change (Ε).ℚmeasure.region (_root_.YM.Six.night) (chords (Λ a) (Λ b) t _)=0
 unfold chords; rw [map_add,map_smul,he a,he b,smul_zero,zero_add]
-- Problem local `w` stencil shadow! change scalar name
omit R
lemma edgeLI (u:Z)(p:∀ a:ℒ,TemperedAtEdge G (Λ a)): ∃ f:Test4, LinearIndependent ℂ (fun a:ℒ=> _root_.YM.SatinEdge.RealSheet.awake (Ε) (Λ a) (p a) f):= by
 have v(i:ℒ):= (u.armada.energy i).2.1; obtain ⟨a,a',b,b',i,-,-,e,f⟩:=u.keeps.centers
 let z:=(b-a); let t:= z 3 / 2; have hz:0<t:=by change 0<(b 3 - a 3)/2; have hv:= thin_separation a b a' b' 3; linarith
 exact colored_rank (Ε) (Λ) p v t hz (γ z) e

local notation "δ" => (𝓝[>] (0:ℝ))
/-- Realizations for these smears, a partial (real Mink) vacuum sector.

*The same anchor F,U*. Construction doesn't take Mink-real probes as input
when certifying this Euclidean interaction price. Instead obtains real-time
**distributions**, and spectral/complextemporal continuation verification, so
can consult THE SAME ordered test of the CP18 smearing-- including all-axis
separation in that price and rank-six. Not asserting causal property!

* In combination with `EdgeLab`: FullPrismLab and registry of fixed probe supports,
  compare positive-time numbers with this same state, via the EXACT
  imaginary gap, even though it has real-time vacuum distributions and is
  not a time-padded representative. No positive smoothing asserted at edge.
* Real test tied-pair prices are inside `W` arity2 system, no heating or t-shift
  imposed in their *Mink* calculation. `loft`: the analytic identification,
  no strip estimate at real edge. Use also `at_paint` and `of_all_prices`: same
  complex and relative-real values as requested. Test spectral measures directly
  with `momentPrice`. They are in `homeMeasure`, unpadded; see `AllSeasons,
  BrightMeasure`. `strict_price` for spectrum in positive TIME only. Rank really
  held in this interpretation (auxiliary Schwartz f chosen here only checks
  that the limiting prices at offset 0 on `awake` didn't become linearly
  dependent). Not spatial or real-local interaction assertions about this f.
* No continuity/generating sector assumption on CP18 unprojected H.
* Not assertion about all CP18 realizations w/o M3p qualifications, nor a
  result about more than the unpadded interpretations in the statement. -/
structure AtZeroHeat (K₀:ℒ→ Test4→L[ℂ] G) (W₀:ℒ→ ℒ→ Test4→L[ℂ] ℂ) : Prop where
 forecasts : ∃ p:∀ i:ℒ, TemperedAtEdge G (Λ i), (∀ i,K₀ i=_root_.YM.SatinEdge.RealSheet.awake (Ε) (Λ i) (p i))∧ ∀ i j,W₀ i j=feelCross (Ε) (Λ i) (Λ j) (p i) (p j)
 calendar : ∀ (a b:ℒ) (v:ℂ), (homeMeasure (Ε) (chords (Λ a) (Λ b) v)).HasTemperateGrowth ∧
              (∀ t:ℝ≥0,0<t→ (θ) (chords (Λ a) (Λ b) v (t:ℝ))=(homeMeasure (Ε) (chords (Λ a) (Λ b) v)).withDensity (coloringE 3 t)) ∧
              ∀ᵐ p∂(homeMeasure (Ε) (chords (Λ a) (Λ b) v)), (0:ℝ) < p (3:Axis)
 curve : ∀ (a b:ℒ)(t:Vantage)(v:0 < t 3), P.pointPrism x V w t a b = P.realQuery x w V t a b -- spectral
 funding : P.measureAccording x w V F U=P.readPrism x V w 1 F U
 integrable_interior : ∀ (a b:ℒ)(u:E4)(t:ℝ)(v:0<t)(z:ℂ), Integrable (fun p=> (↑(Real.exp (-t*p 3)):ℂ) * Probe.plane p u) (homeMeasure (Ε) (chords (Λ a) (Λ b) z))
 pays_pair : ∀ (a b:ℒ)(u:E4)(t:ℝ)(v:0<t), separationPrice (Ε) (Λ a) (Λ b) u t=allMoments (Ε) (Λ a) (Λ b) u t -- incl complex via at_paint
 loft : ∀ (a b:ℒ)(u:E4), AnalyticOnNhd ℂ (paintedFrom (Ε) (Λ a) (Λ b) u) {z:ℂ|0< z.im}
 point : ∀ (a b:ℒ)(u:Vantage)(t:0 < u (3:Axis)),paintedFrom (Ε) (Λ a) (Λ b) (polarBase u) ((u 3)*Complex.I)= P.pointPrism x V w u a b
 surface : ∀ (a b:ℒ)(f:Test4), Tendsto (fun t:ℝ=>∫ y:E4, f y * separationPrice (Ε) (Λ a) (Λ b) y t) (𝓝[>] 0) (𝓝 (W₀ a b f))
 matchTest : ∀ (a b:ℒ)(f g:Test4), W₀ a b (tieAt f g)= inner ℂ (K₀ a f) (K₀ b g)
 translate : ∀ (a:ℒ)(f:Test4)(u:E4), K₀ a (ahead u f)=(Ε).unit.translation u (K₀ a f)
 boundary : ∀ (a:ℒ)(f:Test4),
       (∀ t:ℝ,0<t→ Tendsto (fun i=> ∫ b, f b • ((Ε).unit.translation b (P.cradleG x (W a i) B[a,i] t))) atTop (𝓝 (∫ b, f b • ((Ε).unit.translation b ((Λ a) t))))) ∧
       Tendsto (fun t:ℝ=> ∫ b, f b • ((Ε).unit.translation b ((Λ a) t))) (𝓝[>] 0) (𝓝 (K₀ a f))
 sense : ∃ f:Test4, LinearIndependent ℂ (fun a=> K₀ a f) -- interpretation *after* width then heat consumed
include J
lemma real_order (p:∀ i:ℒ,TemperedAtEdge G (Λ i))(q:Z): P.AtZeroHeat x A c r n w V T F U (fun z:ℒ=> _root_.YM.SatinEdge.RealSheet.awake (Ε) (Λ z) (p z)) (fun i j:ℒ=> feelCross (Ε) (Λ i) (Λ j) (p i) (p j)):=by
 let R:= q.armada
 let hX(z:ℒ):= (R.energy z).2.1
 refine {
   forecasts:= ⟨p,fun _=>rfl,fun _ _=>rfl⟩
   pays_pair:=fun i j u t v=> of_all_prices (Ε) _ _ (hX i) (hX j) u t v
   calendar:=fun i j v=> ?_
   integrable_interior:=fun i j u t p z=> strict_coat_at (Ε) (chords (Λ i) (Λ j) z) (market_chords (Ε) (Λ i) (Λ j) (hX i) (hX j) z) u t p
   curve:=fun _ _ _ p=> (query_charged _ _ _ _ _ _ _ _ _ _ _ R _ _ _ p).symm
   funding:=P.exactlyMeasured x A c r n w V g h T J F U s k K q
   loft:=fun i j=> shade_holo (Ε) (Λ i) (Λ j) (hX i) (hX j)
   point:=fun i j u _=> (at_paint (Ε) ..).trans (P.query_score x w V i j u)
   surface:=fun i j f=> feeling (Ε) (Λ i) (Λ j) (hX i) (hX j) (p i) (p j) f
   matchTest:=fun i j=> tie_prices (Ε) (Λ i) (Λ j) (hX i) (hX j) (p i) (p j)
   translate:= fun i f u=> (transportation (Ε) (Λ i) (p i) (hX i) u f).symm
   boundary:=fun a f=>?_
   sense:=P.edgeLI x A c r n w V g h T F U s k K q p }
 · exact ⟨tempered_home (Ε) _ (boundary_chords (Λ i) (Λ j) v (p i) (p j)), fun t u=> exact_density (Ε) _ (market_chords (Ε) (Λ i) (Λ j) (hX i) (hX j) v) t u, P.strict_price x A c r n w V g h T R i j v⟩
 simp_rw [←collect_eq]; exact ⟨fun t u=> ((collect (Ε) f).continuous.tendsto _).comp (q.armada.heated_points a t u).2,rise_heat (Ε) _ (p a) (hX a) f⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.real_order
