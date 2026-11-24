import SatinFixedContrastNovember4
import YM.SU5.Assay.DuoNotice
import YM.SU5.Assay.Campaign
import YM.SU5.Assay.Coin
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Six Aria Ballad
variable {P:Spine}{R:P.Register}{x:P.Spectrum0 3}{s n:ℕ}{D N:Doorway}{σ:Orders}{F G:SampleDose}
namespace Fresco
open OS.Semigroup
/-!
 Fixed commitment: same original stock and stutter; every refinement pose on
 that expense pays even the marginal stencil receipts. Operator brew for this
 exact commitment (not re-installing the stencil at a different physical width).
-/
variable (h:P.Fresco R x s n D N σ F G)(Z W:Lead.Clan)
include h
local notation "A"=> P.RTest Z s n
local notation "B"=> P.FTest W s n
local notation "l"=> (P.bookPair Z n).transcribe (P.reflectTest 3)
local notation "m"=>P.bookPair W n
local notation "β"=>P.base 3 x
local notation "ψ"=>P.coffee 3 x
local notation "ρ"=>P.rawSlot 3 x
local notation "Vac"=>P.colorZero 3 x
local notation "Ω"=>P.heaven 3 x
local notation "M"=>P.arrayReading x s n (D.turnCut N) F G
local notation "μ"=>P.arrayFine x s n
local notation "w"=>P.probeWidth s n 3

lemma sold (t:ℕ)(p:s ≤ t):P.DuoNotice x t D A Z.2 (l) F N B W.2 (m) G:=by
 have g:= (P.experiment_first Z n s h.taps.extent).kiss 3
 have b:P.Notice x t N B W.2 (m) G := (P.experiment_first W n s h.taps.extent).sell x R p h.fixed2 h.taps.right (h.taps.bills t p).2
 exact (g.sell x R p h.fixed1 h.taps.left (h.taps.bills t p).1).beside R b h.taps.sep

lemma opposition (t:ℕ)(p:s ≤ t):
 P.PriorBoth x t A B F G (l) (m)=0∧ P.paperSplit t x (P.markPair A B t F.val G.val)=0:=
 ⟨(h.sold Z W t p).prior,(h.sold Z W t p).canon.2⟩

lemma old_fee (a b c:ℝ) (u:Walled 3 F a b w)(v:Walled 3 G b c w)(t:ℕ)(p:s ≤ t):
 μ t F G Z W=P.spiritBoth R x t A F B G ∧ μ t F G Z W=inner ℂ (Vac) ((ρ t A a b F * ρ t B b c G) (Vac)):=by
 have r: μ t F G Z W=P.spiritBoth R x t A F B G:=P.reviewWardRaw ..
 exact ⟨r, (h.sold Z W t p).stance _ a b c x u v |>.price.symm⟩

lemma old_brew (a b c:ℝ) (u:Walled 3 F a b w)(v:Walled 3 G b c w):
 P.Rehearses 3 x (fun t=>ρ t A a b F * ρ t B b c G) atTop (ψ (β A) a b F * ψ (β B) b c G) ∧
 (M) Z W= inner ℂ (Ω) ((ψ (β A) a b F * ψ (β B) b c G) (Ω)):=by
 have g:=P.grid_base _ _ (P.metered 3 x R)
 have e: Tendsto (fun t=>μ t F G Z W) atTop (𝓝 ((M) Z W)):=by
   let f(T:Matrix Lead.Clan Lead.Clan ℂ):=T Z W
   have cf:Continuous f:=(continuous_apply W).comp (continuous_apply Z)
   exact (cf.tendsto _).comp h.paid.steady
 have t:=(g A a b F).mul (g B b c G)
 exact ⟨t,tendsto_nhds_unique (e.congr' ((eventually_ge_atTop s).mono fun i p=> (h.old_fee Z W a b c u v i p).2)) t.price⟩
lemma old_walls : let b:=D.turnCut N; Walled 3 F (D.lower 3) b w ∧ Walled 3 G b (N.upper 3) w:=
 ⟨Doorway.first h.taps.left h.fixed1 h.taps.sep,Doorway.second h.taps.right h.fixed2 h.taps.sep⟩
end Fresco
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
