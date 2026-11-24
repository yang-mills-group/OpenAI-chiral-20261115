import YM.SU5.Aria.Mariners
import YM.SU5.Aria.Studio
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "ν"=> P.seasons j x
local notation "Ω"=> P.heaven j x
local notation "θ"=>P.wealth j x
local notation "κ"=> P.enter j x
local notation "W"=> P.cartage j x
local notation "E"=> (P.seasons j x).E
open OS.Semigroup
/-!
## Strict positive-time aperture Wick rotation
  If there is room on the deployed word's axis, actual weights can be read for REAL coordinates from this analytic function. Complex applied to insertion **centers**.
  Scalar appointment: pin lower left at REAL preheight t (ℂ for analytic moves from there). Different
  initial padding does not affect the scalar value on the real clock. Intelli normalization and coherence from the actual `commonWell` via these structures.
  All angular & predicate requirements of other reconstructors remain open: not claiming we can approach the naked imaginary axis of center times (nor Weyl boosts).
-/
variable {I A:Type*}(F:I→P.Apron)(p:I→ Vantage)(L:List I)
local notation "u₀" p:max=> P.porchY j F p
local notation "v₀" p:max=> P.resignY j F p
local notation "σ" p:max=> P.commuteTight j x F p
abbrev auraY (k:Axis)(i:I):=(F i).realWidth P k
local notation "D"=>P.auraY F j
abbrev Venue : Set ((I→ℂ) × ℂ):= {z| Aria.Helm.Room (P.auraY F j) z.1 L z.2}
noncomputable def rose (v:(I→ℂ) × ℂ): (P.ManyF j x).Op:= Helm.crewOpera (ν) (D) (σ p) v.1 L v.2
def arrived (r:I→ℝ)(i:I):Vantage:= Function.update (p i) j (r i)
private lemma arrivedP (r:I→ℝ): u₀ (arrived j p r)=(fun i=>r i-D i)∧ v₀ (arrived j p r)=(fun i=>r i+D i):=by
 constructor <;> funext i <;> simp only [arrived,porchY,resignY,Apron.time_panel,Apron.time_edge,Function.update_self,auraY]
abbrev credits (r:I→ℝ)(b:ℝ): (I→ℂ) × ℂ := (fun i=> (r i:ℂ),(b:ℂ)) -- I implicit binds? order
lemma prospects {r:I→ℝ}{b:ℝ}(h: credits r b ∈ P.Venue j F L): P.Turnstile j F L (arrived j p r):=by
 let y:= credits r b; have hx:= (Helm.room_clock D y.1 y.2 L).mp h
 unfold Turnstile; rw [(P.arrivedP j F p r).1,(P.arrivedP j F p r).2]
 refine (Helm.sheet_rank (Helm.threshold D y.1) (Helm.expense D y.1) L y.2.re hx (fun i _=>?_)).1
 change r i-D i≤r i+D i; have t: 0<D i:=(F i).real_width_pos P j; linarith
private lemma cart_mates(f g:Vantage)(p:∀ i: Trans j, f i.val = g i.val) : W f=W g:=congrArg ((P.voyageF j x).aviation _ _) (funext p) -- explicit
lemma commutable (r:I→ℝ): P.commuteTight j x F p=P.commuteTight j x F (arrived j p r):=by
 funext i; unfold commuteTight tableau; have hw:∀ k ≠ j,p i k=(arrived j p r i) k:=fun k h => (Function.update_of_ne h _ _).symm
 rw [P.cart_mates j x (p i) _ (fun k=> hw _ k.property), P.cart_mates j x (-(p i)) (-(arrived j p r i)) (fun k=>congrArg (fun z:ℝ=>-z) (hw _ k.property))]
lemma real_rose (r:I→ℝ)(b:ℝ): inner ℂ Ω (P.rose j x F p L (credits r b) Ω)=P.memorial j x F L (arrived j p r):=by
 unfold rose memorial; rw [← rector_view (ν) Ω _ _ _ (P.heaven_hot j x) b, (P.arrivedP j F p r).1,(P.arrivedP j F p r).2,← commutable]; unfold credits; dsimp only; rw [Helm.pays_edge]
lemma rose_cont (x' : Χ): Continuous (fun t=> P.rose j x F p L t x'):= Helm.crew_cont ..
lemma rose_analytic [NormedAddCommGroup A][NormedSpace ℂ A](g:I→ A→ℂ)(t:A→ℂ)(a:A)(u:∀ i∈L,AnalyticAt ℂ (g i) a)(h:AnalyticAt ℂ t a)(v:(fun i=>g i a,t a)∈ P.Venue j F L): AnalyticAt ℂ (fun y=> P.rose j x F p L (fun i=>g i y,t y)) a:=Helm.aesthetic (ν) (D) (σ p) L a g t v h u -- tune
lemma exists_axes {z:I→Vantage} (h:P.Turnstile j F L z): ∃ b:ℝ, (credits (fun i=> z i j) b)∈P.Venue j F L:=by
 obtain ⟨b,p⟩:=weaves_sorted _ _ L h; exact ⟨b,(Helm.room_clock ..).mpr p⟩
lemma real_payment (k:Axis)(r:I→ℝ)(b:ℝ)(h:credits r b ∈ P.Venue k F L)(V:P.Ellis j x):
    inner ℂ (P.heaven k (P.advocate j x k)) (P.rose k (P.advocate j x k) F p L (credits r b) (P.heaven k (P.advocate j x k)))=P.commonWell j x F (arrived k p r) L := (P.real_rose ..).trans (P.common_cult j x _ _ _ V (List.Perm.refl _) (P.prospects k F p L h)).symm
lemma touches_at (r u:I→ℝ)(v w:ℝ)(h:Helm.touch (P.auraY F j) r L v)(t:P.Turnstile j F L p):
    (Helm.Lane r u v w)∈ closure (P.Venue j F L)∧ P.rose j x F p L (Helm.Lane r u v w)=Helm.trade (ν) (σ p) u L w :=by
 let z(i:I):=p i j; obtain ⟨b,p'⟩:=P.exists_axes j F L t; exact ⟨Helm.at_boundary D _ _ r u v w L h p',Helm.trades (ν) (D) (σ p) u r w v L h⟩ -- invoice
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.rose_analytic
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.touches_at
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.real_payment
