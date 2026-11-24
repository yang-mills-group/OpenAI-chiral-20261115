import SatinThinCollege
import SatinThinTripods
import SatinThinCardiff
import YM.SU5.Regis.Legend
import YM.SU5.Hiro.Ladles
import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
variable (z:PlaqAxes→ℝ) {I U:Type} [Fintype I] [Fintype U] (T:Trip I)(s:ℕ)(b:U→ ℕ)
local notation "xθ"=> hat P.par.R.L P.par.x s
/-! # affine pose bill and count. -/
variable (A:ℝ)
local notation "M"=> P.par
open BProof Py.Rate.Pannier Py.Rate.LocalLimit.Papal
open Signal.Interval (separationCost)
open Lattice
/-! # All heights in a paid stream. `Vetted` budget g for any such stencil.
    Use probabilities already of preparation, with permit in ShelterCost (earned cp6 etc.). -/
local notation "νW"=> Lamour.Bridge.Celeste.breadth 0 noonFrame
open Pressure.Worth Pressure.Worth.Pays
variable (v v₀:ℝ)
lemma shore_mul (t u x:ℝ): trailℓ t x*trailℓ u x=trailℓ (t+u) x:=by unfold trailℓ; rw [coin_mul]; norm_num
lemma sun_crest (c:ℕ) (h0:0<A) (u:0< v) (h:v₀-v > (A*c+A)*2): ∀ᶠ s:ℕ in atTop,P.mixCost z s A c ≤ (scout P.par v₀ s:ℝ)*(trailℓ (-v) (hat P.par.R.L P.par.x s)/3):=by
 let z':= (A*c+A)*2; let H(t:ℝ):= sunRank P.par.K.top.clip (padC z SU.group A t) c
 have e: Pays 0 z' 0 H :=by
    have h':0<z':=by unfold z'; positivity
    refine scale (8* Real.exp ((Real.pi/2)^2/2)) (Pays.plus (Pays.merit (constant 1) (Or.inr (Or.inl (show _ ∧ _ from ⟨rfl,h'⟩)))) ?_)
    simpa using Pays.pot (sun2 (q:=P.par.K.top.clip) (G:=SU.group) z A c h0) 2
 filter_upwards [(turnover P.par).eventually (Pays.compare (1/3) (by norm_num) e (w:=0) (p:=v₀-v) (q:=0) (Or.inr (Or.inl ⟨rfl,h⟩)))] with k g
 let x:=hat P.par.R.L P.par.x k; let u:=trailℓ (-v) x; have he: H x*3 ≤ trailℓ (v₀-v) x:=by change |_| ≤ (1/3)* trailℓ (v₀-v) x at g; linarith only [g,le_abs_self (H x)]
 rw [sub_eq_add_neg,←shore_mul] at he; have h' : trailℓ v₀ x ≤ ↑(scout P.par v₀ k):= Nat.le_ceil _;
 change H x ≤ _ * (_ / 3); linarith only [he,mul_le_mul_of_nonneg_right h' (show 0≤u from (trainℓ ..).le)] -- tune
-- purchase additional counts with a fixed larger scope
abbrev debt_length (p k:ℕ):ℕ:= (p+8*P.par.block.val*(P.numU p+k)+νW)*2
lemma tollP (h:0< v₀): BunchData P.par (fun s=> P.debt_length (scout P.par v₀ s) (scout P.par v₀ s)):=by
 let g(x:ℝ):= Nat.ceil (trailℓ v₀ x); have hz:Pays 0 v₀ 0 (fun x=> (g x:ℝ)):= helmBound v₀ h; have hc(c:ℝ):Pays 0 v₀ 0 (fun _=>c):= Pays.merit (constant c) (Or.inr (Or.inl ⟨rfl,h⟩))
 have ht: Pays 0 v₀ 0 (fun x:ℝ=>(P.debt_length (g x) (g x):ℝ)):=by
    unfold debt_length numU; push_cast; exact Pays.right 2 (Pays.plus (Pays.plus hz (Pays.scale _ (Pays.plus (Pays.plus (Pays.plus (hc _) hz) (hc _)) hz))) (hc _))
 exact ⟨v₀+1,by linarith only [h], (turnover P.par).eventually (leap ht (w:=0) (q:=0) (p:=v₀+1) (by right; left; constructor; rfl; linarith))⟩
variable {C:ℝ}(Q':∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k)
include Q'
lemma variance_cost_at [Nonempty I](h0:(4:ℝ)*Fintype.card I + 5 + v < A) (u:0< v) (h:v₀-v > (A*Fintype.card I+A)*2)(d:ℝ) :∀ᶠ s:ℕ in atTop, ∀ (T:Trip I),CoversT T (scout P.par v₀ s) → |P.parish z T s A| ≤ d →
  P.stipend j s (P.visitLedger z T s) (P.parish z T s A:ℂ) ≤ trailℓ (-v) (hat P.par.R.L P.par.x s):=by
 let i(s:ℕ):=scout M v₀ s
 have hj := Nat.cast_nonneg (α:=ℝ) (Fintype.card I)
 have hn:0<A:=by linarith only [h0,hj,u]
 have hv:0<v₀:=by nlinarith only [h0,h,hn,hj,u]
 let g(s:ℕ):= P.debt_length (i s) (i s)
 have hg:BunchData P.par g:= P.tollP v₀ hv
 let c:=v+1
 have hc:0≤c:=by unfold c; linarith
 have hA:2*(Fintype.card I:ℝ)+4+c<A:=by unfold c; linarith only [h0,hj]
 have hB:2*(Fintype.card (I⊕I):ℝ)+4+c<A:=by simp only [Fintype.card_sum,Nat.cast_add]; unfold c; linarith only [h0]
 filter_upwards [(turnover P.par).eventually (coin_budget (a:=0) (c:=0) (d:=0) (e:=-v) (b:=-c) (f:=0) (Or.inr (Or.inl ⟨rfl,by unfold c; linarith⟩)) (1+2*d) (1/2) (by norm_num)), P.sun_crest z A v v₀ (Fintype.card I) hn u h,trek (I:=I) P.run z P.large P.law Q' hA hc hg, trek (I:=I⊕I) P.run z P.large P.law Q' hB hc hg] with s w w' p p' T h h'
 let k:=i s; let Y:ℝ:= trailℓ (-c) ((hat P.par.R.L P.par.x s)); have hu:0<k:= Nat.cast_pos (α:=ℝ)|>.mp (heightMerit M v₀ s); letI: NeZero k :=⟨hu.ne'⟩
 have hw:P.mixCost z s A (Fintype.card I) ≤ Fintype.card (Fin k)*(trailℓ (-v) (hat P.par.R.L P.par.x s)/3):=by rw [Fintype.card_fin]; exact w'
 obtain ⟨N,t,s',f⟩:= tile_budget T k h; have hy:Lamour.Bridge.Celeste.breadth 0 N*2≤g s:= s'.trans (?_)
 swap; · unfold g debt_length; unfold k; gcongr; omega
 apply P.variance_cost j z T s (P.priceIncrease k k) A (ε:=Y) (trainℓ ..|>.le) (p T N t hy f) ?_ (P.expenseInjective k k) (P.clearGrade j T k k h) h' hw _ ((trainℓ ..).le)
 · intro v w; dsimp only; obtain ⟨c,x,v',f⟩:= tile_budget (P.win_stack j T (P.priceIncrease k k) v w) _ (P.staff_cover j T (P.priceIncrease k k) _ _ h (P.expenseLimit k k) _ _); exact p' _ _ x v' f
 have hW : (1+2*d)*Y < 1/2* trailℓ (-v) ((hat P.par.R.L P.par.x s)):= w; linarith -- tune apply swap order
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.variance_cost_at
