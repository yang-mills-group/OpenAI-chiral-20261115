import NeedleW.Thirty
import Aloft.Resolve
import NeedleW.Line
import Aloft.Spoon
import Aloft.BudgetA
import Aloft.Ride
import Aloft.Conceit
import Aloft.ZL
import Aloft.Canon
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) 
namespace Aloft
open Py.Dyad Keeping Py.Rate.Pitching.Focus
open _root_.YM.Preen
local notation "j0"=> (3:Axis)
variable (M:Morn P.par.K)(α:ℝ)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(p:∀ s,F ≤ s→ Accordance P M F s (C s) (D s))(u:RobeRoad P F C D x)(v:Jones P M α F C D x)
local notation "ξ"=>P.otherSpectrum 3 3 x
local notation "Ω"=>P.heaven 3 ξ
local notation "Ψ"=> P.seasons 3 ξ
local notation "H"=>P.ManyF 3 ξ
local notation "ζ"=>P.wealth 3 ξ
local notation "A₀"=>paster (Ω)
local notation "U"=>P.cartage 3 ξ
namespace Anchovy
open _root_.NeedleW
variable (J:P.Ellis 3 x)
private lemma reAbs {T:Hilbert}(k:T)(w:T.Op)(x:ℝ): ‖inner ℂ ((x:ℂ) • k) (w ((x:ℂ) • k))‖ = x^2 *‖inner ℂ k (w k)‖:=by rw [map_smul,inner_smul_right,inner_smul_left,Complex.conj_ofReal, norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,← mul_assoc,← sq,sq_abs]
private lemma roadβ{R:Hilbert}(p:ℕ→R.Op)(v:ℕ→R)(τ f:ℕ→ℝ)(D0:ℕ→ℕ)(g:Tendsto (fun k=> ‖τ k‖*f k) atTop (𝓝 0))(h:Tendsto D0 atTop atTop)(a:∀k,‖p k (v k)‖ ≤ f (D0 k)): Tendsto (fun i=>p i ((τ (D0 i):ℂ) • v i)) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_ ) (show Tendsto (fun i=>‖τ (D0 i)‖*f (D0 i)) atTop (𝓝 0) from g.comp h)
 rw [map_smul,norm_smul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (a i) (norm_nonneg _)
variable (G:ℕ→ (P.ManyF 3 (P.otherSpectrum 3 3 x)).space)(g:∀ i,F ≤ i→PeriodS P F C D x i (G i))
local notation "z0" j:max=>A₀ (G j)
variable (v0:Enviro P x)
local notation "ℓ" d:max=>ingress P d
include p v v0 g J
set_option synthInstance.maxHeartbeats 250000 in
lemma avoid {T':ℕ→ℕ}(h:Tendsto T' atTop atTop){y:H}(q:Tendsto (fun i=>z0 (hikeV (T' i))) atTop (𝓝 y))(hy:y≠0): False:=by
 have he:∀ᶠ i:ℕ in atTop, let d:=T' i; ∃ w:Cover,∃ e:Enrolled P d (stairW d) w,∃ r:H, (∃ u':Vantage,U u' r=amber P x 0 (hikeV d+stairW d) w e.clock.1)∧ ‖clean (z0 (hikeV d)) r‖≤thresholdU P M α d (stairW d):=(h.eventually (boundLine P M α F C D x p v G g)).mono (fun i he=>he _)
 obtain ⟨D0,hD,l⟩:= extraction_of_frequently_atTop he.frequently
 let D':= T'∘D0; choose w e r a a' using l; choose g0 g₀ using a
 let t(n:ℕ):=(ℓ (D' n):ℂ) • r n
 let z(n:ℕ):=z0 (hikeV (D' n))
 let Y(i n:ℕ):=terrain P x (D' n) i (w n)
 have hz:Tendsto z atTop (𝓝 y):= q.comp hD.tendsto_atTop
 have uD:= h.comp hD.tendsto_atTop
 have U0:Tendsto (fun i:ℕ=>clean (z i) (t i)) atTop (𝓝 0):= roadβ (R:=H) _ r _ _ D' (thresholdScale P M α) uD a'
 obtain ⟨m,m0,m1⟩:=opening P
 let f(i n:ℕ):= Zippy.outΩ t (Y i) n
 have hf(i n:ℕ)(gk:1 ≤ i): f i n= (ℓ (D' n))^2*‖gem P (D' n) i x (w n)‖:=by
    let y0:= evo P x J (D' n) i (w n) (e n) gk (g₀ n) rfl
    unfold f _root_.Zippy.outΩ t
    exact (Eq.trans (reAbs (T:=H) (r n) (Y i n) _) (congrArg (fun q:ℂ=>(ingress P (D' n))^2*‖q‖) y0.symm))
 have hb:∀ᶠ d:ℕ in atTop, traceF P ≤ f 1 d∧ f 1 d≤ storm*‖Ridgetop.visible‖/( (pollN P:ℝ)*4)^8 ∧ f m d ≤ traceF P/2:=by
    filter_upwards [uD.eventually (sledge P x v0 1 le_rfl),uD.eventually (sledge P x v0 m m0)] with d t' T1
    rw [hf _ _ le_rfl,hf _ _ m0]; have ht:=t' (w d) (e d); simp only [Nat.cast_one,mul_one] at ht; exact ⟨ht.1,ht.2, (T1 (w d) (e d)).2.trans m1⟩
 have U':= _root_.NeedleW.curlV z t y hz hy U0 (Y 1) (Y m) (fun n=>rideTx P x 1 (Y:=D') le_rfl w n) (fun n=>rideTx P x m (Y:=D') m0 w n) (riding P x 1 le_rfl uD w e) (riding P x m m0 uD w e) _ (hb.mono fun i q=> q.2.1) (traceF P/4) (by have h:=trace_pos P; positivity)
 obtain ⟨d,t,v⟩: ∃ d, (traceF P ≤ f 1 d ∧ f m d ≤ traceF P/2) ∧ |f 1 d - f m d| ≤ traceF P/4 := ((hb.mono fun i q=> (And.intro q.1 q.2.2)).and U').exists
 linarith only [le_abs_self (f 1 d-f m d),t.1,t.2,v,trace_pos P]
#check @boundLine
#print axioms avoid
end Anchovy
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
