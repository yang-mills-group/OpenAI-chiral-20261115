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
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
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
local notation "L" z:max => asset P x (A₀ z)
local notation "r" d:max=> ((girder P d):ℝ)
local notation "ℓ" d:max=>ingress P d
private lemma reAbs {T:Hilbert}(k:T)(w:T.Op)(x:ℝ): ‖inner ℂ ((x:ℂ) • k) (w ((x:ℂ) • k))‖ = x^2 *‖inner ℂ k (w k)‖:=by rw [map_smul,inner_smul_right,inner_smul_left,Complex.conj_ofReal, norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,← mul_assoc,← sq,sq_abs]
private lemma roadβ{R:Hilbert}(p:R.Op)(v:ℕ→R)(τ f:ℕ→ℝ)(D0:ℕ→ℕ)(g:Tendsto (fun k=> ‖τ k‖*f k) atTop (𝓝 0))(h:Tendsto D0 atTop atTop)(a:∀k,‖p (v k)‖ ≤ f (D0 k)): Tendsto (fun i=>p ((τ (D0 i):ℂ) • v i)) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (fun i=>?_ ) (show Tendsto (fun i=>‖τ (D0 i)‖*f (D0 i)) atTop (𝓝 0) from g.comp h)
 rw [map_smul,norm_smul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left (a i) (norm_nonneg _)
#check @rideTx
#check @evo
#check @riding
variable (J:P.Ellis 3 x)(v0:Enviro P x)
include v u v0 J p
-- No hypothesis. actually for all x qualifiers.Branch
set_option maxHeartbeats 550000 in
theorem stoker(j:ℕ)(y:H)(hY:PeriodS P F C D x j y): ¬FiniteDimensional ℂ (L y) :=by
 intro ht
 have he:=spoonLX P M α F C D x j y hY ht p u v
 obtain ⟨D0,h,hc⟩:=extraction_of_frequently_atTop he.frequently
 have he(n:ℕ):=hc n (stairW (D0 n)); choose w e z u0 a using he; choose g g₀ using u0
 let t(n:ℕ):=(ℓ (D0 n):ℂ) • z n
 let K:= L y
 let Y(i n:ℕ):=terrain P x (D0 n) i (w n)
 have U0:Tendsto (fun i:ℕ=>adsorption (G:=(H)) K (t i)) atTop (𝓝 0):= roadβ (R:=H) _ z _ _ _ (thresholdScale P M α) h.tendsto_atTop a
 obtain ⟨m,m0,m1⟩:=opening P
 let f(i n:ℕ):= Zippy.outΩ t (Y i) n
 have hf(i n:ℕ)(gk:1 ≤ i): f i n= (ℓ (D0 n))^2*‖gem P (D0 n) i x (w n)‖:=by
    let y0:= evo P x J (D0 n) i (w n) (e n) gk (g₀ n) rfl -- order P x ...
    unfold f _root_.Zippy.outΩ t
    exact (Eq.trans (reAbs (T:=H) (z n) (Y i n) _) (congrArg (fun q:ℂ=>(ingress P (D0 n))^2*‖q‖) y0.symm))
 have hb:∀ᶠ d:ℕ in atTop, traceF P ≤ f 1 d∧ f 1 d≤ storm*‖Ridgetop.visible‖/( (pollN P:ℝ)*4)^8 ∧ f m d ≤ traceF P/2:=by
    filter_upwards [h.tendsto_atTop.eventually (sledge P x v0 1 le_rfl),h.tendsto_atTop.eventually (sledge P x v0 m m0)] with d t T1
    rw [hf _ _ le_rfl,hf _ _ m0]; have ht:=t (w d) (e d); simp only [Nat.cast_one,mul_one] at ht; exact ⟨ht.1,ht.2, (T1 (w d) (e d)).2.trans m1⟩
 let U':=Zippy.curls K t (Y 1) (Y m) (fun n=>rideTx P x 1 (Y:=D0) le_rfl w n) (fun n=>rideTx P x m (Y:=D0) m0 w n) (riding P x 1 le_rfl h.tendsto_atTop w e) (riding P x m m0 h.tendsto_atTop w e) ht U0 _ (hb.mono fun i q=> q.2.1) (traceF P/4) (by have h:=trace_pos P; positivity)
 obtain ⟨d,t,v⟩: ∃ d, (traceF P ≤ f 1 d ∧ f m d ≤ traceF P/2) ∧ |f 1 d - f m d| ≤ traceF P/4 := ((hb.mono fun i q=> (And.intro q.1 q.2.2)).and U').exists
 linarith only [le_abs_self (f 1 d-f m d),t.1,t.2,v,trace_pos P]
#print axioms stoker
end Aloft
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
