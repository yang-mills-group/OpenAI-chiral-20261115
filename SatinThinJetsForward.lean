import SatinFixedContrastNovember4
import SatinThinVisit
import SatinThinJetsPrism
import YM.SU5.Six.Bearing
/-! # Move the *limiting* probe rank sale around the actual positions -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false

namespace YM.SatinJets
open Function Set Filter Complex InnerProductSpace
open OS.Semigroup
open scoped Topology InnerProductSpace NNReal ComplexOrder Classical
variable {H:Hilbert}{j:Axis}(S:OS.Semigroup H j)(U:H.Op)(p:∀ t:ℝ≥0,(S.E t).comp U=U.comp (S.E t))
variable (A B:ℝ→ H)(a:Positive S A)(b:Positive S B)
include a
lemma Positive.cont {t:ℝ}(h:0<t): ContinuousAt A t:= by
 -- analytic from lifted
 have t' := (lifted_analytic S A a (t:ℂ) (show (t:ℂ)∈inside from h)).continuousAt
 apply (t'.comp continuous_ofReal.continuousAt).congr
 filter_upwards [isOpen_Ioi.mem_nhds (show t∈ Set.Ioi 0 from h)] with v hv
 exact lifted_heat S A a hv
-- Core analytic maneuver
include b p
private lemma heat_join (s t a':ℝ) (w:0<a')(u:a'≤ s)(v:a' ≤ t):
    inner ℂ (A s) (U (B t))=inner ℂ (A a') (S.E (s+t-2*a').toNNReal (U (B a'))):=by
 let p':=(s-a').toNNReal; let q:=(t-a').toNNReal
 have h:(s+t-2*a').toNNReal= p'+q:= by ext; rw [NNReal.coe_add,Real.coe_toNNReal]; unfold p' q; rw [Real.coe_toNNReal _ (sub_nonneg.mpr u), Real.coe_toNNReal _ (sub_nonneg.mpr v)]; ring; linarith
 rw [h,S.time,a _ _ w u, b _ _ w v,S.swing]
 exact congrArg (fun y:H=>inner ℂ (A a') (S.E p' y)) (DFunLike.congr_fun (p q).symm (B a'))
lemma spectrum_meet {s t u v:ℝ}(S':0<s)(τ:0<t)(w:0<u)(v':0<v)(u':s+t=u+v):
    inner ℂ (A s) (U (B t))=inner ℂ (A u) (U (B v)):= by
 let z:= min (min s t) (min u v); have p':0<z:= lt_min (lt_min S' τ) (lt_min w v'); rw [heat_join S U p A B a b s t z p' (by unfold z; grind) (by unfold z; grind), heat_join S U p A B a b u v z p' (by unfold z; grind) (by unfold z; grind), u']
lemma analytic_meet : AnalyticOnNhd ℝ (fun t:ℝ=> inner ℂ (A (t/2)) (U (B (t/2)))) (Set.Ioi 0):=by
 intro t h; let x:=t/4
 have hs:0<t:=h; have hx:t>2*x:= by unfold x; linarith
 have hw:0<x:= by unfold x; positivity
 let T:= U (B x); let f (r:ℝ):=inner ℂ (A x) (S.E (r-2*x).toNNReal T)
 have g: AnalyticAt ℝ f t:= (Six.analyticAt_heat S _ _ _ (sub_pos.mpr hx)).comp (f:=fun r:ℝ=> r-2*x) (analyticAt_id.sub analyticAt_const)
 refine g.congr ?_; filter_upwards [lt_mem_nhds hx] with u pu
 rw [heat_join S U p A B a b _ _ x hw (by linarith only [pu]) (by linarith only [pu]),add_halves]
end YM.SatinJets

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid SatinNucleus
open Set YM.Six
-- limit Kernel, ℝ-analytic in each individual coordinate at strict positivity therein via the corresponding axis charge. No joint strip required.
variable (P:Spine)(x:P.Spectrum0 3)
local notation "W" j:max=> P.cartage j (P.advocate 3 x j)
local notation "H" j:max=> P.ManyF j (P.advocate 3 x j)
local notation "E" j:max=> P.seasons j (P.advocate 3 x j)
local notation "κ" j:max=> P.wealth j (P.advocate 3 x j)
variable {Y:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)} {V:ℕ→ P.Apron}
variable (A:Radiates P x V Y)
include A
local notation "Ω" v:max j:max l:max=> (fun t:ℝ=> (κ j) (v j l t))
lemma radiant_plus (j:Axis)(l:List Axis): SatinJets.Positive (E j) (Ω Y j l):= fun _ _=> P.height_pass x j Y A l
  -- tune args
omit A in
lemma travelers_temporal (j:Axis)(u:Vantage)(t:ℝ≥0): ((E j).E t).comp ((W j) u)= ((W j) u).comp ((E j).E t):= by ext1 p; exact P.warm_drive ..
local notation "K" j:max=> P.railKernel x j Y Y [3] []
lemma rail_prices {s t:ℝ}{v:Vantage}(h:v 3=s+t)(p:0<s)(q:0<t):
    (K 3) v= inner ℂ ((Ω Y 3 []) s) ((W 3) v ((Ω Y 3 []) t)):=by
 have g:0<v 3:= h.symm ▸ add_pos p q
 unfold railKernel; rw [P.kinetic x 3 A [] _ (half_pos g)]; exact SatinJets.spectrum_meet (E 3) _ (P.travelers_temporal x 3 v) (Ω Y 3 []) (Ω Y 3 []) (P.radiant_plus x A 3 []) (P.radiant_plus x A 3 []) (half_pos g) (half_pos g) p q (by rw [add_halves,h])
lemma rail_analytic (p:Vantage)(k:Axis): AnalyticOnNhd ℝ (fun t=> (K k) (update p k t)) (Set.Ioi 0):= by
 intro t u; let A':= Ω Y k (k::[3]); let B:= Ω Y k []
 have h:= SatinJets.analytic_meet (E k) _ (P.travelers_temporal x k p) A' B (P.radiant_plus x A k (k::[3])) (P.radiant_plus x A k []) t u
 apply h.congr
 filter_upwards with x'
 unfold railKernel; rw [of_slideP x k (update p k x') p (fun i e=> update_of_ne e ..),update_self]
-- shifted "response" (not itself a thin probe family, but probe the time content one fixed gap at a time so as to inform derivative choices). Coordinates positive shelf. Convenient use t of pt explicitly shifted along 3.
variable (R:P.Ellis 3 x)
include R
def brightShelf : Set Vantage:= shelf (fun _=>Set.Ioi 0)
lemma rail_analytic3 {p:Vantage}(hp:p∈brightShelf)(k:Axis)(s:Vantage)(q:∀ i:Axis,0≤ s i):
    AnalyticOnNhd ℝ (fun t=> (K 3) (update p k t+s)) (Set.Ioi 0):=by
 let R':=p+s
 intro t e; let f(r:ℝ):= update p k r+s; have ht(r:ℝ): f r=update R' k (r+s k):=by ext i; by_cases h:i=k; subst i; simp [f]; simp [R', f,h]
 apply ((P.rail_analytic x A (p+s) k _ (show 0<t+s k from add_pos_of_pos_of_nonneg e (q k))).comp (f:=fun x=>x+s k) (analyticAt_id.add analyticAt_const)).congr
 filter_upwards [isOpen_Ioi.mem_nhds e] with w z; unfold Function.comp; change (K k) (update R' k (w+s k))= (K 3) (f w); rw [← ht]
 have hv(i:Axis): 0<(f w) i:= add_pos_of_pos_of_nonneg (show 0< update p k w i from (show _∈ brightShelf from shelf_update (I:=fun _=> Set.Ioi (0:ℝ)) hp z) i) (q i)
 exact P.scenic_eq x k R A A 3 [3] [] (f w) (hv k) (hv 3)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.rail_analytic3
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.rail_prices
