import YM.SU5.Registration.Heave.Conduct
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

set_option quotPrecheck false
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets Drums
open _root_.YM.SatinRegistration
variable (P:Spine)(x:P.Spectrum0 3)(A:ℕ→ P.Apron)
local notation "ξ"=> P.advocate 3 x 3
local notation "H₁"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "B" i:max=>P.drumStep (A i)
local notation "δ" i:max=> P.burst (A i).s
local notation "sV" t:max i:max=> t-(P.burst (A i).s)
local notation "Θ!"=> P.physicalEnergy 3 ξ
local notation "Γ!"=>P.seasons 3 ξ
local notation "ρ" t:max i:max=> P.stageH 3 ξ (A i) t (sV t i)
local notation "η" t:max i:max=> P.stageG 3 ξ (A i) t (sV t i)
variable (q:Tendsto (fun i=>(A i).s) atTop atTop)(h: P.CapReady x A)
include q h
lemma priceLimit (j:Axis): Tendsto (fun i=>(B i).allowance P j) atTop (𝓝 0):= by simp_rw [P.step_s]; simpa only [add_zero,Function.comp_apply] using (P.all_width_paid x A j h).add (P.burst_zero.comp q)
def drumIssuer (F₀:ℝ≥0→(P.ManyF 3 ξ).Op) (t:ℝ≥0):(P.ManyF 3 ξ).Op:= action (P.seasons 3 (P.advocate 3 x 3)) (t/2) (genPrice (Γ!) (t/2)) (F₀ (t/2))
local notation "G₀"=>P.managed x A h
lemma issue_budget (t:ℝ≥0)(w:0<t): Flying (H:=G) (fun i=>P.stageG 3 ξ (B i) t t) (P.drumIssuer x (G₀) t):=by
 let d(i):= P.burst (A i).s; let z:=t/2; have he:0<z:=half_pos w
 have hv:Tendsto d atTop (𝓝 0):=P.burst_zero.comp q
 let U(i):=η z i
 have T:Flying (H:=G) U (G₀ z):= P.uniform_pit x A z _ _ tendsto_const_nhds (by simpa using Tendsto.sub (tendsto_const_nhds (x:=z)) hv) he h
 let F:=limit_action (Γ!) d hv (Eventually.of_forall fun i=>P.burst_p _) T z he
 refine F.late ((P.priceLimit x A q h 3 |>.eventually (ge_mem_nhds he)).mono fun i h=> ?_); exact (P.conductsG (A i) x t h).symm

omit h
lemma step_bought (F₀:P.Bought3 x A) : P.Bought3 x (fun i=> B i):=by
 let V:= F₀.card; let d(i):=δ i; have e:Tendsto d atTop (𝓝 0):= P.burst_zero.comp q
 let Λ:= P.priceLimit x A q V
 let U(t:ℝ≥0)(i:ℕ):=ρ t i; have T:RisePrice U:= F₀.moving P x A _ _ (fun t _=> tendsto_const_nhds) (fun t _=> by simpa using Tendsto.sub (tendsto_const_nhds (x:=t)) e)
 refine toBought P x _ ?_ (fun t w=> (P.issue_budget x A q V t w).Cauchy) ?_
 · obtain ⟨k,C,b,f⟩:= fare_action (Θ!) d e (Eventually.of_forall fun i=>P.burst_p _) T; refine ⟨k,C,b,fun s t z=>?_⟩
   filter_upwards [f s t z,(Λ 3).eventually (ge_mem_nhds (half_pos t))] with i p h
   rw [P.conducts _ _ _ h]; exact p
 intro j; simp_rw [Apron.width_real]; exact NNReal.tendsto_coe.mpr (Λ j)
include h
lemma uphill {v:ℕ→ P.Apron}(hv:v=(fun i=>B i))(F:P.CapReady x v)(t:ℝ≥0)(g:0<t): P.managed x v F t=P.drumIssuer x (G₀) t:=by subst v; exact (P.received_moves x _ t F g).unique (P.issue_budget x _ q h t g)
omit q h

-- Any order. prepare these values in EXACT chronological step costs. Also need sizes & width
-- correspondence for original witness (not defeq to matrix across starting height).
variable (A₀:P.Apron)
noncomputable def festival : ℕ→ P.Apron
 | 0=>A₀
 | n+1=>P.drumStep (festival n)
local notation "xV"=>A₀.allowance P 3
lemma festival_s (n:ℕ): (P.festival A₀ n).s=A₀.s:=by induction n with| zero=>rfl| succ n h=> exact h
lemma festival_u (n:ℕ)(j:Axis): (P.festival A₀ n).u j=A₀.u j+n:=by induction n with|zero=>rfl|succ n h=> change (P.festival A₀ n).u j+1=_; rw [h,Nat.add_assoc]
lemma festival_f (n:ℕ): (P.festival A₀ n).F=P.tubaField A₀.s A₀.F n:=by
 induction n with
 | zero=> rfl
 | succ n h=> change P.tubaField (P.festival A₀ n).s (P.festival A₀ n).F 1=_; rw [h,P.festival_s]; rfl
noncomputable def festivalPrice (F₀:ℝ≥0→(P.ManyF 3 (P.advocate 3 x 3)).Op) : ℕ→ℝ≥0→(P.ManyF 3 (P.advocate 3 x 3)).Op
 | 0 => F₀
 | n+1=> P.drumIssuer x (festivalPrice F₀ n)
include q
lemma festival_bought (F:P.Bought3 x A)(n:ℕ):P.Bought3 x (fun i=>P.festival (A i) n):=by
 induction n with
 | zero=>exact F 
 | succ n h=> exact P.step_bought x (fun i=>P.festival (A i) n) (by simpa only [P.festival_s] using q) h
lemma festival_match (F:P.Bought3 x A)(n:ℕ)(t:ℝ≥0)(u:0<t): P.managed x _ (P.festival_bought x A q F n).card t=P.festivalPrice x (P.managed x A F.card) n t:=by
 induction n generalizing t with
 | zero=>rfl
 | succ n ht=>
    let Bₙ (i):=P.festival (A i) n; let V:= (P.festival_bought x A q F n).card
    change P.managed x (fun i=> P.festival (A i) (n+1)) _ t=P.drumIssuer x (P.festivalPrice x (P.managed x A F.card) n) t
    rw [P.uphill (v:=fun i=>P.festival (A i) (n+1)) x Bₙ (by simpa only [Bₙ,P.festival_s] using q) V rfl ((P.festival_bought x A q F (n+1)).card) t u]; exact congrArg (action (Γ!) (t/2) (genPrice (Γ!) (t/2))) (ht _ (half_pos u)) -- maybe unfold
omit q
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.festival_match
#print axioms Spine.festival_bought
#print axioms Spine.festival_f
#print axioms Spine.drumIssuer
