import YM.SU5.Registration.Heave.Parade
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
/-! # All fixed finite, translated by an extra time tick

Pay before the final tick is permitted, then show this implements the same
orders in the weighted projection at every positive radius. Keep colored
(H, or lazily along any spectator) estimate; never resample.
-/
open _root_.YM.SatinRegistration
variable (P:Spine) (x:P.Spectrum0 3) (w:Prism)
local notation "θ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x 3
local notation "H₁"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
variable (A:P.Apron) (t:ℝ≥0)
section singular
local notation "B"=> P.aTuba w A
local notation "v"=>(B).u θ
local notation "s"=> A.s
local notation "M" x:max k:max=>whenly (timeMesh P.par) x k
local notation "d"=> P.burst s
local notation "H" n:max=> P.stageH θ ξ (P.festival A (n+1))
local notation "V" n:max=> P.stageG θ ξ (P.festival A (n+1))
local notation "T" t:max n:max=> (w n) • ((H n) (t+d) (t-d))
lemma kid_cost (e:(P.aTuba w A).allowance P θ ≤ t) : P.stageH θ ξ (P.aTuba w A) t t= ∑ n ∈ w.support, (w n) • ((H n) (t+d) (t-d)):=by
 let σ(n:ℕ):P.Test:= P.shifts θ (1:ℤ) (P.festival A (n+1)).F; let k:= v; let F(n:ℕ)(t:ℝ≥0):= T t n
 let g:= add_pos ((B).pos θ) ((B).pos θ)
 have u(n:ℕ)(f:n∈w.support):P.Deposited θ ξ s v g (w n • σ n) (F n):=by
    let Y:= P.festival A (n+1); have hp:Y.s=s:= P.festival_s A _
    have he:n+1 ≤ lastTuba w:= le_sup (f:=fun n=> n+1) f
    have hv:Y.zoom P s θ= A.u θ+(n+1):=(show Y.zoom P s θ=Y.zoom P Y.s θ from congrArg (fun x=> Y.zoom P x θ) hp.symm).trans ((Y.zoom_at P θ).trans (P.festival_u A _ θ))
    have hz:v = A.u θ+lastTuba w + 1:=rfl
    have x := P.shifted_deposit θ ξ s v g Y 1 hp.le (by omega); rw [show Y.full P s=Y.F from hp ▸ Y.full_at P] at x; exact x.scale P θ ξ s v g _
 have he:=Deposited.sum P θ ξ s v g w.support (fun i=> w i • σ i) F u
 have hx: (∑ i∈ w.support,w i • σ i)= (B).F:=by
    change _= P.shifts θ 1 (P.drumroll A.s A.F w); unfold drumroll; rw [map_sum]; apply sum_congr rfl; intro i h; rw [map_smul]; unfold σ; rw [P.festival_f]
 rw [hx] at he; rw [P.deposit_at_finger θ ξ (B) he t e, Finset.sum_apply]
lemma kid_costG (e:(P.aTuba w A).allowance P θ ≤ t) : P.stageG θ ξ (P.aTuba w A) t t= ∑ n ∈ w.support, w n • ((V n) (t+d) (t-d)) := by unfold stageG; rw [P.kid_cost x w A t e,map_sum]; simp_rw [map_smul]
end singular
variable (A₀:ℕ→ P.Apron) (q:Tendsto (fun i=>(A₀ i).s) atTop atTop)(p:P.Bought3 x A₀)
local notation "d" i:max=> P.burst (A₀ i).s
local notation "HΓ" i:max j:max => P.festival (A₀ i) (j+1)
local notation "F" i:max=> P.aTuba w (A₀ i)
-- use resolution kernel position relative to same gauge owner. Pay all at once in cap
noncomputable def drumPrice (F₀:ℝ≥0→ (P.ManyF 3 (P.advocate 3 x 3)).Op) (t:ℝ≥0) : (P.ManyF 3 (P.advocate 3 x 3)).Op:= ∑ n∈w.support,w n • P.festivalPrice x F₀ (n+1) t
local notation "f" i:max j:max t:max=> w j • P.stageG 3 ξ (HΓ i j) (t+d i) (t-d i)
local notation "Hξ"=>P.managed x A₀ p.card
variable {G':Hilbert}
private lemma sum_fly {ι:Type*}(v:Finset ι)(A:ι→ℕ→G'.Op)(B:ι→ G'.Op)(x:∀i, Flying (A i) (B i)): Flying (fun j=>∑ i∈v,A i j) (∑ i∈v,B i):=by
 classical
 induction v using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Flying.still _
 | insert i v' h he=> simp_rw [sum_insert h]; exact (x i).add' he
lemma RisePrice.sum {ι:Type*}(A:ι→ℝ≥0→ℕ→G'.Op)(v:Finset ι) (w:∀ i, RisePrice (A i)): RisePrice (fun t j=>∑ i∈v,A i t j):=by
 classical
 induction v using Finset.induction_on with
 | empty=> refine ⟨0,0,le_rfl,fun t _ _=>Eventually.of_forall fun _=>?_⟩; simp
 | insert i v h ih=>
    obtain ⟨n,C,q,z⟩:=w i; obtain ⟨k,D,p,x⟩:=ih; refine ⟨max n k, C+D,add_nonneg q p,fun t u r=>?_⟩; filter_upwards [z t u r,x t u r] with i₀ a b;
    have g(x y:ℕ)(p:x≤ y)(c:ℝ)(q:0≤c)(r':ℝ)(h:(t:ℝ)^x * c ≤ r'):(t:ℝ)^y*c≤r':= (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (show 0≤(t:ℝ) from by positivity) (show (t:ℝ) ≤ 1 from r) p) q).trans h
    rw [sum_insert h]; exact (mul_le_mul_of_nonneg_left (norm_add_le ..) (pow_nonneg (show (0:ℝ) ≤ (t:ℝ) from by positivity) _)).trans ((mul_add ..).le.trans (add_le_add (g n (max n k) (le_max_left ..) _ (norm_nonneg _) _ a) (g k (max n k) (le_max_right ..) _ (norm_nonneg _) _ b)))
lemma RisePrice.smul {𝒳:ℝ≥0→ℕ→ G'.Op}(p:RisePrice 𝒳) (z:ℂ): RisePrice (fun t i=> z • 𝒳 t i):=by
 obtain ⟨k,C,v,h⟩:=p; refine ⟨k,‖z‖*C,mul_nonneg (norm_nonneg _) v,fun t v₀ a=>?_⟩; filter_upwards [h t v₀ a] with i p; rw [norm_smul,mul_left_comm]; exact mul_le_mul_of_nonneg_left p (norm_nonneg z)
include q p
lemma tubas_are_thin(j:Axis): Tendsto (fun i=>(F i).realWidth P j) atTop (𝓝 0):=by
 simp_rw [P.tuba_width]; simpa only [mul_zero,add_zero,Function.comp_apply] using (p.card.1 j).add ((P.macroStep_zero.comp q).const_mul _)
lemma tubas_allow(j:Axis): Tendsto (fun i=>(F i).allowance P j) atTop (𝓝 0):=by
 have h:= P.tubas_are_thin x w A₀ q p j; simp_rw [Apron.width_real] at h; exact NNReal.tendsto_coe.mp h
lemma trumpets_flight (h:0<t): Flying (fun i=>P.stageG θ ξ (F i) t t) (P.drumPrice x w (Hξ) t) :=by
 have hv:= P.burst_zero.comp q; have u(j:ℕ):= P.festival_bought x A₀ q p (j+1)
 have e(j:ℕ):Flying (H:=G) (fun i=> f i j t) (w j • P.festivalPrice x (Hξ) (j+1) t):=by
    rw [←P.festival_match x A₀ q p]; -- maybe side
    · exact Flying.scaled (tendsto_const_nhds (x:=w j)) (P.uniform_pit x (fun i=>HΓ i j) t _ _ (by simpa using ((P.burst_zero.comp q).const_add t)) (by simpa using Tendsto.sub (tendsto_const_nhds (x:=t)) hv) h (u j).card)
    exact h
 refine (sum_fly w.support (fun j i=> f i j t) _ e).late ((P.tubas_allow x w A₀ q p 3|>.eventually (ge_mem_nhds h)).mono fun i u =>?_); exact (P.kid_costG x w (A₀ i) t u).symm
lemma trumpet_bought : Bought3 P x (fun i=> F i):=by
 refine toBought P x _ ?_ (fun t h=> (P.trumpets_flight x w t A₀ q p h).Cauchy) (P.tubas_are_thin x w A₀ q p)
 let X(n:ℕ)(t:ℝ≥0)(i:ℕ):= w n • P.stageH θ ξ (HΓ i n) (t+d i) (t-d i)
 let h(i:ℕ):= P.festival_bought x A₀ q p (i+1)
 obtain ⟨k,C,v,e⟩:=RisePrice.sum X w.support (fun i=> RisePrice.smul ((h i).moving P x (fun n=>HΓ n i) _ _ (fun t _=>by simpa using (P.burst_zero.comp q).const_add t) (fun t _=>by simpa using Tendsto.sub (tendsto_const_nhds (x:=t)) (P.burst_zero.comp q))) (w i))
 refine ⟨k,C,v,fun t u v=>?_⟩; filter_upwards [e t u v,(P.tubas_allow x w A₀ q p 3).eventually (ge_mem_nhds u)] with i h x'; rw [P.kid_cost x w (A₀ i) t x']; exact h
lemma drum_paid (h:P.CapReady x (fun i=> F i))(w':0<t): P.managed x _ h t=P.drumPrice x w (Hξ) t:= (P.received_moves x _ t h w').unique (P.trumpets_flight x w t A₀ q p w')
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.trumpets_flight
#print axioms Spine.trumpet_bought
#print axioms Spine.drum_paid
