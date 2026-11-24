import YM.SU5.Regis.Legend
import YM.SU5.Cheer.Harp
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
open Cheer
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)(c r:ℕ→ℕ)
open Regis.Head CF.Velvet
variable {β u:ℝ}{P}{R:P.Register}{X:Supplier}(B:uniform P R X β u)
variable {J:ℕ→Type}[∀ n,Fintype (J n)]{I:∀ n,J n→ Type*}[∀ n i,Fintype (I n i)] (A:∀ n i,Etch SU.group (I n i)) (b:ℕ→ℝ)
def aura0 (P:Spine)(c:ℕ→ℕ):Prop:=∀ n i, ‖P.E (c n) (P.view (A n i) (c n)).val-(P.tapestryRate (A n i) (c n):ℂ)‖≤ b n
def aura' (P:Spine)(c:ℕ→ℕ)(x:P.Spectrum0 3):Prop:= ∀ᶠ n in atTop,∀ (j:Axis) i,‖P.singleState j (c n) (P.otherSpectrum 3 j x) (P.view (A n i) (c n))-(P.tapestryRate (A n i) (c n):ℂ)‖< b n
include B
theorem auras (p:∀ i,0<b i): ∃ g:ℕ→ℕ,∀ c:ℕ→ℕ,g≤c→ aura0 A b P c ∧ ∀ᵐ x∂P.pillars 3,aura' A b P c x:=by
 let d(n:ℕ):= discount n (b n)/((Fintype.card (J n):ℝ)+1)
 have ht(n):0<d n:=by unfold d discount; have v:=p n; positivity
 choose g h using fun n=> eventually_atTop.1 (Filter.eventually_all.mpr fun i=> (epochP (A n i) B (b n) (p n)).and (varianceP 3 (A n i) B (ht n)))
 refine ⟨g,fun c p'=> ⟨fun n i=>(h n (c n) (p' n) i).1,?_⟩⟩
 let W(n:ℕ)(i:J n)(x:P.Spectrum0 3):= ‖P.singleState 3 (c n) x (P.view (A n i) (c n)) - (P.tapestryRate (A n i) (c n):ℂ)‖^2
 have hp(n i): Continuous (W n i):= ((P.chi_joint 3 (P.reading 3 _ _) |>.sub continuous_const).norm).pow _
 have hv(n): (Fintype.card (J n):ℝ)* d n≤ discount n (b n):= by have he: d n * ((Fintype.card (J n):ℝ)+1)=discount n (b n):= div_mul_cancel₀ _ (by positivity); linarith only [ht n,he]
 filter_upwards [prognosis W d hp (fun n i x=>sq_nonneg _) b p (fun n i=>(h n _ (p' n) i).2) hv] with x hx; filter_upwards [hx] with n u j i; rw [P.single_agrees]; exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (p n).le (by omega:2≠0)).1 (u _)
omit B
#check aura'
variable (P)
lemma seals' (n)(i:J n)(s:ℕ): let F:= P.view (A n i) s; F∈bay P.calibration (Papal.spanOf (A n i)) false ∧ F∈enclave P.calibration:= by
 intro F; exact ⟨Papal.designed_test .., fun j=> Papal.painted_gauge (A n i) (Papal.museumV (P:=P.par) s) (P.calibration.c j)⟩
end Spine
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
open Regis.Head 
private lemma curvedLift(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
variable {J:ℕ→Type}[∀ n,Fintype (J n)]{I:∀ n,J n→ Type*}[∀ n i,Fintype (I n i)] (A:∀ n i,Etch SU.group (I n i)) (b:ℕ→ℝ)
include A b
-- CP13. arbitrary prescribed precision itinerary.
lemma surveyed (p:∀ n,0<b n) (e v D:ℝ)(X:Supplier)(hx:0<v)(u:0<D) (z:ℕ→ℕ): ∃ (P:Spine)(K:P.Register), uniform P K X e v ∧ ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), Launch P c r ∧ aura0 A b P c ∧ roughUV P c r keyV ∧ ∃ (α t:ℝ),0<α∧ 0<t∧t<D ∧ ∃ Y: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ aura' A b P c x ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) Y t ∧
       ∀ z:SU.Slot, P.Intact K i Y.toGaze x z t∧ P.Royal i (P.otherSpectrum 3 3 x) Y (Window.family z) t ∧ P.Passage x c r K z ∧ P.Bands x (Window.family z) c r:=by
 obtain ⟨P,K,T⟩:=installation X e v hx; obtain ⟨r,g,f,R⟩:= outing T keyV keyV_positive z; obtain ⟨u₀,hU⟩:=auras T A b p; obtain ⟨c,p,h⟩:= curvedLift (fun i=>max (f i) (u₀ i)); obtain ⟨Y,e,F⟩:= R c h (fun i=>(le_max_left ..).trans (p i)); obtain ⟨R',t'⟩:= hU c (fun i=> (le_max_right ..).trans (p i)); obtain ⟨α,t,H,v,g0,S,Z,U⟩:= violet_simultaneous T u
 refine ⟨P,K,T,r,g,c,Y,R',e,α,t,H,v,g0,S,?_⟩; filter_upwards [U] with i F'; obtain ⟨x,J,x',w,W⟩:= F' _ (F.and t')
 exact ⟨x,x',J.2,J.1,w,fun z=> ⟨(W z).1,(W z).2,voyaged Y J.1 keyV_go K z,fertile (Window.family z) Y J.1 keyV_go (x'.2.1.accepted 3)⟩⟩
end Prototype
#check @Papal.lens_state
#print axioms Papal.lens_state
#check @Papal.panelThink
#print axioms Papal.panelThink
#check @Spine.varianceP
#print axioms Spine.varianceP
#check @Prototype.surveyed
#print axioms Prototype.surveyed
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
