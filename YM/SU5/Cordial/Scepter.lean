import YM.SU5.Cordial.Meridian
import YM.SU5.Cordial.Balloon
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
/-! # Hankel estimates repay marginal continuity inside this UV resolution.
 No passage to different study/vacuum data! Lift through other axes on this observation.
 Strict separation using actual SUPPORT at its stencil; no need diagonal limit to get this. -/
open OS.Semigroup (F)
open OS.Semigroup.Balloon
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "κ" => P.calibration
local notation "B" => P.par.block
local notation "M" => timeMesh P.par
local notation "Γ" => marks M
local notation "N₀" => notch M
local notation "ε" => YM.basis (3:Axis)
local notation "ι" => k.val
local notation "ℓ" => P.calibration.ℓ
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "χ" => P.otherSpectrum 3 k.val (β)
local notation "W" => P.ColorHil (ι) (χ)
local notation "Λ" => P.physicalEnergy (ι) (χ)
local notation "Ψ" => P.voyageF 3 (β)
local notation "y" s:max i:max=> P.shard x Z s i
local notation "U" => (Ψ).crew k
lemma visibility (n:ℕ) : (P.stockS Z (P.flash n))∈ bay κ (P.flash n).patio true:= (Tapestry.locates ..).2 (((flourish (P.flash n) Z).1.narrow _).widen) -- tune
-- adapted payable_cut
lemma earningK (n:ℕ) (t:ℤ)(u: (ℓ:ℤ) +1 ≤ 2*(P.crewB t)): let T:= P.stockS Z (P.flash n); P.birthF k.val s (P.shifts k.val t T) ∧ P.birthF k.val s (P.reflectTest k.val (P.reflectTest 3 (P.shifts k.val (-t) T))):=by
 let L:=(P.flash n).patio; intro f; have hp : f∈ enclave P.calibration:= by apply P.celebrity
 let p : f∈bay κ L true := P.visibility Z n
 let k0:=k.val; let w:= P.shifts k.val (-t) f; let Vv':= plow κ k.val (-t) L
 have he:Tower.region (ι) 0 (ℓ) (plow (κ) k.val t L):=by
    intro i h; obtain ⟨j,p,rfl⟩:=plow_stays κ k.val t L h; rw [SlabMark.moves,if_pos rfl,zero_add,P.flash_fixed k.val n _ p k.property,←ruler_offset]; change _ ≤ 1+2*P.crewB t; omega -- relation crewB
 have hv:Tower.region (ι) 0 (ℓ) (reflectedBox (ι) 0 (reflectedBox 3 0 Vv')):=by
    intro i h; obtain ⟨z,v,w⟩:= reflect_stays k.val _ _ h; obtain ⟨z1,v1,tz⟩:= reflect_stays 3 _ _ v; obtain ⟨g,r,rfl⟩:=plow_stays κ k.val _ _ v1; rw [w,if_pos rfl,tz,if_neg k.property,SlabMark.moves,if_pos rfl,mul_zero, P.flash_fixed _ n g r k.property,←ruler_offset]; change _ + ℓ ≤ -(1+2*P.crewB (-t)) +0; rw [show P.crewB (-t) = -P.crewB t from (by simp [crewB,Heat.gaugeShift])]; omega
 exact ⟨P.criteria _ _ (P.shifts_support _ _ _ p) he (P.shifts_keep _ _ hp), P.criteria k.val s (P.canFlip (reflectedBox 3 0 Vv') k.val (P.canFlip Vv' 3 (P.shifts_support _ _ _ p))) hv (P.mirror_keeps k.val _ (P.mirror_keeps 3 _ (P.shifts_keep k.val (-t) hp)))⟩
private lemma backward (s:ℕ)(t:ℤ): N₀ s (-t) = -(N₀ s t):=neg_eq_iff_add_eq_zero.mpr (by rw [←notch_add,add_neg_cancel,notch_zero])|>.symm -- parse identity
-- both viewed at exactly *their* height, and same-axis Σ except translation.
local notation "P₁" i:max n:max => P.shifts k.val i (P.stockS Z (P.flash n))
local notation "P₂" i:max n:max => P.reflectTest k.val (P.reflectTest 3 (P₁ (-i) n))
private lemma GShift {G: AddSubgroup ℝ} (A:Hilbert)(P':Players G A)(b a:G)(x : A):
 inner ℂ x (P'.play (a+(b+b)) x)=inner ℂ (P'.play (-b) x) (P'.play a (P'.play b x)):=by
 rw [← P'.shift_g, P'.paved,P'.paved, add_assoc]; rw [← add_left_comm b a b]  -- tune
lemma marginal (u:Γ)(v:0≤(u:ℝ))(t:ℤ)(n:ℕ)(p:P.birthF k.val s (P₁ t n))(w:P.birthF k.val s (P₂ t n)):
 inner ℂ (y s n) ((U).play (u+(N₀ s t+N₀ s t)) (y s n))=inner ℂ (P.viewF k.val (χ) s w) ((Λ).E (Real.toNNReal (u:ℝ)) (P.viewF k.val (χ) s p)):=by
 let a:=P.brightC Z s n; let f:=P.passes 3 s k.property (-t) a; let g:=P.passes 3 s k.property t a;
 let l:=P.viewF 3 (β) s f; let r:=P.viewF 3 (β) s g; let Z' :V:= y s n; let b:Γ:= N₀ s t; have he:r=(U).play b Z' := (P.registered 3 (β) s k a t).symm
 have ht:l=(U).play (-b) Z':= Eq.trans ((P.registered 3 (β) s k a (-t)).symm) (congrArg (fun t:Γ=> (U).play t Z') (P.backward s t)) -- k needed?
 refine Eq.trans ?_ (P.advances_cost 3 (β) s k u f g w p v)
 change inner ℂ Z' ((U).play (u+(b+b)) Z') = inner ℂ l ((U).play u r)
 exact (GShift (V) (U) b u Z').trans (congrArg₂ (inner ℂ) ht.symm (congrArg ((U).play u) he.symm))
-- bridge eligibility shown once. enter with n-dependent t_n. Cost to go outside corners.
variable {P x c r} (A:Launch P c r) {d:ℕ→ℝ} (Y:readyUV P c r x d)(p:Tendsto d atTop (𝓝 0))
include A Y p
private def R₁ (n:ℕ)(b:ℤ) := P.migrate (ι) (P.flash n) b
private def R₂ (n:ℕ)(b:ℤ) := (((P.migrate (ι) (P.flash n) (-b)).mirror 3 0).mirror (ι) 0)
omit A Y p in
private lemma postage1 (n:ℕ)(b:ℤ): P.stockS Z (P.migrate (ι) (P.flash n) b) = P₁ b n:= (P.acrossStocks Z k.val ..).symm
omit A Y p in
private lemma postage2(n:ℕ)(b:ℤ): P.stockS Z (R₂ (P:=P) k n b)= P₂ b n:=by
 simp only [R₂,← P.acrossStocks,← P.mirror_stock]
variable {C₀:ℕ→ℤ}{z:ℝ}(v:0<z)(H:P.bargain r C₀ z)
include H v
local notation "x₁" i:max=> R₁ (P:=P) k (r i) (C₀ i)
local notation "x₂" i:max=> R₂ (P:=P) k (r i) (C₀ i)
private lemma seats₁ : ∃ t:ℝ,∀ᶠ i:ℕ in atTop,∀ w:P.birthF k.val (c i) (P.stockS Z (x₁ i)), ‖P.viewF k.val (χ) (c i) w‖ ≤ t:=by
 let F(i):=P.flash (r i); let ω:Gaia:= (2:ℝ) • ε; let u:=P.heights_here r A.eager A.unitSize; have w':remainsR r F false 0:= fun i=>⟨rfl,rfl⟩
 let j:Gaia:= z • basis k.val; let X:= ε+j; let X':= ω+j
 have he: marchesR r (fun i=>x₁ i) X X':=P.marching k.val r F ε ω u C₀ z H
 have hp: remainsR r (fun i=>x₁ i) false 0:=P.passRemain k.val r _ false 0 w' C₀
 have H₁:X≠X':=by intro t; have he:=congrArg (fun a:Gaia=> a (3:Axis)) t; simp [X,X',ω,j] at he
 have H₃:0<X k.val:=by simp [X,j,k.property,v]
 have H₄:0<X' k.val:=by simp [X',ω,j,k.property,v]
 exact other_hint Z k.val A Y p he hp H₃ H₄ H₁
private lemma seats₂ : ∃ t:ℝ,∀ᶠ i:ℕ in atTop,∀ w:P.birthF k.val (c i) (P.stockS Z (x₂ i)), ‖P.viewF k.val (χ) (c i) w‖ ≤ t:=by
 let F(i):=P.flash (r i); let ω:Gaia:= (2:ℝ) • ε; let u:=P.heights_here r A.eager A.unitSize; have w':remainsR r F false 0:= fun i=>⟨rfl,rfl⟩
 let D:= inversion 3; let D':= inversion k.val; let L:= ε + (-z) • basis k.val; let L':=ω + (-z) • basis k.val; let W₀:=D' (D L); let W₁:=D' (D L')
 let V₀(i:ℕ):= P.migrate k.val (F i) (-C₀ i); have hu:=P.marching k.val r F ε ω u _ _ (P.minusPath r C₀ z H); have hy:=P.passRemain k.val r F _ _ w' (-C₀);
 have hw:W₀ ≠ W₁:= by intro t; have he:=congrArg (fun a:Gaia=> a (3:Axis)) ((inversion 3).injective ((D').injective t)); simp [L,L',ω] at he
 have hf : marchesR r (fun i=>x₂ i) W₀ W₁:= revolve k.val r (fun i=>(V₀ i).mirror 3 0) (D L') (D L) (revolve 3 r V₀ L L' hu A.eager) A.eager
 have hg : remainsR r (fun i=>x₂ i) (axis_val (ι) (axis_val 3 false)) (Lead.shuffle (ι) (Lead.shuffle 3 0)):= turnsZ k.val r (fun i=>(V₀ i).mirror 3 0) _ _ (turnsZ 3 r V₀ _ _ hy)
 have H₅:0<W₀ k.val:=by simp [W₀,L,D',D,inversion,k.property,v]
 have H₆:0<W₁ k.val:=by simp [W₁,L',ω,D',D,inversion,k.property,v]
 exact other_hint Z k.val A Y p hf hg H₅ H₆ hw
#check @seats₁
lemma seats_book : ∃ t:ℝ,0<t∧∀ᶠ i:ℕ in atTop,(P.birthF k.val (c i) (P₁ (C₀ i) (r i))) ∧ (P.birthF k.val (c i) (P₂ (C₀ i) (r i))) ∧ (∀ x':P.birthF k.val (c i) (P₁ (C₀ i) (r i)), ‖P.viewF k.val (χ) (c i) x'‖≤ t) ∧ (∀ x':P.birthF k.val (c i) (P₂ (C₀ i) (r i)), ‖P.viewF k.val (χ) (c i) x'‖≤ t):=by
 let M₁:ℝ:= (seats₁ Z k A Y p v H).choose; have h₁:= (seats₁ Z k A Y p v H).choose_spec
 let M₂:ℝ:= (seats₂ Z k A Y p v H).choose; have h₂:= (seats₂ Z k A Y p v H).choose_spec
 refine ⟨max 1 (max M₁ M₂),lt_of_lt_of_le zero_lt_one (le_max_left ..),?_⟩
 filter_upwards [h₁,h₂,(P.countPath r C₀ z H v A.eager).eventually_ge_atTop ((ℓ:ℤ)+1)] with i h₁ h₂ h
 have he:P.birthF k.val (c i) (P₁ (C₀ i) (r i)) ∧ P.birthF k.val (c i) (P₂ (C₀ i) (r i)):= P.earningK Z k (c i) (r i) (C₀ i) (by have hp:=_root_.le_add_of_nonneg_right (a:=P.crewB (C₀ i)) (show (0:ℤ) ≤ P.crewB (C₀ i) from (show _≤P.crewB (C₀ i) from le_trans (show (0:ℤ) ≤ (ℓ:ℤ)+1 from (by positivity)) h)); rw [two_mul]; exact h.trans hp)
 refine ⟨he.1,he.2,?_,?_⟩
 · -- use proof ext but not rw at type-heavy goal?
   intro p; have he:= postage1 (P:=P) Z k (r i) (C₀ i); let q:P.birthF k.val (c i) (P.stockS Z (R₁ (P:=P) k (r i) (C₀ i))):= Eq.mpr (congrArg (P.birthF k.val (c i)) he) p; have h:=P.identical_F _ (χ) _ q p he; exact le_trans ((congrArg norm h).ge.trans (h₁ q)) ((le_max_left ..).trans (le_max_right ..))
 intro p; have he:= postage2 (P:=P) Z k (r i) (C₀ i); let q:P.birthF k.val (c i) (P.stockS Z (R₂ (P:=P) k (r i) (C₀ i))):= Eq.mpr (congrArg (P.birthF k.val (c i)) he) p; have h:=P.identical_F _ (χ) _ q p he; exact le_trans ((congrArg norm h).ge.trans (h₂ q)) ((le_max_right ..).trans (le_max_right ..))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.seats_book
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.marginal
