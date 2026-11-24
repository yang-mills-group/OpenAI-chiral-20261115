import YM.SU5.FiniteGaugeData.SalonG.Bout
import YM.SU5.FiniteGaugeData.Chrono.Strobel
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "D"=> Decko Y h a
local notation "U₁"=>W Kₜ
local notation "π"=>nectar Y h s W' R a
variable {x f g:W (tent Y h)}(y z:Decko Y h a)
abbrev Plan (d:ℕ)(x:W (tent Y h)): Prop := ∃ S, Studio a 0 (yard Kₜ d) (reserve Λ l) S∧ Locator Kₜ x S
variable (v':Plan Y h a d f)
namespace Plan
variable {d a}
lemma other (v':Plan Y h a d f) : Plan Y h a d (mateW Kₜ a d f):= ⟨_, arbour v'.choose_spec.1,locate_cold Kₜ _ a _ v'.choose_spec.2⟩
lemma subsidy (p:Plan Y h a d f)(c:ℂ): Plan Y h a d (c • f):= ⟨_,p.choose_spec.1, locate_scale _ _ _ p.choose_spec.2⟩
lemma plus (p:Plan Y h a d f)(t:Plan Y h a d g): Plan Y h a d (f+g):= ⟨_,p.choose_spec.1.union t.choose_spec.1,locate_sum _ _ (locate_sub _ p.choose_spec.2 subset_union_left) (locate_sub _ t.choose_spec.2 subset_union_right)⟩
include W' R
local notation "V" f:max=> ascended Y h s W' R n f
lemma rides (p:Plan Y h a d f): Plan Y h a (energyS Λ d n) (ascended Y h s W' R n f):= ⟨_, series_geo Y h p.choose d n a p.choose_spec.1,ascend_loc Y h p.choose s n f p.choose_spec.2 W' R⟩
lemma upgraded (p:Plan Y h a d f): Plan Y h a (Λ.R.L.val*d) (Charm.next Y h s W' R f):= by
 have he:= Plan.rides Y h s 1 W' R p; rw [show energyS Λ d 1=(Λ.R.L.val*d) from by unfold energyS; rw [pow_one]] at he; exact he
end Plan
-- Decko-level action contains both buffers
variable (q:0<d)
include v'
lemma scoreP : Canaan Y h a f 0:= ⟨v'.choose,v'.choose_spec.1.ahead,v'.choose_spec.2⟩ -- that orientation
/-- Decko slab acts on half-supported reps. -/
abbrev embark : Decko Y h a→ₗ[ℂ] Decko Y h a:= (LinearMap.mulLeft ℂ (⟨f,scoreP Y h a d v'⟩:Decko Y h a)).comp (hoist Y h a a d (fun _=>Nat.cast_nonneg' _))
lemma embarks : (embark Y h a d v' y).val= Swing Kₜ a d f y.val:= rfl
variable {c:ℂ}
lemma fee_scale (w:Plan Y h a d (c • f)): embark Y h a d w y=c• embark Y h a d v' y:= Subtype.ext (Algebra.smul_mul_assoc c f (clockW Kₜ a d y.val)) -- orient check
local notation "Σ" n:max=>store Y h n W' R a A
include W' R
lemma embark_next : nectar Y h s W' R a (embark Y h a d v' y)= embark Y h a (Λ.R.L.val*d) (Plan.upgraded Y h s W' R v') (nectar Y h s W' R a y):= by
 apply Subtype.ext; change Charm.next Y h s W' R _= _; rw [embarks,embarks]; unfold Swing; obtain ⟨T,e,p⟩:=y.property; let S:= v'.choose; let m:= hour Kₜ T a d
 have he:Ahead a (yard Kₜ d) (reserve Λ l) m:= by have he:= flightW Kₜ T a 0 (d:ℤ) e; rw [yard_le,zero_add] at he; exact he
 rw [Charm.separate Y h S m s W' R v'.choose_spec.2 (loc_tic Kₜ T a _ p) (cover_separate a v'.choose_spec.1.behind he),promote_clock,Nat.cast_mul]; rfl
local notation "X'"=> embark Y h a d
lemma rank_bend : inner ℂ ((Σ s) y) ((Σ s) (embark Y h a d v' z))= inner ℂ ((Σ s) (embark Y h a d (Plan.other Y h v') y)) ((Σ s) z):=by
 rw [lawStore,lawStore,embarks,embarks]; change E _ (Fold ..).val = _; rw [adjoint_frame, invariantW Y h s a _ W'] -- explicit Fold
local notation "δ" n:max=> energyS Λ d n
local notation "F" f:max n:max=> ascended Y h s W' R n f
variable (d':ℕ)(Q:ℝ)
def appointed : Decko Y h a→ₗ[ℂ] Decko Y h a := embark Y h a (energyS Λ d n) (Plan.rides Y h s n W' R v')
lemma appointed_val : (appointed Y h s a d n W' R v' y).val= Swing Kₜ a (δ n) (F f n) y.val:= rfl
lemma appointing : appointed Y h s a d 0 W' R v' y= embark Y h a d v' y:=by apply Subtype.ext; rw [appointed_val, embarks,energy_zero]; rfl
lemma appoint_next : nectar Y h (s+n) W' R a (appointed Y h s a d n W' R v' y)=appointed Y h s a d (n+1) W' R v' (nectar Y h (s+n) W' R a y):=by
 unfold appointed; rw [embark_next]; apply Subtype.ext; simp only [embarks]; rw [energy_step]; rfl
lemma appoint_scale (w:Plan Y h a d (c • f)) : appointed Y h s a d n W' R w y=c • appointed Y h s a d n W' R v' y:=by
 apply Subtype.ext; rw [Subalgebra.coe_smul,appointed_val,appointed_val,map_smul]; unfold Swing; rw [Algebra.smul_mul_assoc]
omit v' in
lemma iceWing : mateW Kₜ a (energyS Λ d n) (ascended Y h s W' R n x) = ascended Y h s W' R n (mateW Kₜ a d x):=by
 induction n with
 | zero=> rw [energy_zero]; rfl
 | succ n ih=>
    change mateW Kₜ a _ (Charm.next Y h (s+n) W' R _)= Charm.next Y h (s+n) W' R (ascended Y h s W' R n (mateW Kₜ a d x)); rw [← ih]; unfold mateW; rw [next_mir,energy_step,Nat.cast_mul]; congr 2; unfold Heat.gaugeShift; ring
lemma ice_bend : inner ℂ ((Σ (s+n)) y) ((Σ (s+n)) (appointed Y h s a d n W' R v' z)) = inner ℂ ((Σ (s+n)) (appointed Y h s a d n W' R (Plan.other Y h v') y)) ((Σ (s+n)) z) := by
 unfold appointed; rw [rank_bend]; congr 2; apply Subtype.ext; rw [embarks,embarks,iceWing] -- dependent
-- for uniform norm tests
omit v' R W'
abbrev warmV (d:ℕ)(x:Decko Y h a): Decko Y h a:= hoist Y h a a (d*(0+2):ℕ) (fun _=>Nat.cast_nonneg' _) x
lemma warm_fold : openQ Kₜ a d 0 f y.val=(warmV Y h a d y).val:=by rw [open_small]; rfl
include v'
lemma warm_pay : openQ Kₜ a d 1 f y.val=(embark Y h a d v' (warmV Y h a d y)).val:=by rw [operate_succ,ream_zero,warm_fold,embarks]
local notation "p'" n:max=> Plan.rides Y h s n W' R v'
local notation "τ" n:max=>warmV Y h a (energyS Λ d n)
include W' R
lemma board_echo0 : ‖store Y h (s+n) W' R a A ((τ n) y)‖^2=(E (s+n) (EchoF Y h a (energyS Λ d n) 0 y.val (ascended Y h s W' R n f)).val).re:=by rw [normStore]; unfold EchoF; rw [warm_fold]
lemma board_echo : ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R v' ((τ n) y))‖^2=(E (s+n) (EchoF Y h a (energyS Λ d n) 1 y.val (ascended Y h s W' R n f)).val).re:=by
 rw [normStore]; unfold EchoF; rw [warm_pay ..]; rfl -- p' not inferred?
 exact Plan.rides Y h s n W' R v'

include A q
lemma valued (p:Gallery Y h s a d u v f): ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R v' (warmV Y h a (energyS Λ d n) y))‖ ≤ ‖store Y h (s+n) W' R a A (warmV Y h a (energyS Λ d n) y)‖:= by
 obtain ⟨T,r,t⟩:=y.property
 apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; rw [board_echo Y h s a d n W' R A y v', board_echo0 Y h s a d n W' R A y v']; exact abroad Y h v'.choose T s a d n W' R y.val t r f q v'.choose_spec.1 p v'.choose_spec.2
omit v' in
lemma adaptive (v':Studio a 0 (yard Kₜ d) (reserve Λ l) S)(B C ε:ℝ)(hB:0≤B)(w:0<ε):∀ᶠ i in atTop,∀ᶠ k in atTop,∀ (f:W (tent Y h))(e:Locator Kₜ f S), ‖reading Kₜ S f e‖≤ B→ Credential Y h s (u i) (v k) a d C f→
    ‖store Y h (s+n) W' R a A (appointed Y h s a d n W' R (f:=f) ⟨S,v',e⟩ (warmV Y h a (energyS Λ d n) y))‖^2 ≤ ‖store Y h (s+n) W' R a A (warmV Y h a (energyS Λ d n) y)‖^2+ ε := by
 obtain ⟨T,r,t⟩:=y.property
 filter_upwards [issuance Y h S T s a d n W' R y.val t r C B ε q v' w hB] with i y'; refine y'.mono (fun k p f e Q? V₁=>?_); rw [board_echo Y h s a d n W' R A y _, board_echo0 Y h s a d n W' R A y (f:=f) ⟨S,v',e⟩]; exact p f e Q? V₁
#print axioms ice_bend
#print axioms valued
#print axioms adaptive
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
