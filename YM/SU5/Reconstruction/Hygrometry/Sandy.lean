import YM.SU5.Reconstruction.Hygrometry.OrbitTurn
import YM.SU5.Reconstruction.Hygrometry.Libretto
import YM.CF.Emu.Well
import YM.CF.Buffered.Piling
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Pressure RG Vale Vale.Grace Paige Peaks Vault Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open Mir Reflect RP
open scoped ComplexOrder Classical
variable {K: Teller group} {P:Patch}{B:Side}{e:ℝ}{Y:Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(uK:1 ≤ K.j)
variable {R:ℕ→ℝ}(f:ℕ→ Side)
local notation "S" i:max=> CSide (f i) B
variable (Yg:Yard (fun i=>CSide (f i) B) R)
variable {α β:Type*} [Fintype β]
namespace Overlook
include Yg
lemma boundsFrom (x:ℕ) : ∀ᶠ i:ℕ in atTop,x ≤ (CSide (f i) B).val:= by
 have he: Tendsto (fun i=>(↑(CSide (f i) B).val:ℝ)) atTop atTop:= roam_n (B:=B) (f:=f) Yg -- tune
 exact (he.eventually_ge_atTop (x:ℝ)).mono (fun i l=> (by change ↑x ≤ (↑(CSide (f i) B).val:ℝ) at l; exact_mod_cast l))
include g uK
lemma resolutionM (W:ℕ→Jill.Male): ∀ᶠ i in atTop,A.roundZ ≤ (CSide (f i) B).val ∧ Pad K.j (CSide (f i) B) ∧ Sea (latPose K.j (W i) (CSide (f i) B)) (changeM A (1:Skin (f i) B) (W i)) := by
 obtain ⟨b,d⟩:= gave K.j uK; filter_upwards [boundsFrom f Yg b,boundsFrom f Yg A.roundZ] with i h v; have he:=d _ (Yg.even i) h; exact ⟨v,he,overhead A g v he _⟩
omit g uK
variable (P₁:Agenda α R)(a:Axis)
lemma scheduled (i:α)(e:0<P₁.posV i a): ∀ᶠ k in atTop, wrap (S k) (P₁.appointments k i)∈ posY (f k) B a:=by
 let x(n):= P₁.appointments n i a; let y(n):=(x n:ℝ)/R n; have he:Tendsto y atTop (𝓝 (P₁.posV i a)):= atlas_tend.1 (P₁.timeR i) a
 have ht:= (he.mul Yg.water); rw [mul_zero] at ht
 filter_upwards [he.eventually (lt_mem_nhds e),ht.eventually (gt_mem_nhds (show 0 < Real.pi/2 from by positivity))] with n hp h
 have hr:=Yg.pos n; have hl :0<(x n:ℝ) :=by have ht:(0:ℝ)< (x n:ℝ)/R n:=hp; rw [lt_div_iff₀ hr, zero_mul] at ht; exact ht
 have hb:(S n).val=2*oddSize (f n) B:= RP.suff (f n) B; have h₁:0<x n:=by exact_mod_cast hl
 have hf:(x n)< (oddSize (f n) B:ℕ):=by
    suffices hk : (x n:ℝ)< (oddSize (f n) B:ℕ) by exact_mod_cast hk
    change (x n:ℝ)/R n*(R n*pinch (S n))<_ at h; have hm : 0<(oddSize (f n) B:ℝ):=by exact_mod_cast RP.oddP (m:=f n) (B:=B)
    unfold Ember.pinch at h; rw [hb] at h; push_cast at h; field_simp at h; nlinarith only [h, hr,hm,Real.pi_pos] -- tune
 apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩; rw [wrap_here]
 change ((x n:Per (S n))).val < _
 rw [Buffered.Region.int_val _ h₁.le (by omega)]; omega
-- just instantiate Plot, no change History by gauge sharp election. NEED not require liquidity rotated probe.F
lemma creates (X:α→ Gaia): ∃ (P₁:Agenda α R), P₁.posV=X:= by
 -- any wing.Plot
 let i:SU.Slot:= (0,Sum.inr 0); obtain ⟨p,d,_⟩:= Emu.fig (B:=B) (f:=f) (fun _=>⟨0,i,1⟩) X Yg; exact ⟨⟨p.atV,p.z,p.voyage,p.port⟩,d⟩
include g uK
variable (q:BudgetPoint)(b:Bool)(F:β→ List α)(u:β→ℂ)(Z:α→Personality)
include q A
private lemma straight_ticks (p:∀ i,face_axis a (P₁.posV i))(h:∀ i,wheat (F i)=b): 0 ≤ harvestCost (applaud a) (land_axis a) P₁.posV Z F u b:=by
 let Y':= nextAxis P₁ a Yg p
 let Tz (i):= changeM A (1:Skin (f i) B) babyM
 let U(i):= utter (P₁.appointments i) Z (S i) (R i) F u
 let K' := fun _:ℕ=> babyM
 have ht:= resolutionM A g uK f Yg K'
 have hx := tendedCost (applaud a) (land_axis a) P₁.posV Z F u b P₁ Y'.val Y'.property.1 Y'.property.2 uK K' Yg Tz (ht.mono fun i t=>t.2.2)
 have he (i:β): ∀ᶠ k in atTop,∀ x∈F i, wrap (S k) (P₁.appointments k x)∈ posY (f k) B a:=by
    classical
    simp_rw [← List.mem_toFinset]; exact ((F i).toFinset.eventually_all).2 (fun x _=> scheduled f Yg P₁ a x (p x))
 apply ge_of_tendsto hx; filter_upwards [ht, eventually_all.mpr he] with i p t
 have hv:= straightW (m:=f i) A p.1 g q a p.2.1 uK (bookedUp (P₁.appointments i) Z (R i) F u a b h t); exact hv
lemma continuum (X:α→ Gaia)(p:∀ i, face_axis a (X i))(h:∀ i,wheat (F i)=b): 0 ≤ harvestCost (applaud a) (land_axis a) X Z F u b := by
 obtain ⟨t,rfl⟩:= creates f Yg X; exact straight_ticks A g uK f Yg t a q b F u Z p h
lemma tilted (U:Ramp)(X:α→ Gaia)(p:∀ i,face_tilt U (X i))(h:∀ i,wheat (F i)=b): 0 ≤ harvestCost (whisper U) (land_tilt U) X Z F u b:=by
 let s:= Windward.survey U; let L:= Windward.equip U; let Y:= (s ∘ X); let C:= U.a; let V:= Sum.elim (land_tilt U ∘ X) X; let Z' := Packed (whisper U) Z
 have he:= continuum A g uK f Yg C q b F u (L∘Z) Y (fun i=> Windward.face U _ (p i)) h; apply le_trans he; refine le_of_eq ?_; have hp:Packed (applaud C) (L ∘ Z)=L ∘ Z':= funext fun x=>by cases x <;> first | exact Windward.cross_turn U _ | rfl
 have ht: Sum.elim (land_axis C ∘ Y) Y=s∘ V:=funext fun x=>by cases x <;> first | exact Windward.chronod U _ | rfl
 unfold harvestCost; rw [hp,ht]; simp_rw [show ∀ X Z T, PriceCliff.quantum (α:= α ⊕ α) (s ∘ X) (L ∘ Z) T=PriceCliff.quantum X Z T from fun _ _ _=>Windward.ticket U _ _ _]; rfl
end Overlook
end YM.CF.Hygrometry
