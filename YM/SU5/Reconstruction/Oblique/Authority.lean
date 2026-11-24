import YM.SU5.Reconstruction.Oblique.TwistedSlits
import YM.SU5.Reconstruction.Oblique.RunningClock
/-! # Bilateral angular restore IN THE NET on Hoik. Reduces need for actual physical spacetime assertions to analytical price.Plan Read. Does not buy it yet. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
open LightBudget Chambers -- provide BootBacking later
local notation "Fs" i:max=> fort Y H V G.history G.clipped i false (C i) (wk i)
local notation "N" i:max=>Domain Y H G false (flank i 0)
local notation "V₀" i:max=>coreOs Y H V G i (C i) (wk i)
local notation "X₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (wk i)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (wk i)
local notation "℘" i:max=>Picket.trans (S₀ i)
local notation "Qv" i:max=> Follows Y H V G i (C i) (wk i)
local notation "π" i:max=> opCarries Y H V G i (C i) (wk i)
open Crease Anvil BridgeClub Quartz.Ship
variable (B:BoostBacking Y H V G C a χ){s:Signed}(A:Pave Y H V G C a χ s){j z:Axis}(t:Oriented s j z)
variable (v u : placement Λ)
local notation "L"=>motor Y H V G C a χ B A t
local notation "Θ"=>(L).conjStarAlgEquiv
local notation "Lv" i:max=>Crease.floor Y H V G C a χ i
lemma preserveNorm {F T:Hilbert}(b:F≃ₗᵢ[ℂ]T){x:ℕ→F.Op}{A:F.Op}(m:Limited atTop x A) : Limited atTop (fun n=> b.conjStarAlgEquiv (x n)) (b.conjStarAlgEquiv A):=by
 refine ⟨by simpa only [unit_norms] using m.uniform,fun i j=>?_⟩
 obtain ⟨p,rfl⟩:=b.surjective i; obtain ⟨q,rfl⟩:=b.surjective j; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]; exact m.confirms ..
local notation "Φ" => newstart s v u
local notation "Xu" => newwidth s u
include B A t
lemma missionPermit (h:ℕ→ marks (timeMesh Λ)) (f:ℕ→ Sky (tent Y H)) (X:(Fs j).Op) (Q:ℕ→(J₀ j).Op)(e:Slip Y H V G C a χ j f h Q X) : ∃ T:ℕ→(J₀ z).Op, Slip Y H V G C a χ z (fun n=> A.shift (f n)) h T (Θ X) ∧ ∀ n,(π z) (T n)= Θ ((π j) (Q n)):=by
 choose p W V' using fun n=> follows_move Y H V G C a χ B A t (h n) (e.phase n) (Q n) (e.stays n); exact ⟨p,⟨W,e.phase,e.short,by simp_rw [V']; exact preserveNorm (L) e.propitious⟩,V'⟩
lemma appointed_screen (X:(Fs j).Op)(p:Sight Y H V G C a χ j v u X): Sight Y H V G C a χ z (newstart s v u) (newwidth s u) (Θ X):=by
 obtain ⟨q', h,x,D',e,u₀,t₀⟩:=p
 have he(i:Axis)(p:s.perm i≠z): i≠ j:= fun g=> p (g.symm ▸ t.peer)
 obtain ⟨w,hb,-⟩:= missionPermit Y H V G C a χ B A t h x X D' e
 refine ⟨fun i p=>?_,h,(fun n=> A.shift (x n)),w,hb,?_,fun i p=>?_⟩
 · obtain ⟨i,rfl⟩:=s.perm.surjective i; rw [crate]; exact q' i (he i p)
 · intro n; rw [← motor_tarp t]; exact (A.shifts ..).1 (u₀ n)
 obtain ⟨i,rfl⟩:= s.perm.surjective i; obtain ⟨Y',g,K',B'⟩:= t₀ i (he i p)
 -- tune B shadows
 choose T W T' using fun n=> turned_width Y H V G C a χ B A (v i) (u i) (q' i (he i p)) i (x n) (Y' n) (g n)
 rw [crate,newAt]; exact ⟨T,W,K',fun n=> (T' n).trans_le (B' n)⟩
lemma motor_parcel(x:E4)(T:(Fs j).Op): Θ (parcelUp (S₀ j) x T)= parcelUp (S₀ z) (sailPoint s x) (Θ T):=by
 unfold parcelUp; rw [map_mul,map_mul,allotted,allotted,sail_neg]
theorem motor_wing (U:Set E4)(M:(Fs j).Op)(p:M∈ Wing Y H V G C a χ j U) : Θ M∈ Wing Y H V G C a χ z (sailPoint s '' U):=by
 rcases p with ⟨v,u,x,Q,r,h,rfl⟩; refine ⟨newstart s v u,newwidth s u, sailPoint s x, Θ Q, appointed_screen Y H V G C a χ B A t v u Q r, ?_,motor_parcel Y H V G C a χ B A t x Q⟩; rw [← motor_data t]; rintro _ ⟨_,⟨i,b,rfl⟩,rfl⟩; exact ⟨i+x,h ⟨i,b,rfl⟩, sail_add s i x⟩
-- General, different spaces
omit t B A in
private lemma twoFace {X QD:Hilbert}{S:Set X.Op}{T:Set QD.Op}(p:∀ x∈S,star x∈ S)(q:∀ y∈T,star y∈T) (F:X≃ₗᵢ[ℂ] QD)(v:∀ x∈ S,F.conjStarAlgEquiv x∈ T){x:X.Op}(b:x∈ Auditorium S):F.conjStarAlgEquiv x∈Auditorium T:= by
   rw [←SetLike.mem_coe,lobby T q]; rw [←SetLike.mem_coe,lobby S p] at b; let L':= F.conjStarAlgEquiv
   intro t k; obtain ⟨u,r⟩:= L'.surjective t; change L' u=t at r; subst t; have hs:u∈ Set.centralizer S := by
      intro y g; apply L'.injective; rw [map_mul,map_mul]; exact k (L' y) (v y g)
   change L' u * L' x= L' x* L' u; rw [←map_mul,←map_mul,b u hs]
lemma motor_into (U:Set E4)(M:(Fs j).Op)(p:M∈ (Lv j) U): Θ M∈ (Lv z) (sailPoint s '' U) := twoFace (wing_star Y H V G C a χ B j U) (wing_star Y H V G C a χ B z _) (L) (motor_wing Y H V G C a χ B A t U) p
-- Entire-region geometric equality in all such Frames
theorem motor_cross (U:Set E4)(M:(Fs j).Op): M∈(Lv j) U ↔ Θ M∈ (Lv z) (sailPoint s '' U):= by
 refine ⟨motor_into Y H V G C a χ B A t U M,fun v =>?_⟩
 have ht:=motor_into Y H V G C a χ B (Pave.reflected Y H V G C a χ A) t.return_z _ _ v
 rw [motor_return Y H V G C a χ B A t,run_base,Set.image_image] at ht; simpa only [sail_inverse, Set.image_id'] using ht
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
