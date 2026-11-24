import YM.SU5.Reconstruction.Vermont.Emulate
import YM.SU5.Reconstruction.Vermont.Along
import YM.SU5.Reconstruction.Vermont.Harbor
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "D'" i:max=> Domain Y H G false (flank i 0)
local notation "Tx" => timeMesh Λ
local notation "Q" i:max=>Follows Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open Lens Sail
local notation "Π₀" i:max=> opCarries Y H V G i (C i) (w i)
local notation "L0" => Sight Y H V G C a χ j
local notation "Fz" => (Vo z)
variable {x: Sky (tent Y H)} (d v0 : marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (s t:marks (timeMesh Λ))
  (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')
local notation "ζ"=> floor Y H V G C a χ j
variable (Q': Set E4)(c₀:ℝ)
variable (A0:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (Φ: A0 (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) =
          opCarries Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) A (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))))
variable {T':ℕ→(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable (c :ℝ≥0)
  (p0 : ∀ n, Script (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (floor Y H V G C a χ j Q') (T' n) (Real.toNNReal (s:ℝ)) c)
  (p1 : Limited atTop T' A0)
  (v:∀ x∈Q',|x j|+x z ≤ c₀) (e:s<t)(w0:0≤ (s:ℝ))
local notation "Φ₀" => far Y H V G j (C j) (w j) z d false
local notation "Tt"=> Real.toNNReal (t:ℝ)
local notation "E0"=> Real.toNNReal (s:ℝ)
local notation "A1"=> (Π₀ j) A
local notation "Ω"=> (Ω₀ j)
local notation "S"=> (S₀ j)
include F b v e w0 p0 p1 f0 f1 Φ
lemma affordable (u u':Axis→Gt)(B:(G₀ j).Op) (x:Sight Y H V G C a χ j u u' B)(h1: d+v0 < u z)(h2:c₀+1 < (u z:ℝ)) : ∀ t':ℝ≥0,0<t'→ t'< Tt-E0 → A0 ((S).E t' (B Ω)) = A1 ((S).E t' (B Ω)):= by
 have Ht:0 < (t:ℝ):= lt_of_le_of_lt w0 e; let vt:= Real.toNNReal_pos.mpr Ht; have eh:E0<Tt:= by exact_mod_cast ((Real.toNNReal_lt_toNNReal_iff Ht).mpr e) -- tune
 have h:∀ X∈(ζ Q'),∀ t':ℝ, |t'|≤ 1→ Commute X (LorTime S t' B):= fun X a t0 w1=> spending Y H V G C _ χ F j z b u u' x Q' c₀ t0 v (by linarith) X a
 intro κ κ0 t; refine Lens.buys S A0 B Tt E0 Ω Φ₀ (far_dense Y H V G j (C j) (w j) z b.symm (F.present j) (F.forward j) d false) vt eh (seat_cools Y H V G C a χ j) A1 Φ (fun p _=> ?_) (fun p px=>?_) κ κ0 t
 · exact ⟨1,zero_lt_one,survives S A0 B Tt E0 1 p Ω h zero_lt_one eh p0 p1⟩
 exact see_edges Y H V G C a χ F j z b d v0 A A' s _ u' u f0 f1 B x h1 e w0 p px -- underscore t shadow

lemma imprint_pin (B:(G₀ j).Op)(p:B∈ pinpoints Y H V G C a χ j z) : A0 (B Ω)= A1 (B Ω):=by
 obtain ⟨u,r,V',_,k,h⟩:= p
 let C0:= max ((d:ℝ)+(v0:ℝ)-(u z:ℝ)) (c₀+1-(u z:ℝ)); have ht: 0<(t:ℝ):= lt_of_le_of_lt w0 e; have eh:E0<Tt:= (Real.toNNReal_lt_toNNReal_iff ht).mpr e
 have hV : ∀ (R:E4),(∀ i,i ≠ j → i≠z→ R i=0) → A0 (Picket.trans S R (V' Ω))=A1 (Picket.trans S R (V' Ω)):=by
   intro R H'; refine Lens.traverses S A0 A1 (V' Ω) b.symm Gt (daylight Tx) (F.forward j) C0 (Tt-E0) (tsub_pos_of_lt eh) ?_ R H'
   intro i wI k0 t0 c' φ; have k1 : (d:ℝ)+(v0:ℝ)-(u z:ℝ)< i := (le_max_left ..).trans_lt k0; have k2: c₀+1-(u z:ℝ)< i := (le_max_right ..).trans_lt k0
   let i': Gt:=⟨i,wI⟩; rw [← keepsLaw Y H V G C a χ j]
   let Pt:= u+eject z i'; exact affordable Y H V G C a χ F j z b d v0 A A' s t f0 f1 Q' c₀ A0 Φ c p0 p1 v e w0 Pt r (parcelUp S ((i:ℝ) • basis z) V') (aheadSight Y H V G C a χ F j z b u r i' V' k) (show (d:ℝ)+(v0:ℝ)< (Pt z:ℝ) from (by unfold Pt; simp only [Pi.add_apply, eject_at, AddSubgroup.coe_add]; change _ < _+i; linarith)) (by unfold Pt; simp only [Pi.add_apply, eject_at, AddSubgroup.coe_add]; change _ < _+i; linarith) t0 c' φ
 rcases h with h|⟨q,v,dq,rfl⟩
 · subst V'; let b' := hV 0 (fun _ _ _=> rfl); rw [show Picket.trans S 0=1 from (S).unit.origin] at b'; exact b'
 rw [keepsLaw]; exact hV _ (fun i hi h=> (by unfold stern; rw [Picket.others _ _ _ hi h]; simp [h]))

-- Rank on this pair only
lemma ascertain (x:Creased Y H V G C a χ F j z b) : A0=A1:=by
 obtain ⟨K1,Z,k⟩:= F.circles _ _ b.symm; let u':= engaged Y H V G C a χ F j z b Z k x
 let R':= Z.plume; ext1 p; refine closure_minimal ?_ (isClosed_eq A0.continuous (A1).continuous) (_root_.YM.CrossedFrame.polar_dense (CrossedFrame.Clasp.plume_self Z) (CrossedFrame.Clasp.plume_inj Z) p) -- explicit open?
 rintro y ⟨w1,rfl⟩; let F':=(A0 - A1).comp R'; let Q0:= LinearMap.ker (F'.toLinearMap); have h : IsClosed (Q0:Set (G₀ j)):= isClosed_eq F'.continuous continuous_const
 suffices he:w1∈ Q0 by
   change A0 (R' w1)=_; exact sub_eq_zero.mp he
 apply u'.economize Q0 h _ Q0.zero_mem (fun _ h _ p=> Q0.add_mem h p) (fun _ h x=> Q0.smul_mem x h) w1
 intro X aX; change A0 ((Z.plume) (BridgeClub.label (Flare Y H V G C a χ F j z b) Ω X)) - A1 ((Z.plume (BridgeClub.label (Flare Y H V G C a χ F j z b) Ω X):(G₀ j)))=0; apply sub_eq_zero.mpr; rw [u'.pose X aX]; exact imprint_pin Y H V G C a χ F j z b d v0 A A' s t f0 f1 Q' c₀ A0 Φ c p0 p1 v e w0 X aX -- needs change
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
