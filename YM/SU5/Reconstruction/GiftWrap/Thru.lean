import YM.SU5.Reconstruction.GiftWrap.GammaRay
import YM.SU5.Reconstruction.GiftWrap.Sear
/-! # Pricing through far reservations -/
set_option autoImplicit false
set_option maxHeartbeats 300000
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
local notation "X" i:max=> OSvector Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "m₁" => FirstWindows.move (tent Y H)
local notation "ℓ_"=>osValue Y H V G a (C a) χ
open BridgeClub Reflector
namespace Crease
variable (F: BoostBacking Y H V G C a χ)
variable (j z:Axis) (b:j≠z)
open CrossedFrame
local notation "U"=>flank j 0∩flank z 0
local notation "Λ₁" i:max=>onceLens Y H V G C a χ i
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Tm" i:max=> Picket.trans (S₀ i)
local notation "Ω" i:max=> Ω₀ i
local notation "Sq" => (S₀ j)
namespace Boots
local notation "lu" x:max=> (Tm j) ((x:ℝ) • basis z)
local notation "BC" => parcelUp Sq
open Lens Sail
local notation "lz" T₁:max => (Tm z) ((T₁:ℝ) • basis j)
local notation "N" => reserves Y H V G C a χ j z Z
local notation "Φ₀" x:max=> far Y H V G j (C j) (w j) z x false
variable {x: Sky (tent Y H)} (d v0 s t: marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')
variable (c :ℝ≥0)
variable (Q': Set E4)(c₀:ℝ)
variable (A0:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
variable {T':ℕ→(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable (p0 : ∀ n, Script (peninsula Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (floor Y H V G C a χ j Q') (T' n) (Real.toNNReal (s:ℝ)) c)
  (p1 : Limited atTop T' A0)
  (qW:∀ x∈Q',|x j|+x z ≤ c₀)
local notation "Tt"=> (ℜ t)
local notation "Aq"=> (Π j) A
variable (u v:Axis→marks (timeMesh Λ)) (L : (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
local notation "η" => u z+v z+(u z-(d+v0))
local notation "Θ₀" x:max=> (S₀ j).E x
variable (eL: Sight Y H V G C a χ j u v L)(g:d+v0<u z)(a₁:c₀+1 < (u z:ℝ))
local notation "ℓ" => ℜ s
include p F f0 f1 eL qW p0 p1 g a₁
lemma throughAll (w0:0≤ (s:ℝ)) (q:G₀ j)(r:q∈N η) (k:∀ t:ℝ≥0,A0 ((Θ₀ t) q)= Aq ((Θ₀ t) q)) (t₀:ℝ≥0)(σ:ℝ≥0) : A0 ((Θ₀ t₀) (L ((Θ₀ σ) q)))= Aq ((Θ₀ t₀) (L ((Θ₀ σ) q))):= by
 have t(k0 h0:Gt)(bk:0<(k0:ℝ))(bh:0<(h0:ℝ)) : A0 ((Θ₀ (ℜ k0)) (L ((Θ₀ (ℜ h0)) q)))= Aq ((Θ₀ (ℜ k0)) (L ((Θ₀ (ℜ h0)) q))):= by
    let t':= h0+k0+s; have vt0 : 0< ( ℜ t':ℝ≥0):= Real.toNNReal_pos.mpr (by unfold t'; change (0:ℝ)< _+_+_; linarith); have vℓ: s<t':=lt_add_of_pos_left _ (show 0<h0+k0 from add_pos (show (0:Gt)<_ from bh) (show (0:Gt)<_ from bk)) -- order
    let Xv:=ℜ t'; let U₀:=ℜ k0; let Hℓ:=ℜ h0
    have he:Xv=Hℓ+U₀+ℓ:=by unfold Xv U₀ Hℓ t'; exact (by apply NNReal.eq; simp only [AddSubgroup.coe_add, NNReal.coe_add, Real.coe_toNNReal _ w0,Real.coe_toNNReal _ bk.le,Real.coe_toNNReal _ bh.le, Real.coe_toNNReal _ (add_nonneg (add_nonneg bh.le bk.le) w0)])
    have huv: 0 < U₀:=Real.toNNReal_pos.mpr bk; have hℓ: 0<Hℓ:=Real.toNNReal_pos.mpr bh
    have ht : Xv - (U₀+ℓ)= Hℓ := by rw [he, add_assoc, add_tsub_cancel_right]
    have hox: ℓ < Xv:= by rw [he]; exact lt_add_of_pos_left _ (add_pos hℓ huv)
    have d':U₀ < Xv-ℓ := by rw [he, add_tsub_cancel_right]; exact lt_add_of_pos_left _ hℓ
    change A0 ((Θ₀ U₀) (L ((Θ₀ Hℓ) q)))= Aq ((Θ₀ U₀) (L ((Θ₀ Hℓ) q)))
    rw [← ht]
    let h:∀ B∈floor Y H V G C a χ j Q',∀ t':ℝ, |t'|≤ 1→ Commute B (LorTime Sq t' L):= fun B a0 t0 w1=> spending Y H V G C _ χ F j z b u v eL Q' c₀ t0 qW (by linarith) B a0
    refine buysAt Sq A0 L Xv ℓ q (Φ₀ d) (far_dense Y H V G j (C j) (w j) z b.symm (F.present j) (F.forward j) d false) (show 0<(Xv:ℝ) from vt0) hox Aq k (fun lp _=> ⟨1,zero_lt_one, survives Sq A0 L Xv ℓ 1 lp q h zero_lt_one hox p0 p1⟩) (fun lp hp=> ?_) U₀ huv d'
    exact wallCorner Y H V G C a χ F j z b Z p d v0 s t' A A' f0 f1 u v L eL g vℓ w0 lp hp q r
 let h(k0:Gt)(bk:0<(k0:ℝ)): A0 ((Θ₀ (ℜ k0)) (L ((Θ₀ σ) q)))= Aq ((Θ₀ (ℜ k0)) (L ((Θ₀ σ) q))):= by
   exact radiatory Tx (W:={i:ℝ≥0| A0 ((Θ₀ (ℜ k0)) (L ((Θ₀ i) q)))= Aq ((Θ₀ (ℜ k0)) (L ((Θ₀ i) q)))}) (isClosed_eq (A0.continuous.comp (((Θ₀ (ℜ k0)).continuous.comp L.continuous).comp ((S₀ j).continuousE q))) ((Aq).continuous.comp (((Θ₀ (ℜ k0)).continuous.comp L.continuous).comp ((S₀ j).continuousE q)))) (fun t' ht=> t k0 t' bk ht) σ
 exact radiatory Tx (W:= {i:ℝ≥0| A0 ((Θ₀ i) (L ((Θ₀ σ) q)))= Aq ((Θ₀ i) (L ((Θ₀ σ) q)))}) (isClosed_eq (A0.continuous.comp ((S₀ j).continuousE _)) ((Aq).continuous.comp ((S₀ j).continuousE _))) h t₀ -- h let expects yes
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
