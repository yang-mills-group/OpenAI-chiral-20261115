import YM.SU5.Reconstruction.GiftWrap.Gentry
/-! # Wall right edges : extending two-operand cross through actual Schwinger sector -/
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
include b p F
lemma validGate (R:Ds U) (x t:Gt) : ∃ (Rj:D' j) (Rz:D' z), m₁ (eject j t) Rj.val=m₁ (eject z x) Rz.val ∧ (Tm j) ((x:ℝ) • basis z) ((Λ₁ j) U inter_subset_left R)=(Vo j) Rj ∧ (lz t) ((Λ₁ z) U inter_subset_right R)=(Vo z) Rz:=by
 let a₁ : (D' j):=Submodule.inclusion (le_trans (domain_mono Y H G inter_subset_left) (domain_loose Y H G _)) R; let b₁ : (D' z):=Submodule.inclusion (le_trans (domain_mono Y H G inter_subset_right) (domain_loose Y H G _)) R
 let u:=eject z x; let v:=eject j t
 have hy : m₁ u a₁.val∈ D (flank j 0):= domain_mono Y H G (by rintro _ ⟨y,h,rfl⟩; change 0 ≤ y j+ _; simpa [u,b] using (show 0 ≤ y j from h)) (moving Y H V G _ _ a₁.property)
 have hz : m₁ v b₁.val∈ D (flank z 0):= domain_mono Y H G (by rintro _ ⟨y,h,rfl⟩; change 0 ≤ y z+ _; simpa [v,b.symm] using (show 0 ≤ y z from h)) (moving Y H V G _ _ b₁.property)
 refine ⟨⟨_,hy⟩,⟨_,hz⟩,?_,?_,?_⟩
 · change m₁ v (m₁ u R.val)=m₁ u (m₁ v R.val); rw [move_sum,move_sum,add_comm]
 · rw [← castSpace Y H V G C a χ j b.symm]
   exact (voice_move Y H V G j _ _ (F.present j) u a₁ (by simp [u,b]) hy).symm
 rw [← castSpace Y H V G C a χ z b]
 exact (voice_move Y H V G z _ _ (F.present z) v b₁ (by simp [v,b.symm]) hz).symm

variable {x y: Sky (tent Y H)} (d v0 s t: marks (timeMesh Λ))
variable (A:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (A':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (f0: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) x s A)
  (f1: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-d)) x) v0 A')
variable (u v h : marks (timeMesh Λ))(B:(indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op)
  (B':(indoor Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))).Op)
variable (F₀: Follows Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) y h B)
  (F₁: Follows Y H V G z (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z)) (FirstWindows.move (tent Y H) (eject z (-u)) y) v B')
local notation "Γ" => u-(d+v0)
local notation "Qn" => (u+v+Γ)
local notation "Uj" => (lu (Qn:Gt))
local notation "ρ" => ℜ (Γ:Gt)
local notation "ψ" => transversal z j b
local notation "E₀" => F.forward z
local notation "Ed"=> osValue Y H V G
include f0 f1 F₀ F₁
-- just the precise version for full wall.Rig.
lemma wallChart (q:d+v0 <u) (x':D₀)(L:D' j)(L₁:D' z)
    (q':m₁ (eject j (-t)) ((θ j) L.val)=m₁ (eject z d) ((θ z) L₁.val)) (i:Gt)(vT:0≤(t:ℝ)) : let hr:0< (Real.toNNReal ((u-(d+v0):Gt):ℝ)):= Real.toNNReal_pos.mpr (show 0 < ((u-(d+v0):Gt):ℝ) from sub_pos.mpr q)
    let P:=screen (S₀ z) (F.forward z) (transversal z j b) (le_of_eq (transversal_norm z b)) _ hr ((Π z) A') ((Π z) B') ((Vo z) L₁) (Picket.trans (S₀ z) ((t:ℝ) • basis j) (Z.r x')) (↑(i:ℝ):ℂ)
    (s ≤ i → i+h≤t → P= before (S₀ j) (ℜ t) ((Π j) A) ((Π j) B) ((Vo j) L) (Uj (Z.l x')) s h (↑(i:ℝ):ℂ)) ∧ (i+h≤0 → -t≤ i → s≤ t → P= after (S₀ j) (ℜ t) ((Π j) A) ((Π j) B) ((Vo j) L) (Uj (Z.l x')) s h (↑(i:ℝ):ℂ)):= by
 intro hr
 intro pc; let V'(X0:D₀):= screen (S₀ z) (F.forward z) ψ (le_of_eq (transversal_norm z b)) _ hr ((Π z) A') ((Π z) B') ((Vo z) L₁) ((lz t) (Z.r X0)) (↑(i:ℝ):ℂ)
 let c(X0:D₀):= before Sq (ℜ t) ((Π j) A) ((Π j) B) ((Vo j) L) (Uj (Z.l X0)) s h (↑(i:ℝ):ℂ); let c'(X0:D₀):=after Sq (ℜ t) ((Π j) A) ((Π j) B) ((Vo j) L) (Uj (Z.l X0)) s h (↑(i:ℝ):ℂ)
 have he(X0)(R:Ds U)(g: Z.l X0=(Λ₁ j) U inter_subset_left R)(t': Z.r X0=(Λ₁ z) U inter_subset_right R) : (s≤ i→ i+h≤t→ V' X0=c X0) ∧ (i+h≤0 → -t≤ i → s≤ t → V' X0=c' X0):=by
    obtain ⟨Y',V1,bv,τ,σ⟩:= validGate Y H V G C a χ F j z b Z p R Qn t
    let Ft:=cross_chart Y H V G j (C j) (w j) z (C z) (w z) b v0 v L Y' d u t (F.present z) (show Ed z _ _=Ed j _ _ from (by rw [os_across Y H V G ..,os_across Y H V G ..])) (F.forward z) q f1 F₁ L₁ V1 q' bv i
    constructor
    · intro d₀ h₁; unfold c V'; rw[g,t',τ,σ]; exact Ft.choose_spec.symm.trans (opens_right Y H V G j (C j) (w j) L Y' (F.present j) f0 F₀ t i vT d₀ h₁).choose_spec
    intro d₀ h₁ h₂; unfold c' V'; rw[g,t',τ,σ]; exact Ft.choose_spec.symm.trans (opens_left Y H V G j (C j) (w j) L Y' (F.present j) f0 F₀ t i vT d₀ h₁ h₂).choose_spec
 have hV: Continuous V':= by unfold V' screen; fun_prop
 constructor
 · intro vZ vb; refine closure_minimal ?_ (isClosed_eq hV (show Continuous c from ?_)) (p.port.full x')
   · rintro i ⟨f,p,h⟩; exact (he i f p h).1 vZ vb
   unfold c Sail.before; fun_prop
 intro q0 q1 q2; refine closure_minimal ?_ (isClosed_eq hV (show Continuous c' from (by unfold c' Sail.after; fun_prop))) (p.port.full x'); rintro i ⟨f,p,h⟩; exact (he i f p h).2 q0 q1 q2
end Boots
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
