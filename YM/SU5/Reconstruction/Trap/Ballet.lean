import YM.SU5.Reconstruction.Trap.Vista
import YM.SU5.Reconstruction.Trap.LP
/-!
# Picket in the Reconstruction setup. same character.
-/
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
open CrossedFrame
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
local notation "θ" i:max=> flipMark i (tent Y H)
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "Globe" => (N j ∩ N j')
local notation "L" i:max=> lowland i 0
local notation "Tea" => (L j ∩ L j')
local notation "Wl" i:max=> onceLens Y H V G C a χ i Globe
-- selected LAW
variable {S:Hilbert} (Z:Clasp S (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped j' false (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j'))))
variable (p:saunters Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))=⊤) (q:saunters Y H V G.history G.clipped j' false (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j'))=⊤) (h:Brigade Y H V G C a χ j j' hv S Z)
local notation "U"=> S₀ j
local notation "B"=> S₀ j'
include p in
lemma turnsLens (z: placement Λ)(x y: Ds Globe)(u:0≤ coordinates Λ z j)(t:y.val=move K z x.val) : (Pr j) z ((Wl j) inter_subset_left x)=(Wl j) inter_subset_left y:= by
 let x':D (N j):= Submodule.inclusion (le_trans (domain_loose Y H G Globe) (domain_mono Y H G inter_subset_left)) x; -- shape annotation required
 let x'': D (N j):=x'
 let y':D (N j):= Submodule.inclusion (le_trans (domain_loose Y H G Globe) (domain_mono Y H G inter_subset_left)) y
 change (Pr j) z ((Vo j) x'')=(Vo j) y'; let e: y'.val=move K z x''.val:=t
 have hp:move K z x''.val∈ D (N j):= e ▸ y'.property
 rw [← voice_move Y H V G j (C j) (w j) p z _ u hp, show (⟨_,hp⟩: D (N j))=y' from Subtype.ext e.symm]
-- helper any U, better
include h p q
lemma stepB (z:placement Λ)(b:0≤coordinates Λ z j)(c:0≤coordinates Λ z j'): Z.Pass ((Pr j) z) ((Pr j') z):= by
 apply h.pass
 intro f; let g:= move K z f.val
 have hx : slides (coordinates Λ z) Globe ⊆ Globe:= subset_inter ((Set.image_mono inter_subset_left).trans (even_flank j z (by simpa only [zero_add] using! b))) ((Set.image_mono inter_subset_right).trans (even_flank j' z (by simpa only [zero_add] using! c))) -- tune even_flank requires LE α+; compare
 let hp: g∈ Ds Globe:= domain_mono Y H G hx (moving Y H V G z _ f.property)
 let g':= (⟨g,hp⟩: Ds Globe)
 change Z.Latch ((Pr j) z ((Wl j) inter_subset_left f)) ((Pr j') z ((Wl j') inter_subset_right f))
 rw [turnsLens Y H V G C a χ j j' p z f g' b rfl] -- hv arguments tune
 rw [show (Pr j') z ((Wl j') inter_subset_right f)= (Wl j') inter_subset_right g' from ?_]
 exact h.sees g'
 -- across flip of roles by direct use voice_move
 exact (voice_move Y H V G j' (C j') (w j') q z (Submodule.inclusion (domain_loose Y H G _) (Submodule.inclusion (domain_mono Y H G inter_subset_right) f)) c (domain_loose Y H G _ (domain_mono Y H G inter_subset_right hp))).symm
local notation "xU" => Picket.cross j j' hv
local notation "xB"=> Picket.cross j' j hv.symm
omit h p q in
lemma castSpace {z : Axis} (d:z≠ j) (x:Gt): (Pr j) (eject z x)= Picket.trans (S₀ j) ((x:ℝ) • basis z):= by
 have hp:= across_time Y H V G j (C j) (w j) z 0 x d
 rw [eject_zero, zero_add, AddSubgroup.coe_zero,Real.toNNReal_zero, OS.Semigroup.eZero] at hp; rw [hp,ContinuousLinearMap.comp_id]; exact (Picket.trans_space z (x:ℝ) (S₀ j) (h:=d)).symm
lemma onBeam : Picket.Beam hv U B Z:= by
 apply Picket.timeBeam hv U B Z (timeMesh Λ)
 intro x y u v; let i:= eject j x+eject j' y
 have hj:coordinates Λ i j=(x:ℝ):=by simp [i,hv.symm]
 have hy:coordinates Λ i j'=(y:ℝ):=by simp [i,hv]
 have hs:= stepB Y H V G C a χ j j' hv Z p q h i (hj.symm ▸ u) (hy.symm ▸ v)
 unfold i at hs; rw [across_time Y H V G j (C j) (w j) j' x y hv,add_comm (eject j x),across_time Y H V G j' (C j') (w j') j y x hv.symm] at hs -- ensure add_comm applies only remaining arg
 unfold Picket.argSpace; rw [Real.coe_toNNReal _ v,Real.coe_toNNReal _ u]; exact hs
lemma onStreet: Picket.Behind U B Z:= by
 apply Picket.priceL (S₀ j) (S₀ j') Z (timeMesh Λ)
 intro i z v t; rw [← castSpace Y H V G C a χ j z t, ←castSpace Y H V G C a χ j' v t]
 apply stepB Y H V G C a χ j j' hv Z p q h <;> simp [Ne.symm v,Ne.symm z]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
