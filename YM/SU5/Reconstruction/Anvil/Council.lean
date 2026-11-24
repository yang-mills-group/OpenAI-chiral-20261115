import YM.SU5.Reconstruction.Anvil.Receipt
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
namespace LightBudget
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
variable {J : Calibration}
local notation "D" => Domain Y H G false
local notation "Gt" => marks (timeMesh Λ)
local notation "K₀"=> tent Y H
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "J₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "C₀"=> saunters Y H V G.history G.clipped j false C χ
local notation "G₀"=> fort Y H V G.history G.clipped j false C χ
local notation "Ω₀"=> mainsea Y H V G.history G.clipped j false C χ
local notation "L"=> ride Y H V G.history G.clipped j false C χ
local notation "S"=> peninsula Y H V G.history G.clipped j false C χ
local notation "Π" x:max=> physicalKet Y H V G j C χ x
local notation "F"=> osValue Y H V G j C χ
local notation "A₀"=> flank j 0
set_option quotPrecheck false
local notation "P"=> (C₀).orthogonalProjectionOnto
local notation "θ"=> flipMark j K
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "κ" p:max=> move K p
local notation "Jj"=> Domain Y H G false (flank j 0)open YM.Anvil
local notation "Θ" p:max=> eject j p
variable (tC : saunters Y H V G.history G.clipped j false C χ=⊤)
  (wC : ConePrice.Forward (peninsula Y H V G.history G.clipped j false C χ))
variable {x y: Sky (tent Y H)}
-- same exterior tests on this crossing. no monitor magnitudes involved yet.
variable (j' : Axis) (C' : Arena Y H G.history.circuit j' 0 false)
  (χ' : displayAlgebra Y H V G.history G.clipped j' false C' →⋆ₐ[ℂ] ℂ)
  (tC' : saunters Y H V G.history G.clipped j' false C' χ'=⊤)
  (wC' : ConePrice.Forward (peninsula Y H V G.history G.clipped j' false C' χ'))
  (eT : osValue Y H V G j C χ=osValue Y H V G j' C' χ')
  (a b : Domain Y H G false (flank j 0))(u v : Domain Y H G false (flank j' 0)) (T:marks (timeMesh Λ))
local notation "S'" => peninsula Y H V G.history G.clipped j' false C' χ'
local notation "Ft"=> Follows Y H V G
open YM.Anvil
include tC wC tC' wC' eT
lemma council (m : move (tent Y H) (Θ (-T)) (θ a.val)= move (tent Y H) (eject j' (-T)) (flipMark j' (tent Y H) u.val))
  (n: move (tent Y H) (Θ T) b.val=move (tent Y H) (eject j' T) v.val) (E F' H' U D0 X Y' Z: marks (timeMesh Λ)) (A B: (indoor Y H V G.history G.clipped j false C χ).Op)
  (A' B': (indoor Y H V G.history G.clipped j' false C' χ').Op)
  (p : Follows Y H V G j C χ (move (tent Y H) (Θ (-E)) x) F' A)(q : Follows Y H V G j C χ (move (tent Y H) (Θ (-H')) y) U B)
  (r : Follows Y H V G j' C' χ' (move (tent Y H) (eject j' (-D0)) x) X A')(s : Follows Y H V G j' C' χ' (move (tent Y H) (eject j' (-Y')) y) Z B')
  (k k':Bool)(z:Wage)(z₀:(horizonPrice T E F' H' U).permeates j k z)(z₁:(horizonPrice T D0 X Y' Z).permeates j' k' z):
    (horizonPrice T E F' H' U).sale k (S) (opCarries Y H V G j C χ A) (opCarries Y H V G j C χ B) (coreOs Y H V G j C χ a) (coreOs Y H V G j C χ b) z=
      (horizonPrice T D0 X Y' Z).sale k' (S') (opCarries Y H V G j' C' χ' A') (opCarries Y H V G j' C' χ' B') (coreOs Y H V G j' C' χ' u) (coreOs Y H V G j' C' χ' v) z := by
  let f:=coordinates Λ
  have e: DenseRange (coordinates Λ):= by exact DenseRange.piMap (X:=fun _:Axis=>Gt) (fun i=> (daylight (timeMesh Λ)).denseRange_val) -- pi.map eq
  refine Price.plank _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Set.range (coordinates Λ)) e ?_ _ z₀ z₁
  rintro w ⟨d,rfl⟩ l l'
  obtain ⟨w,W⟩:= embossed Y H V G j C χ tC wC _ _ _ _ p q a b T d _ l
  obtain ⟨ζ,Kx⟩:= embossed Y H V G j' C' χ' tC' wC' _ _ _ _ r s u v T d _ l'
  rw [← W, ← Kx,eT]
  apply congrArg (osValue ..); apply Subtype.ext; change Quartet _ _ _ _ _=Quartet _ _ _ _ _; rw [m,n]
end LightBudget
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
