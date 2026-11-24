import YM.SU5.Reconstruction.Crease.Cistern
import YM.SU5.Reconstruction.Crease.Blade
import YM.SU5.Reconstruction.UVPrice.Void
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
open CrossedFrame Clasp BridgeClub.Club
local notation "Φ"=> Flare Y H V G C a χ F j z b
local notation "ℶ"=> Flare Y H V G C a χ F z j b.symm
variable {D₀:Hilbert} (Z : Clasp D₀ (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped z false (C z) (displacement Y H V G.history G.clipped a false (C a) χ z (C z))))
variable (p:Quarter Y H V G C a χ j z b.symm Z)
local notation "Ξ"=>parcelUp (S₀ j)
local notation "Λ₁"=>Sight Y H V G C a χ j
local notation "ℓ"=>Wing Y H V G C a χ j
local notation "ζ"=>floor Y H V G C a χ j
local notation "Ω" => Ω₀ j
local notation "P" => Z.plume
local notation "R" => Z.shadow
local notation "J" => (Φ).f
local notation "Π" i:max=> opCarries Y H V G i (C i) (w i)
local notation "M"=> ζ (Wedge j z)
local notation "Mm"=> ζ (Counter j z)
local notation "Mw"=> ζ univ
local notation "Γ"=> pinpoints Y H V G C a χ j z
variable (h:Rank (Flare Y H V G C a χ F j z b) (vocation Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (pinpoints Y H V G C a χ j z))
variable (g:FullWins Y H V G C a χ)
include b F
private lemma entitled {A:(G₀ j).Op} (q:A∈ M): (Φ).shade A∈ Mm:= reflection_bound Y H V G C a χ F j z b _ _ (by rintro _ ⟨x,e,rfl⟩; exact (BridgeClub.turning j z x).mpr e) A q
lemma foes : Mm≤ (M).commutant:= fun i q=> VonNeumannAlgebra.mem_commutant_iff.mpr fun A h=> Eq.symm (VonNeumannAlgebra.mem_commutant_iff.mp (spacelike Y H V G C a χ F j _ _ (room_separated j z b) h) _ q)
include p h
local notation "Pp"=> foes Y H V G C a χ F j z b
local notation "Hi"=>engaged Y H V G C a χ F j z b Z p h
lemma equalsShade : (M).commutant = Mm := (Hi).equality (fun _ t=> entitled Y H V G C a χ F j z b t) Pp
lemma transported_room (u:ℝ)(v:E4)(ω:Bool)(A:(G₀ j).Op): A ∈ ζ ((fun x=>x+v) '' curtains j z ω) ↔ ascend u Z A∈ ζ (Picket.move j z u '' ((fun x=> x+v) '' curtains j z ω)) := by
    let T:= curtains j z ω; let Cq:=ascend u Z; have hu(A:(G₀ j).Op): Cq A∈ ζ T ↔ A∈ ζ T:= by
       unfold Cq; rw [pondLevel]; cases ω -- beware T dependent
       case true=> exact (Hi).answers (fun _ t=>entitled Y H V G C a χ F j z b t) Pp _ A
       case false=> exact (Hi).proceeds (fun _ t=>entitled Y H V G C a χ F j z b t) Pp _ A
    let A':= Ξ (-v) A; have hT:Ξ v A'=A:= parcel_inv ..; rw [← hT,← translation_cov _ _ _ _ _ _ _ F,eitherShift b.symm, motionFrame b.symm u Z (S₀ j) (p.spins u).2,← translation_cov _ _ _ _ _ _ _ F]
    exact (hu A').symm
include g
lemma wedgeCenter (A:(G₀ j).Op)(t:A∈ M)(u:A∈ Mm): ∃ z:ℂ,A=z • (1:(G₀ j).Op):= by
 have pV:= (little_due Y H V G C a χ g (r:=0) le_rfl (fewer Y H V G C a χ le_rfl F)).2.unique_normal j
 exact clearCenter Hi b.symm (S₀ j) (fun u=> (p.spins u).2) pV t (Pp u)
lemma irreducible (A:(G₀ j).Op) (q:A∈ (ζ univ).commutant):∃ z:ℂ,A=z • (1:(G₀ j).Op):= by
 have h₁(U:Set E4): A∈ (ζ U).commutant:= VonNeumannAlgebra.mem_commutant_iff.mpr fun x e=> VonNeumannAlgebra.mem_commutant_iff.mp q x (sober _ _ _ _ _ _ _ _ U _ (subset_univ _) e)
 have he: Mm=(M).commutant:= (equalsShade Y H V G C a χ F j z b Z p h).symm
 have ht:=h₁ (Counter j z); rw [he, VonNeumannAlgebra.commutant_commutant] at ht; exact wedgeCenter Y H V G C a χ F j z b Z p h g A ht (he.symm ▸ h₁ _)
lemma allIn (A:(G₀ j).Op): A∈ ζ univ:=by
 rw [← VonNeumannAlgebra.commutant_commutant (ζ univ)]; refine VonNeumannAlgebra.mem_commutant_iff.mpr (fun x ht=>?_); obtain ⟨β,rfl⟩:=irreducible Y H V G C a χ F j z b Z p h g x ht; exact Commute.smul_left (Commute.one_left A) β
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
