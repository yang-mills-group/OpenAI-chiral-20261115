import YM.SU5.Reconstruction.Quartz.HearthRise
import YM.SU5.Reconstruction.Quartz.Assembly
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option linter.unusedSectionVars false
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
open YM.Quartz YM.Quartz.Waltz YM.Quartz.Ship
local notation "Qv"=> Picket.quarter j z
local notation "Lvl" i:max=>floor Y H V G C a χ i
local notation "Uj" i:max=>Picket.trans (S₀ i)
local notation "Oh" i:max=>parcelUp (S₀ i)
local notation "Wj"=> Wedge j z
local notation "Wz"=> Counter z j
local notation "M₁"=> (Lvl j) Wj
local notation "M₂"=> (Lvl z) Wz
local notation "ι"=> Z.look.conjStarAlgEquiv
local notation "Cj" i:max k:max bj:max=> Creased Y H V G C a χ F i k bj
/-! # single net actually seen by both Wick frames, all wedge locations paired.

We've attempted the analytic justification first. See PrismPlan for arguments; this is at physical price, no claiming all those budgets are discharged!
-/
variable (s:Creased Y H V G C a χ F j z b) (r:Creased Y H V G C a χ F z j b.symm)
include p F s r
lemma filial (h:CrewCost Y H V G C a χ j z) : ∀ η:Bool, Pull Z.look (floor Y H V G C a χ z (curtains z j (!η)))= floor Y H V G C a χ j (curtains j z η):= by
 let u:= back_quarter Y H V G C a χ F j z b Z p
 have hp : Pull Z.look M₂=M₁:= congruent Y H V G C a χ F j z b Z p r s (crewing Y H V G C a χ F j z b Z p r h) -- tune
 intro η; cases η
 · change Pull Z.look ((Lvl z) (Wedge z j))=(Lvl j) (Counter j z)
   rw [← equalsShade Y H V G C a χ F j z b Z p s]; rw [← (show (M₂).commutant=(Lvl z) (Wedge z j) from (by rw [← equalsShade Y H V G C a χ F z j b.symm Z.Back u r, VonNeumannAlgebra.commutant_commutant]))]; exact Ship.reverseRel Z.look _ hp
 exact hp
lemma horizonMatch (h:CrewCost Y H V G C a χ j z) (t:E4) (η:Bool): Pull Z.look ((Lvl z) (hikeWorld (curtains z j (!η)) (Qv t)))=(Lvl j) (hikeWorld (curtains j z η) t):=by
 let T:= curtains j z η; let W:=curtains z j (!η); let ϕ:= Z.look.conjStarAlgEquiv
 apply VonNeumannAlgebra.ext; intro x; let A:=(Oh j) (-t) x; unfold hikeWorld; rw [show x=(Oh j) t A from (parcel_inv ..).symm,← translation_cov _ _ _ _ _ _ _ F, pulling,← carries_shift _ _ _ _ _ _ _ j z b Z p, ← translation_cov _ _ _ _ _ _ _ F, ←pulling Z.look, filial Y H V G C a χ F j z b Z p s r h η] -- binder implicit params; `translation_cov not sees` unfold hikeWorld
-- opp fomular
omit p s r F
structure BilateralPort : Prop where
    accepts (F:BoostBacking Y H V G C a χ)(j z:Axis)(b:j≠z)(D₀:Hilbert)(Z:Clasp D₀ (G₀ j) (G₀ z))(p:Quarter Y H V G C a χ j z b.symm Z): Quarter Y H V G C a χ z j b Z.Back
    -- ALL at that pair for any paid by criterion. At Observer legando all.
    crowns : ∀ (F:BoostBacking Y H V G C a χ) (j z:Axis) (b:j≠z) (D₀:Hilbert) (Z:Clasp D₀ (G₀ j) (G₀ z)), Quarter Y H V G C a χ j z b.symm Z →Creased Y H V G C a χ F j z b→ Creased Y H V G C a χ F z j b.symm→ CrewCost Y H V G C a χ j z→∀ (η:Bool) (t:E4) (A:(G₀ j).Op), A∈ (Lvl j) (hikeWorld (curtains j z η) t) ↔ (Z.look.conjStarAlgEquiv A) ∈ (Lvl z) (hikeWorld (curtains z j (!η)) (Picket.quarter j z t)) -- Lvl macro may capture? `Lvl` uses free j? define uses i passed.St.
    -- these credits require no Rank nor cross attachments, only the BoostBacking
    honours (F:BoostBacking Y H V G C a χ)(j z:Axis)(b:j≠z)(D₀:Hilbert)(Z:Clasp D₀ (G₀ j) (G₀ z))(p:Quarter Y H V G C a χ j z b.symm Z)(x:Sky K)(t u:Gt)(h:0<(t:ℝ))(k:0≤(u:ℝ))(v: x∈ Ds (Chambers.strip j 0 (t:ℝ)∩Chambers.strip z 0 (u:ℝ)))(A:(J₀ j).Op)(A':(J₀ z).Op): (Q j) x t A → (Q z) x u A' → let Uₘ:= (Π j) A*(Uj j) ((u:ℝ) • basis z); let W:=(Π z) A'*(Uj z) ((t:ℝ) • basis j); Z.Pass Uₘ W ∧ ∃ V, Quartz.Reflected Z Uₘ W V -- no confusion payments
    estimates (F:BoostBacking Y H V G C a χ)(j z:Axis)(b:j≠z)(D₀:Hilbert)(Z:Clasp D₀ (G₀ j) (G₀ z))(p:Quarter Y H V G C a χ j z b.symm Z)(u v:Axis→Gt)(A:(G₀ j).Op)(e:0<(u z:ℝ))(x:Sight Y H V G C a χ j u v A) : ∃! B:(G₀ z).Op, Duet Y H V G C a χ j z u v A B
    landscapes (F:BoostBacking Y H V G C a χ)(j z:Axis)(b:j≠z)(D₀:Hilbert)(Z:Clasp D₀ (G₀ j) (G₀ z))(p:Quarter Y H V G C a χ j z b.symm Z)(u v:Axis→Gt)(A:(G₀ j).Op)(B:(G₀ z).Op)(d: Duet Y H V G C a χ j z u v A B): ∃ V, Quartz.Reflected Z (A*((Uj j) ( (((u z:ℝ)+(v z:ℝ))) • basis z))) B V
    -- EACH actual program has that exact further-clock weak-limit budget (spinEcho statement). Can call with gauge apertures centres positive.

lemma heirs : BilateralPort Y H V G C a χ:=by
 refine ⟨fun F j z b _ Z p=> back_quarter Y H V G C a χ F j z b Z p, ?_,?_,?_,?_⟩
 · intro F j z b _ Z p hj hz h η t x; rw [← horizonMatch Y H V G C a χ F j z b Z p hj hz h t η, pulling]
 · intro F j z b _ Z p x t u h k' v A B q wA; let y:=herePass Y H V G C a χ F j z b Z p x t u A B q wA h k' v; exact ⟨y, Quartz.reflected Z _ _ y⟩
 · intro F j z b K0 Z p u v A e x; obtain ⟨Y',g⟩:=awardEcho Y H V G C a χ F j z b Z p u v A e x; exact ⟨Y',g, fun B h=> Quartz.eitherUnique Z (bookedEcho Y H V G C a χ F j z b Z p u v A B h) (bookedEcho Y H V G C a χ F j z b Z p u v A Y' g)⟩
 intro F j z b _ Z p u v A B d; exact Quartz.reflected Z _ _ (bookedEcho Y H V G C a χ F j z b Z p u v A B d)
end Crease
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
