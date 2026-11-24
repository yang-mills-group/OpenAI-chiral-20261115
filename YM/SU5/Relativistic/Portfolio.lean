import VerifiedSatinSelectedSectors
import YM.SU5.Relativistic.ProbeDelivered

/-!
# CP1: Joint prescription and testing one physical FiniteGaugeData observable per
slot and axis, all in one already elected Glass phase.
-/
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 27000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Reliance ShortWave
open Tower.Selected Vacancy
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra
section registrar
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
local notation "K"=>tent Y H
variable {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{L:Rack Λ l}{B:Clay Λ l}
    (Q: Exhibition Y H a b I E L B)
local notation "V"=>Q.univ_
variable (G:SatinVerification.GroundExtension (i:=a) (k:=b) (E:=E) Y H)
variable (c:∀ j,Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H Q.univ_ G.history G.clipped 0 false (c 0) →⋆ₐ[ℂ] ℂ)
local notation "χ̂" j:max=> displacement Y H V G.history G.clipped 0 false (c 0) χ j (c j)
local notation "χ₁"=> SameCharacter.resident Y H V G 0 false (c 0) χ
local notation "Φ" => onDrawing Y H V G Q 0 c χ₁
local notation "MX"=> evaluate Y H V G 0 c χ₁
local notation "Ω" => Dome (tent Y H)
-- noninstance P quantifiers
variable (q d w:ℕ) (s:ℕ) (ζ:ℝ) (f':SU.Slot → observable (tent Y H) true)
local notation "origin"=> CF.Pannier.Chancel.grain (payout d q w)
local notation "places"=> grindscape (booty origin d q) (Sen origin (payout d q w))
structure Installation : Prop where
  engine : ∀ (n : ℕ) (F : Family K) (h:TestFamily K true F), Φ (Altitude.pinhole Ω n (⟨F,h⟩ : Ω))= MX n F
  readings {U:Set RSpace} {x:Altitude.Cloud (Dome (tent Y H))} {wide:Bool}{a:Set ℕ}{s:ℕ}
    (p:x∈ circum Λ l (tent Y H) wide U (a∩ Set.Iic s)) :
    ∃ S:Finset Cover, (∀ n:ℕ, SupportedPhysically Λ l (s+n) (volumeAround Λ l n S) U) ∧
      (∀ᶠ i : ℕ in atTop,Host Y H i s S) ∧
      ∀ (i k n : ℕ), Tapestry.Pay Y (s+n) i k → AtSupport false (Satin.region (volumeAround Λ l n S) (side Y i (s+n))) (attire (breathing Y H (s+n) i k x)) ∧
        covariant (attire (breathing Y H (s+n) i k x)) ∧
        taking Y H i k x= Journey.compass Y i k (s+n) (attire (breathing Y H (s+n) i k x)) ∧
        microscope Y i k 1 ≠ 0 ∧ taking Y H i k x=microscope Y i k (attire (breathing Y H (Y.uv k) i k x))/microscope Y i k 1
  joint : ∀ (j:Axis) (z:SU.Slot) (δ:ℝ), 0<δ → ∃ p q':Cover,
    Coupled Y H Q G 0 j c χ s (z:=z) (u:=d) (v:=q) (S:=places) (o:=CF.Pannier.Chancel.grain (payout d q w)) (δ:=δ) (w:=ζ) p q' (f' z)
end registrar
end YM.CF.Buffered.Afterglow.Tower.Reconstruction

namespace YM.CF.Py.Rate.LocalLimit.Papal
open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open Tower.Reconstruction
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

-- Kept indexed so that new Ports can compose with exactly these data.
variable {ε η : ℝ} {U:Supplier} {P : Preparation} {l : ℕ} {Z ζ:ℝ} {H : Real.exp 1 ≤ P.x}
    {Y : Course P (VolumeCape.Dream.Nimbus l)} {q d w:ℕ} {C:ℝ}
    {a b : ℕ → ℕ} {I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ} {E : ℕ → Buffered.Family (tent Y H) → ℂ}
    {L : Rack P l} {B : Tapestry.Clay P l} {T : ℕ → ℕ → Tapestry.Tariff} {t : ℕ → Tapestry.Tariff}
    {D : Tapestry.Fashion Y H a b I E L B T t}
    {G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H}
    {room : ∀ j, Tower.Arena Y H G.history.circuit j 0 false}
    {pan : Panel Y H D.univ_ G.history G.clipped 0 false (room 0)}
    {s : ℕ}
    {f f' : SU.Slot → observable (tent Y H) true}
    {sample : pan.X}
lemma Election.install (h : Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample):
    Installation Y H D.toExhibition G room (pan.character sample) q d w s ζ f' := by
  constructor
  · intro n F t; exact costs_pinhole Y H D.toExhibition G 0 room (pan.character sample) n (⟨F,t⟩:Tapestry.Dome (tent Y H))
  · intro U x w S s p; exact continuum_footprint Y H s p
  intro j z δ hp
  let R:=CF.Pannier.Chancel.grain (payout d q w); let S:= grindscape (booty R d q) (Sen R (payout d q w))
  obtain ⟨p,q',r⟩:=(h.survives z j δ hp).2
  have hv:= (h.paint z).2.2.2.1.2.witness.link
  refine ⟨p,q',Coupled.jointly Y H D.toExhibition G 0 j room (pan.character sample) s _ _ (f' z) hv.mark_mem r h.ζ_pos ?_ hv.anchor_inj⟩
  exact tinted_weight (pow_pos h.korn.range _) (h.paint z).2.2.1

/-- Single object, everything from the election as specified. -/
theorem physical_tests (ε η : ℝ) (p : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample, Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample ∧
      Installation Y H D.toExhibition G room (pan.character sample) q d w s ζ f' := by
  obtain ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,h⟩:=electGlass ε η p U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,room,pan,s,ζ,f,f',sample,h,h.install⟩
end YM.CF.Py.Rate.LocalLimit.Papal
#check @YM.CF.Buffered.Afterglow.Tower.Reconstruction.Installation.joint
#check @YM.CF.Buffered.Afterglow.Tower.Reconstruction.Installation.readings
#check @YM.CF.Py.Rate.LocalLimit.Papal.physical_tests
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.physical_tests
