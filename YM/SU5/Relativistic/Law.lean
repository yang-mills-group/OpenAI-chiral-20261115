import VerifiedSatinSelectedSectors

/-!
# Freeze the election (all witnesses from glass_with_appointment).

For ergonomics in developments referring to very many pieces of the law. Not a new
selection/strengthening. `sample` not classically chosen in a second worker.
-/
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 26000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Papal

open Function Set Filter MeasureTheory
open Lattice SU Buffered Afterglow Journey Preparation CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet
open Satin Tapestry Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice
open scoped Topology BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

structure Election (ε η : ℝ) (U : Supplier)
    (P : Preparation)
    (l : ℕ)
    (Z : ℝ)
    (H : Real.exp 1 ≤ P.x)
    (Y : Course P (VolumeCape.Dream.Nimbus l))
    (q : ℕ)
    (d : ℕ)
    (w : ℕ)
    (C : ℝ)
    (a : ℕ → ℕ)
    (b : ℕ → ℕ)
    (I : ℕ → Buffered.Family (tent Y H) → ℕ → ℂ)
    (E : ℕ → Buffered.Family (tent Y H) → ℂ)
    (L : Rack P l)
    (B : Tapestry.Clay P l)
    (T : ℕ → ℕ → Tapestry.Tariff)
    (t : ℕ → Tapestry.Tariff)
    (D : Tapestry.Fashion Y H a b I E L B T t)
    (G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H)
    (room : ∀ j, Tower.Arena Y H G.history.circuit j 0 false)
    (pan : Panel Y H D.univ_ G.history G.clipped 0 false (room 0))
    (s : ℕ)
    (ζ : ℝ)
    (f : SU.Slot → observable (tent Y H) true)
    (f' : SU.Slot → observable (tent Y H) true)
    (sample : pan.X) : Prop where
  lt_pivot : ε < P.x
  d_le : P.d ≤ η
  decorate_le : decorate U P l Z ≤ P.h
  nominated : P.nominated (VolumeCape.Dream.Nimbus l)
  usable : ∃ z, Usable (D:=P.δ) P.V P.W P.J P.N0 z P.delay Y.meter
  prepared : ∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay
  loomLaw : ∀ i j:ℕ, Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)
  korn : Korn Y H q d w C Z
  seasonCert : SeasonCert Y H D
  mixed : ∀ j:Axis, ∃ a' : Tower.Arena Y H G.history.circuit j 0 true, Papal.mixed_in_ground Y H D.univ_ G j a' q d w
  issued : Issued Y H D.univ_ G.history G.clipped 0 false (room 0) pan
  mean : ∀ j F, ∫ x, response Y H D.univ_ j G.history G.clipped 0 false (room 0) (pan.character x) F ∂pan.μ = E j F.val
  ζ_pos : 0 < ζ
  paint : paints_for Y H D.univ_ s G.history G.clipped (room 0) pan room q d w ζ sample f f'
  pins : Appointment Y H D.univ_ G D.toExhibition 0 room
    (SameCharacter.resident Y H D.univ_ G 0 false (room 0) (pan.character sample))
  survives (z : SU.Slot) (j:Axis) (δ:ℝ) : 0 < δ →
    let r:=displacement Y H D.univ_ G.history G.clipped 0 false (room 0) (pan.character sample) j (room j)
    let o:= CF.Pannier.Chancel.grain (payout d q w)
    let S:= Sen o (payout d q w)
    (∃ p q':Cover, Exceeds Y H D.univ_ s G.history G.clipped j (room j) r δ (f z) z S o q d p q') ∧
    ∃ p q':Cover, Exceeds Y H D.univ_ s G.history G.clipped j (room j) r δ (f' z) z (grindscape (booty o d q) S) o q d p q'

theorem electGlass (ε η : ℝ) (p : 0 < η) (U : Supplier) :
    ∃ P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample, Election ε η U P l Z H Y q d w C a b I E L B T t D G room pan s ζ f f' sample := by
  obtain ⟨P,l,Z,h₁,h₂,h₃,h₄,H,Y,y₁,y₂,y₃,q,d,w,C,k,a,b,I,E,L,B,T,t,D,
    season,G,c,pan,mixed,issued,mean,s,ζ,f,f',x,hζ,paint,pins,survive⟩ :=
    glass_with_appointment ε η p U
  exact ⟨P,l,Z,H,Y,q,d,w,C,a,b,I,E,L,B,T,t,D,G,c,pan,s,ζ,f,f',x,
    ⟨h₁,h₂,h₃,h₄,y₁,y₂,y₃,k,season,mixed,issued,mean,hζ,paint,pins,survive⟩⟩

end YM.CF.Py.Rate.LocalLimit.Papal
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.electGlass
