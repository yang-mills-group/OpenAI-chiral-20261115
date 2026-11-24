import VerifiedSatinWidthAndUVNovember4

/-!
# Towards the matrix zoom: mixed clan price

New files under YM/SU5/Six extend VerifiedSatinWidthAndUVNovember4 to work on
`the construction notes`'s `t:trans6`, following the Lean
handoff there. Here generalize the two-lead purchases of
`YM/SU5/Cordial/{Fountain,LatticeFieldEstimates}.lean` to mixed `Window.Family`, adapting
their code. These are for the one *elected* reading, not uniform across
characters nor adopted prices for the smeared bodies.
-/

set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section

namespace YM.CF.Buffered.Ballad.Cordial

open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods
     Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear
     Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze Twah
open Lead (Clan)
open YM.Stationary (Gaia)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra

-- cf Fountain, Audition
private lemma runes_two_pairs {T : Type*} (d : T → T → ℂ) (p q r s : T) :
    runes d [p, q, r, s] = d p q * d r s - d p r * d q s + d p s * d q r := by
  simp [runes, claps, picks, spinC, offer, besideX, cites, Fock.cval, extendsU, beside]
  ring

/-- The two-family Wick price for different families has no exchange term. -/
lemma chorus4_cross {I : Type*} (P : Cellz I → Gaia) (D : I → DirSpin) (Z : I → Clan)
    (i j : I) (h : Z i ≠ Z j) :
    witness Z [i,j] P D = lyric P D (Z i) i * lyric P D (Z j) j := by
  let f (p q : Slot) := runes (germRho P D) (sayHi (sayHi [] i p) j q)
  let v := billX P D i i * billX P D j j
  have cost (p : Slot) (hp : p ∈ colors (Z i)) (q : Slot) (hq : q ∈ colors (Z j)) :
      f p q = v := by
    have n : p ≠ q := fun e =>
      h (((mem_filter.mp hp).2).symm.trans ((congrArg family e).trans (mem_filter.mp hq).2))
    change runes _ [(i,p,true), (i,p,false), (j,q,true), (j,q,false)] = _
    rw [runes_two_pairs]
    simp only [funds, funds_neg, dcash, ite_true, if_neg n, mul_zero, sub_zero, zero_mul, add_zero, v]
  unfold witness
  change ∑ p ∈ colors (Z i), ∑ q ∈ colors (Z j), f p q = _
  have rhs (p : Slot) (hp : p ∈ colors (Z i)) :
      ∑ q ∈ colors (Z j), f p q = numberX (Z j) * v := by
    rw [sum_congr rfl (cost p hp), sum_const, nsmul_eq_mul, colors_card, numberX]
  rw [sum_congr rfl rhs, sum_const, nsmul_eq_mul, colors_card]
  unfold lyric numberX v
  ring

lemma goes_cross {Z Z' : Clan} (h : Z ≠ Z') (t : ℝ) (x : Bank) :
    (1/5:ℂ) * (1/5) * witness (![Z,Z']) (Twah.letters 2) (duo t x) 0 =
      (purePrice Z : ℂ) * (purePrice Z' : ℂ) := by
  rw [show Twah.letters 2 = [0,1] from rfl, chorus4_cross _ _ _ 0 1 h]
  change _ * (lyric _ _ Z _ * lyric _ _ Z' _) = _
  unfold lyric
  obtain ⟨a,b,-⟩ := reunion t x
  rw [a,b, show (purePrice Z : ℂ) = numberX Z * P20 / 5 from price_as Z,
           show (purePrice Z' : ℂ) = numberX Z' * P20 / 5 from price_as Z']
  ring

end YM.CF.Buffered.Ballad.Cordial
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine

private lemma crossSl_val {q : ℕ} (A B : Lead q) (Z Z' : Lead.Clan) :
    plait ![liftS A,liftS B] ![Z,Z'] (Twah.letters 2) q =
      (liftS A).groundWord q Z * (liftS B).groundWord q Z' :=
  congrArg ((liftS A).groundWord q Z * ·) (mul_one ((liftS B).groundWord q Z'))

variable (Z Z' : Lead.Clan) (a : Axis)
variable {c r : ℕ → ℕ} {P : Spine} {x : P.Spectrum0 3} {d : ℕ → ℝ}
variable (S : Launch P c r) (A B : ∀ i, Lead (r i)) (h : readyUV P c r x d)
         (p : Tendsto d atTop (𝓝 0))
include S h p
local notation "σ" n:max => P.singleState a (c n) (P.otherSpectrum 3 a x)

lemma shineUV_any_clan {w : ℕ} (C : Fin w → Lead.Clan) (D : Cellz (Fin w) → Gaia)
    (r' : Fin w → DirSpin) (F : ℕ → Fin w → Twah) (hu : riseUp F r D) (hc : Injective D)
    (u : ∀ n : ℕ, ∀ j : Fin w, (F n j).traceV.length = 2 * r n)
    (v : ∀ n : ℕ, bodyF (F n) = r') :
    Tendsto (fun n => (σ n) (P.tuneK (lovely (F n) C (Twah.letters w) (r n))))
      atTop (𝓝 (Twah.witness C (Twah.letters w) D r')) := by
  have ht : plateau F D := fun i j p => Eventually.of_forall (fun l => congrArg _ (hc p))
  refine rightRide S _ D F r' (Eventually.of_forall v) hu ht
    (Eventually.of_forall fun n k => ?_) h p a
  rw [u]
  calc _ ≤ 32*((0+2)*r n) := by omega
       _ ≤ _ := by gcongr; exact Nat.zero_le _

lemma duo_wins_two
    (U V : Gaia) (b : Bool) (i : Fin 2) (t : marchesR r A U V) (v : remainsR r A b i)
    (X Y : Gaia) (b' : Bool) (j : Fin 2) (T : marchesR r B X Y) (e : remainsR r B b' j)
    (u : Injective (zephyr U V X Y)) :
    Tendsto (fun n => (σ n) (P.stockS Z (A n) * P.stockS Z' (B n))) atTop
      (𝓝 (Lead.cash b * Lead.cash b' *
        Twah.witness ![Z,Z'] (Twah.letters 2) (zephyr U V X Y) ![(i,i),(j,j)])) := by
  let f (n : ℕ) : Fin 2 → Twah := ![liftS (A n), liftS (B n)]
  let D : Fin 2 → DirSpin := ![(i,i),(j,j)]
  let χ (n : ℕ) := Gemini.flourish (liftS (A n)) Z (R:=r n)
  let W := ![Z,Z']
  let g := zephyr U V X Y
  have h₁ : riseUp f r g := by
    rintro ⟨k,z⟩; fin_cases k <;> cases z <;> first | exact t.1 | exact t.2 | exact T.1 | exact T.2
  have h₂ (n : ℕ) (i : Fin 2) : (f n i).traceV.length = 2*r n := by
    fin_cases i <;> first | exact (A _).costs | exact (B _).costs
  have h₃ (n : ℕ) : bodyF (f n) = D := by
    funext k; fin_cases k
    · exact congrArg (fun z : Fin 2 => (z,z)) (v n).2
    exact congrArg (fun z : Fin 2 => (z,z)) (e n).2
  have hq := (shineUV_any_clan a S h p W _ _ _ h₁ u h₂ h₃).const_mul (Lead.cash b*Lead.cash b')
  have he (n : ℕ) :
      P.stockS Z (A n) * P.stockS Z' (B n) =
        (Lead.cash b*Lead.cash b') • P.tuneK (lovely (f n) W (Twah.letters 2) (r n)) := by
    simp only [P.liftS_paid,(v n).1,(e n).1,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]
    rw [mul_comm (Lead.cash b') (Lead.cash b)]
    exact congrArg (fun t : P.Test => (Lead.cash b * Lead.cash b') • t)
      (P.songsAg (lovely (f n) W (Twah.letters 2) _)
        ((χ n).mul (Gemini.flourish (liftS (B n)) Z')) (crossSl_val (A n) (B n) Z Z')).symm
  simp_rw [he,map_smul,smul_eq_mul]
  exact hq

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
