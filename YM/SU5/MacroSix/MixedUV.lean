import YM.SU5.Cordial.Meridian

/-!
# Distinct-clan UV purchase for the macroscopic six-channel theorem

Use `Prototype.rightRide` on the **two** Twahs and their **different** clans.
This uses `Launch` and `readyUV` of *this* x. The same-clan estimate is
already in `Cordial/Meridian`. These proofs, in particular `trafficCross`
and `penetrationCross`, are adaptations/generalizations of
`Cordial/{Fountain,LatticeFieldEstimates,Meridian}`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Ballad.Cordial

open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods
  Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear
  Window Skye Emu Onyx Kea Flare Dial Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Twah
open Lead (Clan)
open YM.Stationary (Gaia)

variable {J : Type*} {C : J → Clan} (P : Cellz J → Gaia) (D : J → DirSpin)

private lemma wickFour {T : Type*} (d : T → T → ℂ) (p q r s : T) :
    runes d [p,q,r,s] = d p q*d r s - d p r*d q s + d p s*d q r := by
  simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring

/-- Wick cross-terms between *distinct representation or generation slots* vanish.
The four-letter price is therefore just the product of the two same-body prices. -/
theorem chorus4_ne (i j : J) (h : C i ≠ C j) :
    witness C [i,j] P D = lyric P D (C i) i * lyric P D (C j) j := by
  let f (p q : Slot) := runes (germRho P D) (sayHi (sayHi [] i p) j q)
  let c := billX P D i i * billX P D j j
  have hf (p : Slot) (hp : p ∈ colors (C i)) :
      ∑ q ∈ colors (C j), f p q = numberX (C j) * c := by
    calc
      _ = ∑ _q ∈ colors (C j), c := by
        refine sum_congr rfl (fun q hq ↦ ?_)
        have hn : p ≠ q := by
          rintro rfl
          exact h ((mem_filter.mp hp).2.symm.trans (mem_filter.mp hq).2)
        change runes _ [(i,p,true),(i,p,false),(j,q,true),(j,q,false)] = _
        rw [wickFour]
        simp [funds, funds_neg, dcash, hn, c]
      _ = numberX (C j) * c := by rw [sum_const, colors_card]; simp [numberX]
  change ∑ p ∈ colors (C i), ∑ q ∈ colors (C j), f p q = _
  rw [sum_congr rfl hf, sum_const, colors_card]
  simp only [lyric, numberX, c, nsmul_eq_mul]
  ring

/-- The two-clan analogue of `goesO`. -/
theorem flashWitness_ne (Z W : Clan) (h : Z ≠ W) (t : ℝ) (x : Bank) :
    (1/5:ℂ) * (1/5) * witness ![Z,W] (Twah.letters 2) (duo t x) 0 =
      numberX Z * P20 / 5 * (numberX W * P20 / 5) := by
  rw [show Twah.letters 2 = [0,1] from rfl, chorus4_ne _ _ 0 1 (by exact h)]
  unfold lyric
  obtain ⟨a,b,-⟩ := reunion t x
  rw [a,b]
  change (1/5:ℂ) * (1/5) * (numberX Z * P20 * (numberX W * P20)) = _
  ring
end YM.CF.Buffered.Ballad.Cordial

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
  Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

namespace Spine

variable (P : Spine) (x : P.Spectrum0 3) (Z W : Lead.Clan) (s : ℕ)
local notation "M" => timeMesh P.par
local notation "N₀" => notch M
local notation "β" => P.otherSpectrum 3 3 x
local notation "U₃" => P.voyageF 3 (β)
local notation "S" => P.physicalEnergy 3 (β)

private def mixedPair (Z W : Lead.Clan) {r : ℕ} (A B : Lead r) :=
  plait ![liftS A,liftS B] ![Z,W] (Twah.letters 2) r

private lemma mixedPair_val {r : ℕ} (A B : Lead r) :
    mixedPair Z W A B = (liftS A).groundWord r Z * (liftS B).groundWord r W :=
  congrArg ((liftS A).groundWord r Z * ·) (mul_one ((liftS B).groundWord r W))

/-- Payment in axis 3 of the precisely translated marks. Unprojected (ColorHil)
formula, with the same actual `singleState` in all entries. -/
theorem trafficCross (J : List Street) (t ν : ℕ) (n : Street → ℤ) :
    let f := P.flash t
    inner ℂ (P.shard x Z s t) ((U₃).raw J (fun i ↦ N₀ s (n i))
      ((S).E (whenly M s ν) (P.shard x W s t))) =
        P.singleState 3 s (β) (P.stockS Z (f.mirror 3 0) *
          P.stockS W (P.ride J n (P.migrate 3 f ν))) := by
  intro f
  let F := P.stockS Z f
  let G := P.stockS W f
  let A := P.brightC Z s t
  let B := P.brightC W s t
  let v := P.passesLater 3 s ν B
  let p := P.certify 3 s J n v
  let u := P.viewF 3 (β) s p
  let Q := P.luggage 3 J n
  let b := P.singleState 3 s (β)
  have hu : u = (U₃).raw J (fun i ↦ N₀ s (n i))
      ((S).E (whenly M s ν) (P.shard x W s t)) :=
    (P.ship_ideal 3 (β) s J n v).trans (congrArg ((U₃).raw J (fun i ↦ N₀ s (n i)))
      (P.releasedLater 3 (β) s ν B))
  rw [← hu]
  calc
    _ = b (P.reflectTest 3 F * Q (P.shifts 3 ν G)) := P.released_gram 3 (β) s A p
    _ = _ := congrArg b (congrArg₂ (· * ·) (P.mirror_stock Z 3 f)
        ((congrArg Q (P.acrossStocks W 3 f ν)).trans
          (P.pal_transfer W J n (P.migrate 3 f ν))))

local notation "ε" => YM.basis (3:Axis)
private lemma bend_third : inversion 3 ε = -ε := by
  ext i; by_cases z : i = 3; subst i; simp [inversion]; simp [inversion,z]

variable {P x} {c r : ℕ → ℕ} (A : Launch P c r) {d : ℕ → ℝ}
  (Y : readyUV P c r x d) (p : Tendsto d atTop (𝓝 0))
include A Y p

/-- Generalize `duo_wins` to separate family arguments. No equality or symmetry of
characters in different sectors is assumed. Here time and election axis are 3. -/
theorem duoCross (F G : ∀ i, Lead (r i)) (T T' V V' : Gaia)
    {b b' : Bool} {i j : Fin 2} (u : marchesR r F T T') (v : marchesR r G V V')
    (e : remainsR r F b i) (g : remainsR r G b' j) (z : Injective (zephyr T T' V V')) :
    Tendsto (fun n ↦ P.singleState 3 (c n) (β)
      (P.stockS Z (F n) * P.stockS W (G n))) atTop
      (𝓝 (Lead.cash b * Lead.cash b' *
        Twah.witness ![Z,W] (Twah.letters 2) (zephyr T T' V V') ![(i,i),(j,j)])) := by
  let f (n : ℕ) : Fin 2 → Twah := ![liftS (F n),liftS (G n)]
  let D : Fin 2 → DirSpin := ![(i,i),(j,j)]
  let χ (n : ℕ) := Gemini.flourish (liftS (F n)) Z (R:=r n)
  let C : Fin 2 → Lead.Clan := ![Z,W]
  let K := zephyr T T' V V'
  have h₁ : riseUp f r K := by
    rintro ⟨k,w⟩; fin_cases k <;> cases w <;>
      first | exact u.1 | exact u.2 | exact v.1 | exact v.2
  have h₂ (n : ℕ) (k : Fin 2) : (f n k).traceV.length = 2*r n := by
    fin_cases k <;> first | exact (F _).costs | exact (G _).costs
  have h₃ (n : ℕ) : bodyF (f n) = D := by
    funext k; fin_cases k
    · exact congrArg (fun z : Fin 2 ↦ (z,z)) (e n).2
    exact congrArg (fun z : Fin 2 ↦ (z,z)) (g n).2
  have ht : plateau f K := fun i j p ↦ Eventually.of_forall fun _ ↦ congrArg _ (z p)
  have hr := rightRide A C K f D (Eventually.of_forall h₃) h₁ ht
    (Eventually.of_forall fun n k ↦ (by
      rw [h₂]
      calc
        _ ≤ 32*((0+2)*r n) := by omega
        _ ≤ _ := by gcongr; exact Nat.zero_le _)) Y p 3
  have he (n : ℕ) : P.stockS Z (F n) * P.stockS W (G n) =
      (Lead.cash b * Lead.cash b') • P.tuneK (lovely (f n) C (Twah.letters 2) (r n)) := by
    simp only [P.liftS_paid,(e n).1,(g n).1,Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm,smul_smul]
    rw [mul_comm (Lead.cash b') (Lead.cash b)]
    exact congrArg (fun t : P.Test ↦ (Lead.cash b * Lead.cash b') • t)
      (P.songsAg (lovely (f n) C (Twah.letters 2) _)
        ((χ n).mul (Gemini.flourish (liftS (G n)) W))
        (mixedPair_val Z W (F n) (G n))).symm
  simp_rw [he,map_smul,smul_eq_mul]
  exact hr.const_mul (Lead.cash b * Lead.cash b')

/-- Off-diagonal UV price, with both heat displacement and transverse translation.
Ticks in these formulas are full ticks. Inputs include actual purchase conditions, all
poses are on the course, both ends on the same axis-3 character. -/
theorem penetrationCross (h : Z ≠ W) (J : List Street) (q : ℕ → ℕ) (z : ℝ) (hz : 0 ≤ z)
    (n : Street → ℕ → ℤ) (t : Street → ℝ)
    (N : ∀ i ∈ J, P.bargain r (n i) (t i)) (Q : P.bargain r (fun i ↦ (q i:ℤ)) z) :
    Tendsto (fun i ↦ inner ℂ (P.shard x Z (c i) (r i))
      ((U₃).raw J (fun k ↦ N₀ (c i) (n k i))
        ((S).E (whenly M (c i) (q i)) (P.shard x W (c i) (r i))))) atTop
      (𝓝 ((purePrice Z:ℂ) * (purePrice W:ℂ))) := by
  let F (i) := P.flash (r i)
  let x' := palace J t
  let G (i) := (F i).mirror 3 0
  let kS (i) := P.migrate 3 (F i) (q i)
  let L (i) := P.ride J (fun k ↦ n k i) (kS i)
  let a₁ : Gaia := -ε
  let a₀ : Gaia := (-2:ℝ) • ε
  let v₀ := layoutFirst z x'
  let v₁ := v₀+ε
  let D := zephyr a₀ a₁ v₀ v₁
  have he := P.heights_here r A.eager A.unitSize
  have hg : marchesR r G a₀ a₁ := by
    have hz := revolve 3 r F _ _ he A.eager; rw [map_smul, bend_third, smul_neg,← neg_smul] at hz
    exact hz
  have hp : marchesR r L v₀ v₁ := by
    have k := P.rideLegs r J n N (P.marching 3 r F _ _ he _ z Q)
    let y : E4 := x'.val; have hx : v₀=(ε+ z • ε)+ y := by unfold v₀ layoutFirst siteOf y; abel
    have hv : v₁=((2:ℝ) • ε+ z • ε)+y := by unfold v₁; rw [hx]; module
    rw [hx,hv]; exact k
  have hr : remainsR r F false 0 := fun i ↦ ⟨rfl,rfl⟩
  have hh : remainsR r G false 0 := turnsZ (3:Axis) r F _ _ hr
  have hw : remainsR r L false 0 := P.rider_remain r J _ n (P.passRemain 3 r _ _ _ hr _)
  have hv (i : Gaia) (x : ℝ) : i 3=x → (i+ ε) 3=x+1 := fun h ↦ by simp [h]
  have hV : v₀ 3=z+1 := hv _ _ (Cordial.tip z _); have hU : v₁ 3=z+1+1 := hv _ _ hV
  have hx : D=Cordial.duo z x' := by
    funext x; rcases x with ⟨x,y⟩; fin_cases x <;> cases y <;> rfl
  have hb (x y : Gaia) (h : x 3 < y 3) : x ≠ y := fun t ↦ h.ne (t ▸ rfl)
  have ha : a₁ 3 = -1 := by unfold a₁; simp
  have ha0 : a₀ 3 = -2 := by unfold a₀; simp
  have u : Injective D := zephyr_non a₀ a₁ v₀ v₁ (hb _ _ (by rw [ha,ha0]; norm_num))
    (hb _ _ (by linarith)) ⟨hb _ _ (by linarith), hb _ _ (by linarith),
      hb _ _ (by linarith), hb _ _ (by linarith)⟩
  have hl := duoCross Z W A Y p G L _ _ _ _ hg hp hh hw u
  have ht : Lead.cash false * Lead.cash false *
      Twah.witness ![Z,W] (Twah.letters 2) D (![(0,0),(0,0)]) =
        (purePrice Z:ℂ) * (purePrice W:ℂ) := by
    rw [show (![(0,0),(0,0)] : Fin 2 → DirSpin)=0 from funext fun k ↦ by fin_cases k <;> rfl,
      hx, show Lead.cash false = (1/5:ℂ) by simp [Lead.cash,phaseF]]
    rw [flashWitness_ne Z W h, price_as, price_as]
    rfl
  let fz (i : ℕ) := P.singleState 3 (c i) (β) (P.stockS Z (G i) * P.stockS W (L i))
  have hy : Tendsto fz atTop (𝓝 ((purePrice Z:ℂ) * (purePrice W:ℂ))) := by rw [← ht]; exact hl
  exact hy.congr fun i ↦ (P.trafficCross x Z W (c i) J (r i) (q i) (fun k ↦ n k i)).symm

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.penetrationCross
