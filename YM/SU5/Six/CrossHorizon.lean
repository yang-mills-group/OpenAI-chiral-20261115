import YM.SU5.Six.MixedRide
/-!
# Towards the matrix zoom: mixed clan heat price

Grid purchases `penetration_cross` (includes (fgmixed) via `traffic_two`)
and passage to projected heat & space translations in `initialPoint_cross`,
`evenlater_cross`, adapting `YM/SU5/Cordial/{Meridian,Horizon}.lean`.
This directly gives enough mixed Laplace/characteristic limits for the matrix
measure argument, without needing variable time ratio tending to zero (we buy
the time 0 test with 0 translation in time itself).
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
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

variable (P : Spine) (x : P.Spectrum0 3) (Z Z' : Lead.Clan) (s : ℕ)
         (c r : ℕ → ℕ) (J : List Street)
local notation "M" => timeMesh P.par
local notation "N₀" => notch M
local notation "ε" => YM.basis (3 : Axis)
local notation "β" => P.otherSpectrum 3 3 x
local notation "V" => P.ColorHil 3 (β)
local notation "U" => P.voyageF 3 (β)
local notation "S" => P.physicalEnergy 3 (β)

lemma traffic_two (t ν : ℕ) (n : Street → ℤ) :
    let f := P.flash t
    inner ℂ (P.shard x Z s t)
      ((U).raw J (fun i => N₀ s (n i)) ((S).E (whenly M s ν) (P.shard x Z' s t))) =
    P.singleState 3 s (β)
      (P.stockS Z (f.mirror 3 0) * P.stockS Z' (P.ride J n (P.migrate 3 f ν))) := by
  intro f
  let W := P.stockS Z f; let W' := P.stockS Z' f; let A := P.brightC Z' s t
  let v := P.passesLater 3 s ν A; let p := P.certify 3 s J n v; let u := P.viewF 3 (β) s p
  let Q := P.luggage 3 J n; let b := P.singleState 3 s (β)
  have hu : u = (U).raw J (fun i => N₀ s (n i)) ((S).E (whenly M s ν) (P.shard x Z' s t)) :=
    (P.ship_ideal 3 (β) s J n v).trans
      (congrArg ((U).raw J (fun i => N₀ s (n i))) (P.releasedLater 3 (β) s ν A))
  calc _ = inner ℂ (P.shard x Z s t) u := congrArg (inner ℂ (P.shard x Z s t)) hu.symm
       _ = b ((P.reflectTest 3 W) * Q (P.shifts 3 ν W')) := P.released_gram 3 (β) s (P.brightC Z s t) p
       _ = _ := congrArg b (congrArg₂ (· * ·) (P.mirror_stock Z 3 f)
          ((congrArg Q (P.acrossStocks Z' 3 f ν)).trans (P.pal_transfer Z' J n (P.migrate 3 f ν))))

private lemma bend_true' : inversion 3 ε = -ε := by
  ext i; by_cases z : i=3
  · subst i; simp [inversion]
  simp [inversion,z]

variable {P x c r} (A : Launch P c r) {d : ℕ → ℝ}
         (Y : readyUV P c r x d) (p : Tendsto d atTop (𝓝 0)) (hZZ : Z ≠ Z')
include A Y p hZZ
local notation "Φ" X:max i:max => P.shard x X (c i) (r i)
local notation "C₀" => (purePrice Z : ℂ) * (purePrice Z' : ℂ)

lemma penetration_cross
    (q : ℕ → ℕ) (z : ℝ) (v : 0 ≤ z) (n : Street → ℕ → ℤ) (t : Street → ℝ)
    (N : ∀ i ∈ J, P.bargain r (n i) (t i)) (Q : P.bargain r (fun i => (q i:ℤ)) z) :
    Tendsto (fun i : ℕ => inner ℂ (Φ Z i) ((U).raw J (fun k => N₀ (c i) (n k i))
        ((S).E (whenly M (c i) (q i)) (Φ Z' i)))) atTop (𝓝 C₀) := by
  let F(i) := P.flash (r i); let x' := palace J t
  let G(i) := (F i).mirror 3 0; let kS(i) := P.migrate 3 (F i) (q i)
  let L(i) := P.ride J (fun k => n k i) (kS i)
  let a₁ : Gaia := -ε; let a₀ : Gaia := (-2:ℝ) • ε; let v₀ := layoutFirst z x'; let v₁ := v₀+ε
  let D := zephyr a₀ a₁ v₀ v₁
  have he := P.heights_here r A.eager A.unitSize
  have hg : marchesR r G a₀ a₁ := by
    have hz := revolve 3 r F _ _ he A.eager
    rw [map_smul, bend_true', smul_neg,←neg_smul] at hz
    exact hz
  have hp : marchesR r L v₀ v₁ := by
    have k := P.rideLegs r J n N (P.marching 3 r F _ _ he _ z Q)
    let y : E4 := x'.val
    have hx : v₀ = (ε+ z • ε)+ y := by unfold v₀ layoutFirst siteOf y; abel
    have hv : v₁ = ((2:ℝ) • ε+ z • ε)+y := by unfold v₁; rw [hx]; module
    rw [hx,hv]; exact k
  have hr : remainsR r F false 0 := fun _ => ⟨rfl,rfl⟩
  have hh : remainsR r G false 0 := turnsZ (3:Axis) r F _ _ hr
  have hw : remainsR r L false 0 := P.rider_remain r J _ n (P.passRemain 3 r _ _ _ hr _)
  have hv(i : Gaia)(x : ℝ) : i 3=x → (i+ ε) 3=x+1 := fun h => by simp [h]
  have hV : v₀ 3 = z+1 := hv _ _ (Cordial.tip z _)
  have hU : v₁ 3 = z+1+1 := hv _ _ hV
  have hx : D = Cordial.duo z x' := by funext x; rcases x with ⟨x,y⟩; fin_cases x <;> cases y <;> rfl
  have hb(x y : Gaia)(h : x 3 < y 3) : x ≠ y := fun t => h.ne (t ▸ rfl)
  have ha : a₁ 3 = -1 := by unfold a₁; simp
  have ha0 : a₀ 3 = -2 := by unfold a₀; simp
  have u : Injective D := zephyr_non a₀ a₁ v₀ v₁ (hb _ _ (by rw [ha,ha0]; norm_num))
    (hb _ _ (by linarith)) ⟨hb _ _ (by linarith), hb _ _ (by linarith),hb _ _ (by linarith),
      hb _ _ (by linarith)⟩
  have hz := duo_wins_two Z Z' 3 A G L Y p _ _ false 0 hg hh _ _ false 0 hp hw u
  have ht : Lead.cash false * Lead.cash false *
      Twah.witness ![Z,Z'] (Twah.letters 2) D (![(0,0),(0,0)]) = C₀ := by
    rw [show (![(0,0),(0,0)] : Fin 2 → DirSpin) = 0 from funext fun k => by fin_cases k <;> rfl,
        hx, show Lead.cash false = (1/5:ℂ) by simp [Lead.cash,phaseF]]
    exact goes_cross hZZ _ _
  let fz(i : ℕ) := P.singleState 3 (c i) (β) (P.stockS Z (G i)*P.stockS Z' (L i))
  have hx : Tendsto fz atTop (𝓝 C₀) := by rw [←ht]; exact hz
  exact hx.congr fun i => (P.traffic_two x Z Z' (c i) J (r i) (q i) (fun k => n k i)).symm

open OS.Semigroup (F)
open OS.Semigroup.Balloon

local notation "ρ" i:max => P.dew (c i) (r i)
local notation "G" => P.ManyF 3 (β)
local notation "Ψ'" => P.seasons 3 (β)
local notation "π'" => P.wealth 3 (β)
local notation "φ" X:max i:max => P.lucid x X (c i) (r i)

omit A Y p hZZ in
private lemma light_repay' (X Y : V) :
    inner ℂ ((π') X) ((π') Y) = inner ℂ (P.visitors 3 (β) X) Y := by
  let g := P.visitors 3 (β); change inner ℂ (g X) (g Y) = _
  have hc : g.adjoint = g := Alliance.symmetricstack ..
  have he : g (g X) = g X := Alliance.grounded _ _ ((U).planted (look 3) X)
  exact (ContinuousLinearMap.adjoint_inner_left g Y (g X)).symm.trans
    (congrArg (inner ℂ · Y) ((DFunLike.congr_fun hc _).trans he))

omit hZZ in
lemma shard_bill' : Limited V (fun i => Φ Z i) :=
  OS.Semigroup.Balloon.hasLimit (H:=V) (horn_norm Z A Y p)

omit hZZ in
lemma lucid_bill' : Limited G (fun i => φ Z i) := by
  obtain ⟨k,h⟩ := shard_bill' Z A Y p
  exact ⟨k,h.mono fun i v => le_trans (P.bank_cost 3 (β) (Φ Z i)) v⟩

private lemma highBeam_cross (v : Bank) {z : ℝ} (q : 0 ≤ z) (D : ℕ → ℕ)
    (w : P.bargain r (fun i => (D i:ℤ)) z) :
    let T i := whenly M (c i) (D i)
    Tendsto (fun i => inner ℂ (φ Z i)
      ((Ψ').U (P.horizon c r v i) ((Ψ').E (T i) (φ Z' i)))) atTop (𝓝 C₀) := by
  let g(i : Street) := v.val i.val; let f(i : Street)(n : ℕ) := P.pan r v n i
  let X(i) := P.pit c r v i
  let SP := Ψ'; let L := look (3:Axis); intro T
  have h : ∀ i : Street, P.bargain r (f i) (g i) := fun i => P.intendR r (g i) A.eager
  let qX(i : ℕ) := (U).raw L (X i) ((S).E (T i) (Φ Z' i))
  have he : Tendsto (fun i => inner ℂ (Φ Z i) (qX i)) atTop (𝓝 C₀) :=
    penetration_cross Z Z' L A Y p hZZ D z q (fun i n => f i n) g (fun i _ => h i) w
  have hh(i : ℕ) : SP.U (P.horizon c r v i) (SP.E (T i) (φ Z' i)) = (π') (qX i) := by
    have ht := P.bankHeat 3 (β) (T i) (Φ Z' i)
    exact (congrArg (SP.U (P.horizon c r v i) : (P.ManyF 3 (β)).space → _) ht.symm).trans
      (P.roll_motion 3 (β) (P.pit c r v i) ((S).E (T i) (Φ Z' i)))
  let K := P.visitors 3 (β)
  have hp : Limited (V) qX := le_seam (fun i => Φ Z' i) (shard_bill' Z' A Y p)
    fun i => ((U).raw_isometry L (X i) ((S).E (T i) (Φ Z' i))).le.trans
      (heatedLim (S) (T i) (Φ Z' i))
  have hv : Tendsto (fun i => inner ℂ (K (Φ Z i)) (qX i) - inner ℂ (Φ Z i) (qX i))
      atTop (𝓝 0) := (OS.Semigroup.Balloon.aura' V qX _ hp (whole_sky Z A Y p)).congr fun i =>
    inner_sub_left (𝕜:=ℂ) (K (Φ Z i)) (Φ Z i) (qX i)
  exact (unifier hv he).congr fun i =>
    ((congrArg (inner ℂ (φ Z i)) (hh i)).trans (light_repay' (Φ Z i) (qX i))).symm

lemma rays_cross (v : Bank) {z : ℝ} (q : 0 ≤ z) (D : ℕ → ℕ)
    (w : P.bargain r (fun i => (D i:ℤ)) z) (F : ℕ → Bank)
    (h : Tendsto (fun i => (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i => inner ℂ (φ Z i)
      ((Ψ').U (F i) ((Ψ').E (whenly M (c i) (D i)) (φ Z' i)))) atTop (𝓝 C₀) := by
  let t(i) := whenly M (c i) (D i)
  let x₀(i : ℕ) := φ Z i; let x'(i : ℕ) := φ Z' i
  let B' := Ψ'; let g := P.horizon c r v; let E i := B'.E (t i) (x' i)
  have he := highBeam_cross Z Z' A Y p hZZ v q D w
  have hv : Tendsto (fun i => B'.U (F i) (x' i)- B'.U (g i) (x' i)) atTop (𝓝 0) :=
    neighbor Z' A Y p v (P.pan r v) F (fun i => P.intendR r (reveal i v) A.eager) h
  have hw : Tendsto (fun i => inner ℂ (x₀ i) (B'.U (F i) (E i)) -
                              inner ℂ (x₀ i) (B'.U (g i) (E i))) atTop (𝓝 0) :=
    (aura G x₀ _ (lucid_bill' Z A Y p) (realize_shim (Ψ') x' t F g hv)).congr
      fun i => inner_sub_right (𝕜:=ℂ) (x₀ i) (B'.U (F i) (E i)) (B'.U (g i) (E i))
  exact unifier hw he

lemma evenlater_cross (v : Bank) {z : ℝ} (q : 0 < z) (E : ℕ → ℝ≥0)
    (w : P.dimensionS c r E z) (F : ℕ → Bank) (h : Tendsto (fun i => (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i => inner ℂ (φ Z i) ((Ψ').U (F i) ((Ψ').E (E i) (φ Z' i))))
      atTop (𝓝 C₀) := by
  let T := Ψ'; let v₀(i : ℕ) := φ Z i; let v'(i : ℕ) := φ Z' i
  let D := (grantR A z q.le).choose; have he := (grantR A z q.le).choose_spec
  let L(i : ℕ) := whenly M (c i) (D i)
  let I(i : ℕ) := T.E (E i) (v' i); let G'(i : ℕ) := T.E (L i) (v' i)
  have hx : Tendsto (fun i => T.U (F i) (I i) - T.U (F i) (G' i)) atTop (𝓝 0) :=
    (soarE T F _ (uniform_zoom T v' (fun i => P.dew_pos _ (A.unitSize i)) w he.2 q
      (lucid_bill' Z' A Y p))).congr fun i => map_sub (T.U (F i)) (I i) (G' i)
  let f(i) := inner ℂ (v₀ i) (T.U (F i) (I i)); let g(i) := inner ℂ (v₀ i) (T.U (F i) (G' i))
  have hh : Tendsto (fun i => f i - g i) atTop (𝓝 0) := (aura G v₀ _ (lucid_bill' Z A Y p) hx).congr
    fun i => inner_sub_right (𝕜:=ℂ) (v₀ i) (T.U (F i) (I i)) (T.U (F i) (G' i))
  exact unifier hh (rays_cross Z Z' A Y p hZZ v q.le D he.1 F h)

lemma initialPoint_cross (v : Bank) (F : ℕ → Bank) (h : Tendsto (fun i => (ρ i)⁻¹ • F i) atTop (𝓝 v)) :
    Tendsto (fun i => inner ℂ (φ Z i) ((Ψ').U (F i) (φ Z' i))) atTop (𝓝 C₀) := by
  let x'(i : ℕ) := φ Z' i; let T := Ψ'; let g(i : ℕ) := T.E (whenly M (c i) 0) (x' i)
  have he(i : ℕ) : g i = x' i := (congrArg (fun t => T.E t (x' i)) (when_zero ..)).trans
    (DFunLike.congr_fun T.eZero _)
  exact (rays_cross Z Z' A Y p hZZ v le_rfl (fun _ => 0) (unpaid_move (P:=P)) F h).congr
    fun i => congrArg (inner ℂ (φ Z i) ∘ T.U (F i)) (he i)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
