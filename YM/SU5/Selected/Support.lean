import VerifiedSatinGroundInteraction

/-!
# A fixed physical probe (Satin resolution observables), before conditioning

Fix a late **observing resolution**, not a UV threshold or period. Buy a first-Pane,
continuous-coefficient, neutral physical test there. Use the fixed-separation convention
**of Filigree**, i.e. the creator sites are away from all of the removal anchors at which
we test center charge. This is a statement about positions in the support of a resolution
test, not the distance between two regions carrying separately gauge-invariant observations.
Lengths are real level-0 *gauge* spacings (Tapestry conventions). We verify them also on
the actual periods, on the SAME sharp-normalized course as in the specified projection.
The pure geometry lemmas from Signal used below take no other history inputs (we even pass
our own calibration to the period lemma; there is no use of an older election or limiting history).

Stencils really stay local through arbitrarily many refinements. Transition is of the
WHOLE probe (charged matter and gauge together), in the actual Q of the tower. We claim
neither that an inter-level map sends this observation into *upper rung Filigree*, nor
that it factors the measure/testing of overlapping supports. Thus not e.g. a theorem of
nontrivial pointlike fields, or of off-diagonal distributions obtained from convergent
probes whose physical sizes also go to ZERO.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FixedProbe
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark SatinVerification Tapestry Vacancy
open CF.Pannier.Chancel
open CF.Signal.Interval (separationCost Located)
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

lemma spacing_distance (Λ : Preparation) (s : ℕ) (x y : Cover) :
    dist (addressG Λ s x) (addressG Λ s y) =
      (separationCost x y : ℝ) / precisionAt Λ s := by
  let d (i : Axis) := ((x-y) i).natAbs
  have h := positiveScale Λ s
  have coord (i : Axis) : ‖(addressG Λ s x - addressG Λ s y) i‖ =
      (d i : ℝ)/precisionAt Λ s := by
    change ‖(x i : ℝ)/_-(y i : ℝ)/_‖ = _
    rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos h]
    dsimp only [d, Pi.sub_apply]; rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  rw [dist_eq_norm]; apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (div_nonneg (Nat.cast_nonneg _) h.le)).mpr
    intro i; rw [coord i]; gcongr; exact le_sup (f:=d) (mem_univ i)
  obtain ⟨i,_,hi⟩ := Finset.sup_mem_of_nonempty (s:=univ) (f:=d) univ_nonempty
  have eq : d i=separationCost x y := hi
  rw [← eq, ← coord]
  exact norm_le_pi_norm ..

/-- `AnchorGap` checks **all** distances that can be used in the Filigree grammar at
    these supports; `RSpace` uses sup distance. Lower bound (gauge grid): one
    gauge spacing of the (fixed) observing mesh. 
    Separately `levelAddress` says centers of gauge sites keep the same physical
    positions on finer meshes (separation of the *addresses*). -/
def AnchorGap {m : ℕ} (s : ℕ) (b : Fin m → Cover) (S : Finset Cover) : Prop :=
  0 < 1 / precisionAt Λ s ∧
    (∀ i, nodeC (b i) ∈ S) ∧
    ∀ i (y : Cover), nodeC y ∈ S → (∀ t, y ≠ b t) →
      1 / precisionAt Λ s ≤ dist (addressG Λ s (nodeC y)) (addressG Λ s (nodeC (b i)))

lemma anchor_gap {m : ℕ} (s : ℕ) {b : Fin m → Cover} {S : Finset Cover}
    (h : ∀ i, nodeC (b i) ∈ S) : AnchorGap (Λ:=Λ) s b S := by
  have hp:=positiveScale Λ s
  refine ⟨by positivity,h,fun i y _ t=>?_⟩
  rw [spacing_distance]; gcongr
  exact_mod_cast CF.Signal.Interval.separation_physical (t i)

lemma levelAddress (s n : ℕ) (x : Cover) :
    addressG Λ (s+n) (Λ.R.L.val^n • x)=addressG Λ s x := by
  induction n with
  | zero => simp
  | succ n h => rw [pow_succ',mul_smul,← Nat.add_assoc,addressUp,h]

lemma still_printed (s n : ℕ) (S : Finset Cover) (R : Set RSpace)
    (p : printedHere Λ l s S R) : printedHere Λ l (s+n) (volumeAround Λ l n S) R := by
  induction n with
  | zero => exact p
  | succ n h => rw [← Nat.add_assoc]; exact shielding Λ l (s+n) R _ h

variable {i k : ℕ → ℕ}{I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
  (G : GroundExtension Y H (i:=i) (k:=k) (E:=E))
local notation "Q"=> G.history
local notation "Ξ" r:max=> i (G.rows r)
local notation "η" r:max=> k (G.columns r)

/-- Geometry using the actual observation side. No change of spacing as we run farther
    down the paired path, even if the bare couplings/fields vary. -/
def PeriodGap (s : ℕ) (S : Finset Cover) (p : ℕ) : Prop :=
  let n := side Y p s
  ∀ x∈ S, ∀ y∈ S, (separation (wrap (More n) x) (wrap (More n) y) : ℝ) / precisionAt Λ s =
    dist (addressG Λ s x) (addressG Λ s y)
include V in
lemma geometry_money (S : Finset Cover) :
    ∀ᶠ r : ℕ in atTop, PeriodGap Y s S (i (G.rows r)) := by
  have he := (momentum Y s).eventually (CF.Signal.Interval.distanceLease K S)
  filter_upwards [(V.pick.grow_i.comp G.history.growsA).tendsto_atTop.eventually he] with r hr
  let a:=Ξ r
  change Located (tent Y H) S (momentm Y a s) at hr
  intro x hx y hy
  have ht : side Y (i (G.rows r)) s=(K).c (momentm Y a s):=(terrain Y H (Y.ir a) s).symm
  rw [ht, hr.2 x hx y hy, spacing_distance]

/-- Participating sharp readings here are divisions by the PAID signed partition. -/
lemma divide (s : ℕ) : ∀ᶠ r in atTop,
    let n := i (G.rows r); let m := k (G.columns r)
    Ferry Y s n m ∧ partitionZ (((Y.voyage n).X (Y.uv m)).gram s) Λ.U
      ((Y.voyage n).CapeT s) ≠ 0 :=
  (G.history.finance s).mono fun _ paid => ⟨paid, (Y.each_level _ _ s paid.depth paid.enters).valid⟩
lemma coherent_price {x : Family K} (h : TestFamily K true x) :
    Tendsto (fun r=> sharp Y H s (Ξ r) (η r) x) atTop (𝓝 (E s x)) := by
  obtain ⟨S,p⟩:=h.paid; obtain ⟨C,z⟩:=Journey.valuation Y H p; have Hx : pay x C := z
  have hC:=pay_nonneg Hx
  obtain ⟨_,_,t⟩:= G.history.implements s S
  apply Metric.tendsto_nhds.mpr; intro e hz
  let a:=e/(C+1); have hv:0<a:=by dsimp [a]; positivity
  filter_upwards [t a hv] with r c
  rw [dist_eq_norm]
  obtain ⟨_,_,_,_,b,_⟩:= c x p C Hx
  refine lt_of_le_of_lt b ?_
  have hp : a*(C+1)=e:=div_mul_cancel₀ _ (by positivity); linarith

abbrev KernelTest (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1≤Λ.x)
    := observable (tent Y H) true
/-- Carry one probe *unchanged as an observation*, using its refinement reps. -/
structure Carries (F : KernelTest Y H) (S : Finset Cover) (N : ℕ) : Prop where
  firstPane : F.val ∈ observ (tent Y H) S false
  keepsSize (n : ℕ) : printedHere Λ l (s+n) (volumeAround Λ l n S) (cabin N)
  nativeGap (n : ℕ) : ∀ᶠ r in atTop, PeriodGap Y (s+n) (volumeAround Λ l n S) (i (G.rows r))
  refines (n : ℕ) : (upward Y H G.history true F s n).val ∈
    observ (tent Y H) (volumeAround Λ l n S) true -- possibly both Panes
  unselected (n : ℕ) : E (s+n) (upward Y H G.history true F s n).val = E s F.val
  costs (n : ℕ) : Tendsto (fun r=> sharp Y H (s+n) (i (G.rows r)) (k (G.columns r))
      (upward Y H G.history true F s n).val) atTop (𝓝 (E s F.val))
  allLevels (n : ℕ) (j : Axis) (C : Arena Y H G.history.circuit j 0 true) :
    Vacancy.cap Y H V (s+n) G.history G.clipped j true C (upward Y H G.history true F s n) =
      Vacancy.cap Y H V s G.history G.clipped j true C F
  sameGround (j : Axis) (C : Arena Y H G.history.circuit j 0 true) :
    inner ℂ (Vacancy.seat0 Y H V G.history j true C)
      (Vacancy.cap Y H V s G.history G.clipped j true C F (Vacancy.seat0 Y H V G.history j true C)) = E s F.val

lemma carry (F : KernelTest Y H) (S : Finset Cover)
    (p : F.val ∈ observ (tent Y H) S false) : ∃ N : ℕ, Carries Y H V s G F S N := by
  obtain ⟨N,u⟩ := (fundCabin Λ l s S).exists
  obtain ⟨a,hc⟩ := (obs_in ..).1 p
  have h (n : ℕ) := proceeds Y H G.history.circuit s n a.widen
  refine ⟨N,p,fun n=>still_printed s n S _ u,fun n=>geometry_money Y H V _ G _,
    fun n=>chroma Y H G.history.circuit s n ((obs_in ..).2 ⟨a.widen,hc⟩), fun n=>(h n).2,?_,?_,
    fun j C=> Vacancy.inspected ..⟩
  · intro n; rw [← (h n).2]
    exact coherent_price Y H _ G (upward Y H Q true F s n).property.1
  intro n j C; have h' := Vacancy.cap_level (F:=F) Y H V s Q G.clipped j true C (s+n) (by omega)
  rwa [Nat.add_sub_cancel_left] at h'

open CF.Pannier.Chancel -- spin positions and Filigree
/-- Use this e.g. at **one** of the (nonempty set of) observing rungs; that's when
    we have fixed, and proved strictly positive, physical separation. -/
theorem current {Z C : ℝ} {d q w : ℕ} (p : Papal.Cornet Y H q d w C Z) (z : SU.Slot) (o : Cover) :
    ∀ᶠ s in atTop, let b := booty o d q; let S := Sen o (payout d q w)
                    ∃ (F : KernelTest Y H) (N : ℕ), AnchorGap (Λ:=Λ) s b S ∧
                      F.val ∈ Filigree (tent Y H) (Window.family z) b S ∧
                      Carries Y H V s G F S N ∧ 1/4 ≤ ‖E s F.val‖ := by
  filter_upwards [Papal.certificate Y H C Z z p I E V] with s a
  obtain ⟨_,_,f,_,h,h',_,_,c⟩:=a o
  intro b S
  have hp:=FilTest h
  let F : KernelTest Y H := ⟨f,aux_test hp.widen, fun _=>h'⟩
  obtain ⟨N,t⟩:= carry Y H V s G F S ((obs_in ..).2 ⟨hp,h'⟩)
  exact ⟨F,N,anchor_gap s (fun m=>Papal.stake_centers Y H o d q w m),h,t,c⟩

end YM.CF.Buffered.Afterglow.Tower.FixedProbe
#check @YM.CF.Buffered.Afterglow.Tower.FixedProbe.current
#print axioms YM.CF.Buffered.Afterglow.Tower.FixedProbe.spacing_distance
#print axioms YM.CF.Buffered.Afterglow.Tower.FixedProbe.divide
#print axioms YM.CF.Buffered.Afterglow.Tower.FixedProbe.current
