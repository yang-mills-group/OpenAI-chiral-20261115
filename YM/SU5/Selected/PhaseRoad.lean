import YM.SU5.Selected.Threshold
import YM.SU5.Selected.Halo
/-!
# Phase road on the actual ellipse drives

Continues **into** the phase representation; buys full Mink time and spatial dense-grid
transverse translation in every character of same unselected marked ellipse drive.
Joint uniqueness in all `Victory`s. Intrinsic OS real-time via dummy translations to
access heat API (port from Tower.TimeKeeper). Norm hol on interior and agreement on
ALL underlying selected representations, payments, Gram etc.

Remaining Obligation: spatial all-real motion and other relativistic requirements. Do NOT
read ride S.U as giving spatial dynamics; see `turnstile` for what we claim now.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
private noncomputable def S₀ := (clockdrive Y H V Q.circuit j 0 strict C).monoAxis j
local notation "S" => S₀ Y H V Q j strict C
lemma luminous (t : ℝ≥0) : advance Y H V Q.circuit j 0 strict C t ∈ driveAlgebra Y H V Q Qt j strict C :=
  heat_complete (S) (𝔅) (fills (timeMesh Λ)) (fun _ v => clock_at Y H V Q Qt j strict C v) t

def coat (t : ℝ≥0) : driveAlgebra Y H V Q Qt j strict C := lamp (S) (𝔅) (luminous Y H V Q Qt j strict C) t
local notation "A₀" => coat Y H V Q Qt j strict C
lemma coat_epoch (t : ℝ≥0) : (A₀ t).val=advance Y H V Q.circuit j 0 strict C t := rfl
lemma coat_mark (n : ℕ) : A₀ (θt s n) = ψ s n := rfl
lemma coats_warm : Warm (Ρ) (fun t => Π (A₀ t)) := by
  apply (stroll_dense Y H V Q Qt j strict C f).mono
  intro x h
  obtain ⟨r,v⟩ := Set.mem_iUnion.mp h; obtain ⟨y,p⟩ := v
  obtain ⟨t,z,q⟩ := predecessor Y H r Q.circuit j 0 strict y
  let n := r+t; let T := θt n 1
  refine mem_iUnion.mpr ⟨T, mem_iUnion.mpr ⟨(show 0 < T from when_pos (Μ) _ _ zero_lt_one),a₀ n z,?_⟩⟩
  change (Π (ψ (r+t) 1)) (a₀ (r+t) z)=x
  rw [slot_time,mul_one,q,flourishes,p]

/-- This Semigroup used only to access ONE DIMENSIONAL measures and analytic continuation. -/
def ride := pecos (S₀ Y H V Q j strict C) (driveAlgebra Y H V Q Qt j strict C)
    (procession Y H V Q Qt j strict C f) (luminous Y H V Q Qt j strict C) (coats_warm Y H V Q Qt j strict C f)
local notation "L" => ride Y H V Q Qt j strict C f
lemma ride_advance (t : ℝ≥0) : (L).E t = Π (A₀ t) := rfl
lemma ride_ticks (x : 𝔙 s) (n : ℕ) : (L).E (θt s n) (a₀ s x) = a₀ s (tick Y H s j 0 strict (2*n) x) :=
  slot_time Y H V s Q Qt j strict C f x n
lemma ride_affordable {x : Ρ} (p : ∀ (s n : ℕ), (Π (ψ s n)) x=x) (t : ℝ≥0) : (L).E t x=x := by
  suffices h : (fun t => (L).E t x)=(fun _ : ℝ≥0 => x) by exact congrFun h _
  apply (fills (timeMesh Λ)).denseRange_val.equalizer ((L).continuousE _) continuous_const; funext y
  obtain ⟨a,v,u⟩ := MeshClock.split _ y.property
  dsimp only [Function.comp_apply]; rw [←u]; exact p a v

open Complex
/-- A witness of analytic continuation that stays in the drive algebra for interior times. -/
def air (z : ℂ) : driveAlgebra Y H V Q Qt j strict C := halo (S) (𝔅) (luminous Y H V Q Qt j strict C) (-Complex.I*z)
local notation "Z" => air Y H V Q Qt j strict C
lemma air_positive {z : ℂ} (p : 0<z.im) : -Complex.I*z∈inside := by change 0<(-Complex.I*z).re; simpa using p
lemma unselected_air {z : ℂ} (p : 0<z.im) : (Z z).val=continued Y H V Q.circuit j 0 strict C z := halo_val (S) (𝔅) (luminous Y H V Q Qt j strict C) _ (air_positive p)
lemma selected_air {z : ℂ} (p : 0<z.im) : Π (Z z) = (L).F (-Complex.I*z) :=
  (pecos_F _ (𝔅) (procession Y H V Q Qt j strict C f) (luminous Y H V Q Qt j strict C) (coats_warm Y H V Q Qt j strict C f) (air_positive p)).symm

/-- Continue from strictly positive imaginary time, with norm analytic interior and strong edge semantics. -/
lemma airs (t : ℝ) (u : ℝ≥0) (p : 0<u) : Π (Z ((t:ℂ)+((u:ℝ):ℂ)*Complex.I)) = (L).edge t * (L).E u := by
  have hu := air_positive (show 0<((t:ℂ)+((u:ℝ):ℂ)*Complex.I).im from (by simpa using p)) -- positivity cast
  -- write hu as needed
  rw [selected_air Y H V Q Qt j strict C f (show 0<((t:ℂ)+((u:ℝ):ℂ)*Complex.I).im from (by simpa using p)),
    ← (L).roots_heat p, ContinuousLinearMap.mul_def, OS.Semigroup.along (L) (OS.Semigroup.dur.mpr p) t] -- comp vs mul
  congr 1; apply Complex.ext <;> simp [duration,sideways] -- tune

lemma ride_anal : AnalyticOnNhd ℂ (fun z => (L).F (-Complex.I*z)) {z:ℂ|0<z.im} :=
  fun _ p => ((L).localHeat _ (air_positive p)).comp (analyticAt_const.mul analyticAt_id)
lemma ride_continue (x : Ρ) (t : ℝ) : Tendsto (fun u : ℝ≥0 => (Π (Z ((t:ℂ)+((u:ℝ):ℂ)*Complex.I))) x) (𝓝[>] 0) (𝓝 ((L).edge t x)) := by
  have hu : Tendsto (fun u : ℝ≥0 => (L).E u x) (𝓝[>] (0:ℝ≥0)) (𝓝 x) := by
    have h := ((L).continuousE x).continuousAt (x:=0)
    rw [ContinuousAt, show (L).E 0 x=x from ?_] at h; swap; · rw [(L).eZero]; rfl
    exact h.mono_left nhdsWithin_le_nhds
  apply Tendsto.congr' _ (((L).edge t).continuous.continuousAt.tendsto.comp hu)
  filter_upwards [self_mem_nhdsWithin] with k v
  rw [airs Y H V Q Qt j strict C f t k v]; rfl

lemma oriented (x y : 𝔅) (z : ℂ) : Φ (star x*(Z z*y)) = inner ℂ (Oa x) ((Π (Z z)) (Oa y)) := by rw [arrive_mul,arrive_pair]

open Germ
-- Transverse steps are not removed. actual dense `marks` representation, remains action of
-- spectator coordinate all moved specimens. Not claiming full Γ-axis continuity. 
local notation "U" a:max d:max => Π (Σ₁ a d)
lemma rides_trans {α} (d : marks Μ) (t : ℝ≥0) : Commute ((L).E t) (Π (Σ₁ α d)) := by
  apply Commute.map (f:=(procession Y H V Q Qt j strict C f))
    (x:=(A₀ t)) (y:=(Σ₁ α d))
    (show Commute (A₀ t) (Σ₁ α d) from Subtype.ext (ladder_time Y H V Q.circuit j 0 strict C α t d).symm)
lemma real_rides_trans {α} (d : marks Μ) (t : ℝ) : Commute ((L).edge t) (Π (Σ₁ α d)) :=
  lamp_orbit _ (rides_trans Y H V Q Qt j strict C f d 1) t

lemma transverse_mul (x : Trans j) (v u : marks Μ) : (Σ₁ x v)*(Σ₁ x u)=Σ₁ x (v+u) :=
  Subtype.ext (((ladder Y H V Q.circuit j 0 strict C).crew x).piles v u)
lemma transverse_c (x y : Trans j) (d p : marks Μ) : Commute (Σ₁ x d) (Σ₁ y p) :=
  Subtype.ext ((ladder Y H V Q.circuit j 0 strict C).cCom x y d p)
lemma transverse_z (x : Trans j) : Σ₁ x 0=1 := Subtype.ext (((ladder Y H V Q.circuit j 0 strict C).crew x).play_zero)
lemma transverse_price (x : Trans j) (d : marks Μ) : ‖Σ₁ x d‖≤1 := by
  obtain ⟨i,r,h⟩ := notch_exists (Μ) d
  obtain ⟨n,v⟩ := tours j (.inr (x,i,r))
  have h' := travellers Y H V Q Qt j strict C n; rw [traveller,Function.comp_apply,v] at h'
  rw [←h]; exact h'

def turnstile : Alliance (Trans j) (marks (timeMesh Λ)) (indoor Y H V Q Qt j strict C f) where
  crew a :=
    { play x := Π (Σ₁ a x)
      pulls i v := ((Π (Σ₁ a i)).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) ((NonUnitalStarAlgHom.norm_apply_le _ _).trans (transverse_price Y H V Q Qt j strict C a i)))
      play_zero := by rw [transverse_z,map_one]; rfl
      piles i k := by
        rw [←transverse_mul,map_mul]; rfl }
  cCom a b x y := (transverse_c Y H V Q Qt j strict C a b x y).map (procession Y H V Q Qt j strict C f)
lemma turnstile_in (x : 𝔙 s) (u : Trans j) (d : ℤ) :
    ((turnstile Y H V Q Qt j strict C f).crew u).play (notch (timeMesh Λ) s d) (a₀ s x) =
      a₀ s (sail Y H s j 0 strict u.val u.property (2*d) x) := turns_across Y H V s Q Qt j strict C f u d x

local notation "V₁" => turnstile Y H V Q Qt j strict C f
local notation "R₀" => YM.SelectionAnalysis.joint (traveller Y H V Q Qt j strict C) (procession Y H V Q Qt j strict C f)
/-- Real time and dense-grid transverse JOINT invariants. -/
def RealJoint (x : indoor Y H V Q Qt j strict C f) : Prop :=
    (∀ t : ℝ, (L).edge t x=x) ∧ (∀ (u : Trans j) (t : marks Μ), ((V₁).crew u).play t x=x)
lemma true_joint (x : Ρ) : x ∈ R₀ ↔ RealJoint Y H V Q Qt j strict C f x := by
  rw [mem_joint Λ₀ (travellers Y H V Q Qt j strict C), RealJoint,lamp_fixed ]; constructor
  · intro h
    have ht (i : PinMark j) : (Π (travelAt Y H V Q Qt j strict C i)) x=x := by obtain ⟨i',hi⟩ := tours j i; rw [←hi]; exact h i'
    refine ⟨ride_affordable Y H V Q Qt j strict C f (fun s n => ht (.inl (s,n))), fun u v => ?_⟩
    obtain ⟨i,p,g⟩ := notch_exists Μ v; rw [←g]; exact ht (.inr (u,i,p))
  intro h i; cases e : rolodex j i with
  | inl v => rw [traveller,Function.comp_apply,e]; exact h.1 (θt v.1 v.2)
  | inr v => rw [traveller,Function.comp_apply,e]; exact h.2 v.1 (notch Μ v.2.1 v.2.2)
lemma resides_real : RealJoint Y H V Q Qt j strict C f Ω :=
  (true_joint Y H V Q Qt j strict C f Ω).1 (above_door Y H V Q Qt j strict C f)
theorem one_real (p : Victory Y H V Q Qt strict j C f) {x : Ρ} (q : RealJoint Y H V Q Qt j strict C f x) : ∃ z : ℂ,z • Ω=x :=
  firm_door _ _ _ _ _ _ _ _ _ p x ((true_joint Y H V Q Qt j strict C f x).2 q)

noncomputable def luminousBill (v : indoor Y H V Q Qt j strict C f) : Measure ℝ := roadMeasure (L) v
local notation "μ" v:max => luminousBill Y H V Q Qt j strict C f v
instance billFinite (v : Ρ) : IsFiniteMeasure (μ v) := roadFinite _ _
lemma luminous_char (v : Ρ) (t : ℝ) : inner ℂ v ((L).edge t v) = ∫ r : ℝ, Complex.exp ((r:ℂ)*(t:ℂ)*Complex.I) ∂(μ v) := roadEngine _ _ t
lemma luminous_orbit (v : Ρ) (t : ℂ) (p : 0<t.im) : inner ℂ v ((Π (Z t)) v) = ∫ r : ℝ, Complex.exp ((r:ℂ)*t*Complex.I) ∂(μ v) := by
  rw [selected_air Y H V Q Qt j strict C f p]; exact roadBill _ _ t p
theorem bill_positive (v : Ρ) : ∀ᵐ r : ℝ ∂(μ v), 0 ≤ r := roadLight _ _

end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.ride
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.luminous
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.coats_warm
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.airs
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.ride_continue
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.luminous_orbit
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.ride_ticks
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.one_real
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.turnstile
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.turnstile_in
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.real_rides_trans
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.unselected_air
