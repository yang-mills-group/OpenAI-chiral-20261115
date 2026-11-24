import YM.SU5.Selected.Pack.Opportunity

/-! # Choose ONE component with all six slots from the actual law, normal diagnostic. Use
CONSENSUS with Footprint definition `Witness` ie Euclidean-resolution test. Room still
pre spacetime. Need not assume invariance of the choice under any larger group yet. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : ∀ j : Axis, Arena Y H Q.circuit j 0 false)
local notation "A" v:max => Arena Y H Q.circuit v 0 false
local notation "Test" => Vacancy.observable (tent Y H) false
local notation "Lab" => Beacon (tent Y H) false
local notation "m" χ:max => marked Y H V Q Qc j false (C j) χ
open CF.Pannier.Chancel Tapestry Papal SatinVerification
variable {q d w : ℕ} {C₀ Z : ℝ} {Ω : ℝ} (p : Council.Choir Y H q d w C₀ Z Ω)
    {X : Rack Λ l} {R₀ : Clay Λ l} (U : Exhibition Y H i k I E X R₀)
-- probability law
variable (Ψ : Horizon Y H V Q Qc j false (C j)) (hΨ : Law Y H V Q Qc j false (C j) Ψ)
local notation "L" v:max => emigrant Y H V Q Qc j false (C j) Ψ v (C v)
include V Q Qc C p U Ψ hΨ
open Council Survival OS.Ground -- likely ambiguous
local notation "B" => payout d q w
local notation "R" => Aurora Y H V Q j false (C j)
local notation "bM" => camp B
local notation "S" => Sen (camp B) B
local notation "M" s:max => liftCap Y H V Q Qc j false (C j) s
local notation "Π" => (R).orthogonalProjectionOnto
local notation "Ω₀" => seat0 Y H V Q j false (C j)
local notation "W" ℘:max => (Ψ.character ℘)
-- carton bound. variance; real part budget. Need not actually build pair read expectation from θ after orientation.
variable (s:ℕ)
omit U in
lemma variance_light {D:ℝ}(h:0≤D)(F: Test)(x: InTest K true S false F.val)
    (hc: ‖E s (pledgeVolume Y H F.val j)‖≤ D) : Continuous (fun i=> (m (W i)) s F) ∧
    (∫ ℘, ‖1+(m (W ℘)) s F‖^2∂Ψ.μ) ≤ D:=by
  let X:= asField Y H j false s F x (by rw [area0]; exact marches (K) j (from_width K p.small))
  let f:= unity Y H j 0 false s + X
  let F':=combined false (legalOne false) F
  have pΛ : F'=toTest Y H j false s f:=Subtype.ext rfl
  have he i : 1+(m (W i)) s F=(W i) ((M s) F'):= by unfold F' marked; rw [read_add,read_unit]; exact Eq.symm (((W i).map_add' _ _).trans (congrArg (· + (W i) ((M s) F)) ((W i).map_one')))
  refine ⟨(many_accept Y H V Q Qc j false (C j) Ψ hΨ s F).1,?_⟩
  simp_rw [he]
  rw [Localization.Canton.sees_star_sq (X:=basisRoom Y H V Q j false (C j)) Ω₀ Ψ hΨ]
  rw [pΛ]; let X0 := actor Y H s Q.circuit j 0 false (C j) f
  change ‖cap Y H V s Q Qc j false (C j) _ Ω₀‖ ^ 2 ≤ D
  rw [cap_prepares]; refine (pow_le_pow_left₀ (norm_nonneg _) ((R).norm_orthogonalProjectionOnto_apply_le X0) 2).trans ?_
  have hp : inner ℂ X0 X0 = E s (pledgeVolume Y H F.val j) := by unfold X0; rw [stems Y H V,area0]; rfl
  change ‖X0‖^2 ≤ _; rw [← inner_self_eq_norm_sq (𝕜:=ℂ), hp]; exact (Complex.re_le_norm _).trans hc

-- Finite union; sum cap squared varying upper. impose Ω ≥ 10000 for coarse witness (can tune for thresholds). Useful prep chooses larger chamber later.
omit V Q Qc C p U Ψ hΨ
private lemma all_rings {X Y:Type}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]
    [Fintype Y](Q':X→Prop)(he: ∀ᵐ x ∂μ,Q' x)(f:Y→X→ℂ) (h:∀ y: Y,Integrable (fun x=> ‖1+f y x‖^2) μ) (g:ℝ)(h':∀ y,(∫ x, ‖1+f y x‖^2 ∂μ)≤g)
    (v: (Fintype.card Y:ℝ) * g < (1/2)^2): ∃ i, Q' i ∧ ∀ y, ‖1+f y i‖ <1/2 :=by
  classical
  let k(x:X) := ∑ y,‖1+f y x‖^2
  suffices h': ∃ᵐ i ∂μ,k i< (1/2)^2 by
    obtain ⟨i,t,g⟩:= (h'.and_eventually he).exists
    refine ⟨i,g,fun y=>?_⟩
    exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).1 (lt_of_le_of_lt (single_le_sum (f:=fun y=>‖1+f y i‖^2) (fun i _=> sq_nonneg _) (mem_univ _)) t) -- tune sum body
  by_contra! p
  have hp:∀ᵐ i∂μ, (1/2)^2≤ k i:= not_frequently.mp (by simpa using p) |>.mono (fun i t=>le_of_not_gt t) -- tune Lean contraposit
  have hv:(∫ i,k i∂μ)≥(1/2)^2 :=by simpa using integral_mono_ae (integrable_const ((1/2:ℝ)^2)) (integrable_finsetSum univ (fun i _=>h i)) hp
  unfold k at hv; rw [integral_finsetSum] at hv
  · exact ((hv.trans (sum_le_sum (fun y _=> h' y))).trans_lt (by simpa using v)).ne rfl
  exact fun i _=> h i
private lemma credits (x:ℝ) (t:10000 ≤ x) : (Fintype.card SU.Slot :ℝ)*(3*Real.exp (1-x))< (1/2:ℝ)^2:=by
 rw [SU.slots]; have hp: Real.exp (1-x) ≤1/10000:=by
    rw [show (1-x)= -(x-1) from by ring,Real.exp_neg,← one_div]; apply one_div_le_one_div_of_le (by norm_num); linarith [Real.add_one_le_exp (x-1)]
 norm_num at *; linarith
include V Q Qc C p U Ψ hΨ
lemma assigns (u : ℕ) (t:10000 ≤ Ω) (V' : ∀ v i, Birthplace Y H V Q Qc v false (C v) ((L v).character i)) :
    ∃ (F : SU.Slot→Family K) (s c : ℕ) (℘ : Ψ.X), u ≤ s ∧
      extremeJoint Y H Q false (m (Ψ.character ℘)) ∧
      ∀ v : Axis, LoneVac Y H V Q Qc v false (C v) (V' v ℘) ∧
        Law Y H V Q Qc v false (C v) (L v) ∧
        marked Y H V Q Qc v false (C v) ((L v).character ℘)=m (Ψ.character ℘) ∧
        ∀ z: SU.Slot, Witness Y H V Q Qc v (C v) ((L v).character ℘) (F z) z s S (booty bM d q) (cabin c) (1/2) ∧
            ‖1+ phaseRead Y H V Q Qc v (C v) ((L v).character ℘) s (F z)‖ <1/2 := by
  obtain ⟨s,h,hS⟩:= ((glimpses Y H C₀ Z Ω p V j).and (eventually_ge_atTop u)).exists
  choose F hF e t0 v using h
  obtain ⟨c,u⟩:= (fundCabin Λ l s S).exists -- l shadow
  have H'(z): PhysicalTexture Y H (F z) z s S (booty bM d q) (cabin c) (2/precisionAt Λ s) :=by
    have h:= positiveScale Λ s; exact ⟨p.corn.cents bM, stake_centers Y H bM d q w, by positivity, fun i h a=> endpoints_far Λ s (h a), e z,hF z,u⟩
  let u' (z:SU.Slot) (i : Ψ.X):= (m (W i)) s ((H' z).enter Y H false)
  have hp z:= variance_light Y H V Q Qc j C p Ψ hΨ s (show 0 ≤ 3*Real.exp (1-Ω) by positivity) ((H' z).enter Y H false) (FilTest (hF z)).widen (v z)
  haveI:= hΨ.normalized; let P (i : Ψ.X):= ∀ v:Axis,LoneVac Y H V Q Qc v false (C v) (V' v i)
  obtain ⟨x,f,hx⟩:= all_rings P (typical Y H V Q Qc j C Ψ hΨ V' U) u' (fun y=> ((continuous_const (y:=(1:ℂ))|>.add (hp y).1).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) _ (fun y=>(hp y).2) (credits Ω t)
  have he (v:Axis): marked Y H V Q Qc v false (C v) ((L v).character x)=m (Ψ.character x) := funext fun i => funext fun y=> unchanged Y H V Q Qc j false (C j) v (C v) (Ψ.character x) i y
  refine ⟨F,s,c,x,hS,(he j ▸ owner Y H V Q Qc j false (C j) (V' j x) (f j)),fun y=> ⟨f y,Selection.brought Y H V Q Qc j false (C j) Ψ hΨ y (C y),he y,fun z=>?_⟩⟩
  let read:= phaseRead Y H V Q Qc y (C y) ((L y).character x)
  have e1:read s (F z)= u' z x:= (phase_read Y H V Q Qc y (C y) s _ ((H' z).enter Y H false)).trans (congrFun (congrFun (he y) s) _)
  have h2: ‖1+ read s (F z)‖ < 1/2:= e1 ▸ hx z
  refine ⟨witnesses Y H V Q Qc y (C y) (by norm_num) (H' z) (t0 z) ?_,h2⟩
  let h1 :1 - ‖read s (F z)‖ ≤ ‖1+ read s (F z)‖:=by
    have h:= norm_sub_norm_le (1:ℂ) (-(read s (F z))); rwa [norm_one,norm_neg,sub_neg_eq_add] at h
  change 1/2< ‖read s (F z)‖; linarith only [h2,h1]
end YM.CF.Buffered.Afterglow.Tower.Selection
