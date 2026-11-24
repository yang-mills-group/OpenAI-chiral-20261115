import YM.SU5.Reconstruction.FirstWindows.Value
/-!
# Polynomial semantics for reconstruction

What about contact/overlap observables? None are lost. The ordinary commutative
resolution polynomial algebra (even chiral link-matter), evaluated by
`Appointment` in this character, maps LINEARLY into our spacetime test domain.
Only when supports are disjoint is it also required to map multiplication to
the operation there. It's a surjection even on each physical and gauge invariant
local space. Each insertion arises from an actual supported polynomial and
reading those in the local algebra (product included) can be implemented by
finishing the whole query, not via continuing separate coincident legs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 300000
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Tapestry.Altitude Tapestry.Exhibition
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)

local notation "F" => vistaDressing Y H Z
local notation "T" s:max => vistaFinish Y H s Z
local notation "σ₀" => Domain Y H G
local notation "θ" => PhaseChoice.handstamp

/-- The *local polynomial algebra*, including contact products, converted to
matter units for spacetime locations (no constraint on set of allowed stages).
On the physical system we require full gauge invariance, same as `circum`.
Both use joint-link (& even matter) support. -/
def questions (Λ : Preparation) (l : ℕ) (J : Calibration) (singlets : Bool)
    (U : Set RSpace) : Subalgebra ℂ (Altitude.Cloud (Dome J)) :=
  if singlets then PhaseChoice.circum Λ l J true U univ else jetty Λ l J true (θ U) univ

theorem questions_loose : questions Λ l J true U ≤ questions Λ l J false U := by
  simp only [questions, ↓reduceIte, Bool.false_eq_true]
  exact fun _ h => ((well_spec Λ J l true (θ U) Set.univ).1 h).1

theorem questions_mono (p : U ⊆ W) : questions Λ l J q U ≤ questions Λ l J q W := by
  cases q
  · exact admits Λ l J true _ _ _ _ Set.Subset.rfl (Set.preimage_mono p)
  exact wellGrows Λ J l true (θ U) (θ W) univ univ Set.Subset.rfl (Set.preimage_mono p)

theorem questions_top_loose : questions Λ l J false univ = FiniteGaugeDataPoly J := by
  simp only [questions,Bool.false_eq_true,↓reduceIte,PhaseChoice.handstamp, Set.preimage_univ]
  exact jetty_awork Λ l J

theorem questions_polynomials : questions Λ l J q U ≤ FiniteGaugeDataPoly J := by
  cases q
  · exact jets ..
  exact wellPolynomial Λ J l true (θ U) univ

local notation "vₜ" U:max t:max => jetty Λ l (tent Y H) true (PhaseChoice.handstamp U) ((Set.univ : Set ℕ)∩ Set.Iic t)
-- careful notation U binder.
theorem questions_price {f : Cloud (Dome K)} (p : f ∈ questions Λ l K q U) :
    ∀ᶠ t in atTop, f ∈ vₜ U t := by
  have h : f ∈ jetty Λ l K true (θ U) Set.univ := by
    cases q
    · exact p
    exact questions_loose p
  obtain ⟨n,h⟩ := entrusted Λ l K true (θ U) Set.univ h
  refine (eventually_ge_atTop n).mono fun x e => ?_
  exact admits Λ l K true (θ U) (θ U) (Set.univ ∩ Set.Iic n) (Set.univ ∩ Set.Iic x) (fun i ⟨u,v⟩ => ⟨u,le_trans v e⟩) Set.Subset.rfl h

include V
lemma finish_rise {s t : ℕ} (p : s ≤ t) {f : Cloud (Dome (tent Y H))}
    (h : f ∈ shorter (Dome K) s) : (T t) f = spreadTo Y H G s t ((T s) f) := by
  induction t,p using Nat.le_induction with
  | base => symm; exact spreadTo_refl ..
  | succ t p ih =>
    have e : (T (t+1)) f = Exhibition.liftD Y H t Z ((T t) f) :=
      Decking.joins F t f (auxiliaryPad K) (Altitude.climbs (Dome K) p h)
    rw [e]; apply Subtype.ext
    rw [PhaseChoice.lifts_here Y H V G,ih,spreadTo_val,spreadTo_val,show t+1-s=t-s+1 by omega,
      stream_step,show s+(t-s)=t by omega]

theorem finish_agrees {s t : ℕ} {f : Cloud (Dome K)} (p : f ∈ shorter (Dome K) s)
    (q : f ∈ shorter (Dome K) t) :
    ticket Y H G s ((T s) f)=ticket Y H G t ((T t) f) := by
  rcases le_total s t with e | e
  · rw [finish_rise Y H V G Z e p, ticket_spread Y H G e]
  rw [finish_rise Y H V G Z e q,ticket_spread Y H G e]

omit V
/-- A single interpretation (independent of target region). Use the ordinary
algebra `FiniteGaugeDataPoly`. -/
noncomputable def realize : FiniteGaugeDataPoly (tent Y H) →ₗ[ℂ] Sky (tent Y H) where
  toFun f := ↑(fun t => (T t) f.val)
  map_add' _ _ := Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun t => map_add (T t) _ _
  map_smul' _ _ := Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun t => map_smul (T t) _ _

include V
theorem realize_ticket (s : ℕ) (f : FiniteGaugeDataPoly (tent Y H)) (h : f.val ∈ shorter (Dome K) s) :
    realize Y H Z f = ticket Y H G s ((T s) f.val) := by
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  exact finish_rise Y H V G Z ht h

omit V in
lemma finish_inside {s : ℕ} {f : Cloud (Dome K)}
    (p : f ∈ vₜ U s) (q' : f ∈ questions Λ l K q U) : (T s) f ∈ insideAt Λ l K q U s := by
  have e : (T s) f ∈ keep Λ l s K true (θ U) := crownShelter Λ l s F (auxiliaryPad K) (fun i x=>rfl)
    (θ U) (fun i g h=>roofline Λ l i true (θ U) Z h) p
  cases q
  · exact ⟨e,Algebra.mem_top⟩
  exact ⟨e,Z.finishCoherent Y H s f (show f∈ well Λ K l true (θ U) univ from q') (jettyBan Λ l K true (θ U) univ s p)⟩

theorem realize_inside {f : FiniteGaugeDataPoly (tent Y H)} (p : f.val ∈ questions Λ l K q U) :
    realize Y H Z f ∈ D q U := by
  obtain ⟨t,h⟩ := (questions_price Y H p).exists
  rw [realize_ticket Y H V G Z t f (jettyBan Λ l K true (θ U) univ t h)]
  exact ticket_mem Y H G (finish_inside Y H Z h p)

include G in
/-- Separated multiplication *between regions* even if built internally from
families that are not just simple pinholes, which might need to launch at very
different resolutions. -/
theorem realize_separated {x y : FiniteGaugeDataPoly (tent Y H)}
    {a b : Bool} (p : x.val ∈ questions Λ l K a U) (q : y.val ∈ questions Λ l K b W)
    (d : Disjoint U W) : realize Y H Z (x*y) = realize Y H Z x * realize Y H Z y := by
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [questions_price Y H p, questions_price Y H q] with t v w
  exact PhaseChoice.depart_pair Y H V G Z v w (Disjoint.preimage _ d)

omit V in
theorem one_question (s : ℕ) (x : Dome K) (p : x ∈ insideAt Λ l K q U s) :
    pinhole (Dome K) s x ∈ questions Λ l K q U := by
  have e : x ∈ keep Λ l s K true (θ U) := inf_le_left (α:=Subalgebra ℂ (Dome K)) p
  cases q
  · exact pokes Set.univ _ (Set.mem_univ s) e
  exact oneSlotWell Λ K l true (θ U) univ s (Set.mem_univ s) e (show x ∈ enclave K from (p : _∧_).2)

theorem one_realized (s : ℕ) (x : Dome K)
    (p : pinhole (Dome K) s x ∈ FiniteGaugeDataPoly (tent Y H)) :
    realize Y H Z ⟨pinhole (Dome K) s x,p⟩ = ticket Y H G s x := by
  rw [realize_ticket Y H V G Z s _ (Altitude.short_pinhole s x), vistaFinish, Decking.outcrop]
  rfl

/-- Surjection even with specified region. No *point* field claims. -/
theorem realize_covers (q : Bool) (U : Set RSpace) :
    realize Y H Z '' {x | x.val ∈ questions Λ l (tent Y H) q U} = (Domain Y H G q U : Set (Sky K)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x,h,rfl⟩; exact realize_inside Y H V G Z h
  rintro _ ⟨s,f,p,rfl⟩
  have h := one_question Y H s f p
  exact ⟨⟨_,questions_polynomials h⟩,h,one_realized Y H V G Z s f _⟩

variable (j : Axis) (R : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (R j) →⋆ₐ[ℂ] ℂ)
local notation "rJ" => PhaseChoice.SameCharacter.resident Y H V G j false (R j) χ

theorem realize_read (f : FiniteGaugeDataPoly (tent Y H)) (p : realize Y H Z f ∈ σ₀ false univ) :
    osValue Y H V G j (R j) χ ⟨realize Y H Z f,p⟩ = PhaseChoice.onDrawing Y H V G Z j R rJ f.val ∧
    courseValue Y H V G ⟨realize Y H Z f,p⟩ = vistaTake Y H Z f.val := by
  obtain ⟨s,t⟩ := curve.mp f.property
  have h : (⟨realize Y H Z f,p⟩ : σ₀ false univ)=⟨ticket Y H G s ((T s) f.val), ticket_loose ..⟩ :=
    Subtype.ext (realize_ticket Y H V G Z s f t)
  constructor
  · rw [h,os_ticket_val,← audition_here Y H V G j R χ s]
    exact (PhaseChoice.drawAt Y H V G Z j R rJ t).symm
  rw [h,course_ticket_val]
  exact (Exhibition.vistaCall Y H s _ Z t).symm

-- note `p` paid automatically
theorem always_realizes (f : FiniteGaugeDataPoly (tent Y H)) : realize Y H Z f ∈ Domain Y H G false Set.univ :=
  realize_inside Y H V G Z ((questions_top_loose).symm ▸ f.property)

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
