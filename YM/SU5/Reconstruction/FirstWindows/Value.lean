import YM.SU5.Reconstruction.FirstWindows.Spaces
/-!
# The linear laws on reconstruction insertions

`osValue` is for the common chosen character. It evaluates also loose tests on
this same character: NO issue at factors of a singlet that aren't invariant on
their own (as long as these are even supported marks). Persistence and gauge frame
under this evaluation will be important. At NO point should its equality with E be
presumed; `mixture` is the relation and we can also compute with continuations
from other sources using exact `displacement`. -/
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
variable {J : Calibration} {q : Bool} (U : Set RSpace)
local notation "D" => Domain Y H G

-- Adapt the two worker interfaces.
noncomputable def asLoose (J : Calibration) : Dome J →ₐ[ℂ] Marks J false where
  toFun x := ⟨x.val,x.property,nofun⟩
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_one' := rfl
  map_zero' := rfl
  commutes' _ := rfl

@[simp] theorem asLoose_val (x : Dome J) : (asLoose J x).val = x.val := rfl

variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)

noncomputable def oneAt (s : ℕ) : Dome (tent Y H) →ₗ[ℂ] ℂ :=
  (χ.toAlgHom.toLinearMap.comp (located Y H V s G.history G.clipped j false C)).comp
    (asLoose K).toLinearMap

local notation "E₁" => oneAt Y H V G j C χ

theorem oneAt_reads (s : ℕ) (f : Dome (tent Y H)) :
    E₁ s f = response Y H V s G.history G.clipped j false C χ (asLoose K f) := rfl

@[simp] theorem oneAt_one (s : ℕ) : E₁ s 1 = 1 := by
  rw [oneAt_reads,Selected.response, map_one,located_one,map_one]

theorem acrossOne (s : ℕ) (j' : Axis) (C' : Arena Y H G.history.circuit j' 0 false) :
    oneAt Y H V G j' C' (displacement Y H V G.history G.clipped j false C χ j' C') s = E₁ s :=
  LinearMap.ext fun f => across_response Y H V s G.history G.clipped j false C χ (asLoose K f) j' C'

theorem oneAt_spread {s t : ℕ} (p : s ≤ t) (x : Dome (tent Y H)) :
    E₁ t (spreadTo Y H G s t x) = E₁ s x := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le p
  rw [oneAt_reads,oneAt_reads,
    show asLoose K (spreadTo Y H G s (s+n) x) =
      upward Y H G.history false (asLoose K x) s n from ?_]
  · exact moves_up ..
  apply Subtype.ext
  simp only [asLoose_val,spreadTo_val, show s+n-s=n by omega]
  rfl

/-- The selected linear evaluation, on ALL test insertions (2). -/
noncomputable def osValue : Domain Y H G false Set.univ →ₗ[ℂ] ℂ :=
  assemble Y H G Set.univ false (fun s => (oneAt Y H V G j C χ s).comp
    ((insideAt Λ l (tent Y H) false Set.univ s).toSubmodule.subtype))
    (fun _ _ p x => oneAt_spread Y H V G j C χ p x.val)

-- qualified form easier later?
local notation "ℒ" => Domain Y H G false Set.univ

@[simp] theorem os_enclose (s : ℕ) (f : insideAt Λ l K false univ s) :
    osValue Y H V G j C χ (enclose Y H G univ false s f) = E₁ s f.val :=
  assemble_enclose ..

/-- For convenience no need to have found exact stage witnesses for `osValue` to be
applied at any site; AND on any ticket height, the value can be computed with its
origin prescription. -/
theorem os_ticket_val (s : ℕ) (x : Dome (tent Y H)) (hx : ticket Y H G s x ∈ ℒ) :
    osValue Y H V G j C χ ⟨ticket Y H G s x,hx⟩ = E₁ s x := by
  have h : x ∈ insideAt Λ l K false univ s := by rw [insideAt_univ_loose]; exact Algebra.mem_top
  exact os_enclose Y H V G j C χ s ⟨x,h⟩

@[simp] theorem os_ticket (s : ℕ) (x : Dome (tent Y H)) :
    osValue Y H V G j C χ ⟨ticket Y H G s x,ticket_loose ..⟩ = E₁ s x :=
  os_ticket_val ..

theorem domain_le_lawDomain : Domain Y H G q U ≤ Domain Y H G false Set.univ := by
  cases q
  · exact domain_mono Y H G (subset_univ _)
  exact le_trans (domain_loose Y H G U) (domain_mono Y H G (subset_univ _))

theorem os_across (j' : Axis) (C' : Arena Y H G.history.circuit j' 0 false) :
    osValue Y H V G j' C' (displacement Y H V G.history G.clipped j false C χ j' C') = osValue Y H V G j C χ := by
  ext1 x
  obtain ⟨j'',f,rfl⟩ := (eventually_enclosed Y H G x).exists
  rw [os_enclose,os_enclose,acrossOne]

section mixture

noncomputable def beforeSelection (s : ℕ) : Dome (tent Y H) →ₗ[ℂ] ℂ where
  toFun f := E s f.val
  map_add' f g := E_add Y H V s ((marque ..).1 f.property) ((marque ..).1 g.property)
  map_smul' c f := E_scale Y H V s ((marque ..).1 f.property) c

-- actual equality using `proceeds`
theorem before_spread {s t : ℕ} (p : s ≤ t) (x : Dome K) :
    beforeSelection Y H V t (spreadTo Y H G s t x)=beforeSelection Y H V s x := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le p
  change E (s+n) _= E s _
  rw [spreadTo_val,show s+n-s=n by omega]
  exact (proceeds Y H G.history.circuit s n ((marque _).1 x.property).paid.choose_spec).2

noncomputable def courseValue : Domain Y H G false univ →ₗ[ℂ] ℂ :=
  assemble Y H G univ false (fun s => (beforeSelection Y H V s).comp
    ((insideAt Λ l (tent Y H) false univ s).toSubmodule.subtype))
    (fun _ _ p x => before_spread Y H V G p x.val)

@[simp] theorem course_enclose (s : ℕ) (f : insideAt Λ l K false univ s) :
    courseValue Y H V G (enclose Y H G univ false s f) = E s f.val.val :=
  assemble_enclose ..

theorem course_ticket_val (s : ℕ) (f : Dome (tent Y H)) (p : ticket Y H G s f ∈ ℒ) :
    courseValue Y H V G ⟨ticket Y H G s f,p⟩ = E s f.val := by
  have h : f ∈ insideAt Λ l K false univ s := by rw [insideAt_univ_loose]; exact Algebra.mem_top
  exact course_enclose Y H V G s ⟨f,h⟩

theorem mixture
    (P : Panel Y H V G.history G.clipped j false C)
    (h : Issued Y H V G.history G.clipped j false C P) (f : ℒ) :
    (∫ x, osValue Y H V G j C (P.character x) f ∂P.μ) = courseValue Y H V G f := by
  obtain ⟨s,x,rfl⟩ := (eventually_enclosed Y H G f).exists
  simp_rw [course_enclose,os_enclose]
  exact survives_check Y H V s G.history G.clipped j false C P h (asLoose K x.val)

end mixture

section choice

variable (R : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
  (c : displayAlgebra Y H V G.history G.clipped j false (R j) →⋆ₐ[ℂ] ℂ)
local notation "r" => PhaseChoice.SameCharacter.resident Y H V G j false (R j) c

theorem audition_here (s : ℕ) : PhaseChoice.audition Y H V G j R r s = oneAt Y H V G j (R j) c s := by
  ext1 f
  exact (PhaseChoice.evaluates Y H V G j R r s (asLoose K f)).trans
    (PhaseChoice.SameCharacter.sameReading Y H V G j false (R j) c s (asLoose K f))

-- gauge on all loose insertions can use the actual frame in `pennant`: dissertation next.
theorem gauge_one (s : ℕ) (x : Dome K) (g : Cover → SU.E) :
    oneAt Y H V G j (R j) c s (pennant K g x) = oneAt Y H V G j (R j) c s x := by
  rw [← audition_here]
  exact PhaseChoice.umbrella ..

end choice
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
