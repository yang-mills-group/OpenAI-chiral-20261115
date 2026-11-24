import YM.SU5.Reconstruction.FirstWindows.Mirror
/-!
# One spacetime test-field domain, axes as different Gram structures

Occupy all axis OS spaces for **this character**, see the selected functional on
local polynomials. Account for the real units, the openness of the test-domain
positive-time support, and our single-motion registry. This is a common test space
BEFORE passing to an inter-axis real time Hilbert construction. The remaining
obligations for that passage should concern THIS law. -/
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
open SlabMark MeshClock
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G

variable (j : Axis)
local notation "V₊" => flank j 0
local notation "V₋" => (mirrorE j 0 '' (flank j 0))

/-- Positive **closed** half-space -- the subsequent shift into its interior
or to any positive gap doesn't require new Hilbert data. -/
theorem positive_today (s : ℕ) (x : Dome K) :
    x ∈ insideAt Λ l K q (flank j 0) s ↔ x.val ∈ purpose K (meshface (Λ:=Λ) 0 s) j q := by
  rw [mem_insideAt,purpose_ok,area0]; change _ ↔ (∃ S, InTest K true S false x.val ∧ Tower.region j 0 (K).ℓ S) ∧ _
  have he : PhaseChoice.handstamp (flank j 0)=flank j 0 := PhaseChoice.stamp_flank j
  suffices g : ∀ S : Finset Cover, PhaseChoice.SupportedPhysically Λ l s S V₊ ↔ Tower.region j 0 (K).ℓ S by
    simp_rw [g]
  intro S
  change Tapestry.printedHere Λ l s S (PhaseChoice.handstamp (flank j 0)) ↔ _
  rw [he]
  have e : markZ Λ s 0=0 := by simp [markZ]
  constructor
  · intro h; apply Tapestry.returns Λ l s j 0 S; rw [e]; exact h
  intro h; have h := brought Λ l s j 0 S h; rw [e] at h; exact h

local notation "Kp" q:max s:max=> insideAt Λ l (tent Y H) q (flank j 0) s

noncomputable def asField (q : Bool) (s : ℕ) :
    (insideAt Λ l (tent Y H) q (flank j 0) s) →ₗ[ℂ] Tower.Field Y H s j 0 q where
  toFun x := ⟨x.val.val,(positive_today Y H j s x.val).1 x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def fromField (s : ℕ) (x : Tower.Field Y H s j 0 q) : insideAt Λ l (tent Y H) q (flank j 0) s := by
  let f : Dome K := ⟨x.val, field_test Y H s j 0 q x⟩
  exact ⟨f,(positive_today Y H j s f).2 x.property⟩

@[simp] theorem asField_val (s : ℕ) (x : insideAt Λ l K q V₊ s) :
    (asField Y H j q s x).val=x.val.val := rfl
@[simp] theorem fromField_val (s : ℕ) (x : Tower.Field Y H s j 0 q) :
    (fromField Y H j s x).val.val=x.val := rfl
@[simp] theorem from_asField (s : ℕ) (x : insideAt Λ l K q V₊ s) :
    fromField Y H j s (asField Y H j q s x)=x := rfl
@[simp] theorem as_fromField (s : ℕ) (x : Tower.Field Y H s j 0 q) :
    asField Y H j q s (fromField Y H j s x) = x := rfl

-- Reflected pairing works even with touching shields. Thus the ambient
-- formula (which DOES NOT always work across overlap) suffices here too.
lemma paired_today (s : ℕ) (x y : insideAt Λ l K q (flank j 0) s) :
    let f := aureole K j 0 x.val
    ticket Y H G s (f*y.val)=flipMark j K (ticket Y H G s x.val) * ticket Y H G s y.val := by
  intro f
  rw [flipMark_ticket]
  obtain ⟨S,t,h⟩ := (((purpose_ok ..).1 ((positive_today Y H j s x.val).1 x.property)).1 : ∃ _ , _)
  obtain ⟨T,u,v⟩ := (((purpose_ok ..).1 ((positive_today Y H j s y.val).1 y.property)).1 : ∃ _,_)
  rw [area0] at h v
  refine Filter.Germ.coe_eq.mpr <| Eventually.of_forall fun n => ?_
  exact Subtype.ext <| woven_product Y H G.history.circuit s (n-s) (axial K j 0 t) u (mirror_detached _ _ h v)

lemma paired_forever (f g : Sky (tent Y H)) (p : f ∈ D q V₊) (v : g ∈ D q V₊) :
    flipMark j K f*g ∈ D q Set.univ := by
  obtain ⟨s,⟨a,t,rfl⟩,x,h,rfl⟩ := (((domain_eventually Y H G).1 p).and ((domain_eventually Y H G).1 v)).exists
  rw [← show ticket Y H G s (aureole K j 0 a*x)=_ from paired_today Y H G j s ⟨a,t⟩ ⟨x,h⟩]
  exact ticket_mem Y H G ((insideAt Λ l K q _ s).mul_mem
    (insideAt_mono (Set.subset_univ _) (mirror_inside Y H j a s t)) (insideAt_mono (Set.subset_univ _) h))

-- use the loose Hilbert of the statement; strict determining fields pay its whole Gram.
variable (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "I₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "κ₀" t:max x:max=> bud Y H V t G.history G.clipped j false C χ x
local notation "I₁"=> fort Y H V G.history G.clipped j false C χ
local notation "Ψ" => osValue Y H V G j C χ

/-- Use with all heights of *this* polynomial/component theory in positive time. -/
noncomputable def OSvector : Domain Y H G false (flank j 0) →ₗ[ℂ] I₀ :=
  assemble Y H G (flank j 0) false (fun s => (arriving Y H V s G.history G.clipped j false C χ).comp
    (asField Y H j false s)) (fun s t p x => by
      let f := asField Y H j false s x
      have h : asField Y H j false t (refineInside Y H G (flank j 0) false s t p x) =
        Raise Y H G.history.circuit j 0 false s t p f := Subtype.ext rfl
      change κ₀ t (asField Y H j false t _) = κ₀ s f
      rw [h]; exact flourishes ..)

local notation "λp" => OSvector Y H V G j C χ
noncomputable def physicalKet : Domain Y H G true (flank j 0) →ₗ[ℂ] I₀ :=
  (OSvector Y H V G j C χ).comp (Submodule.inclusion (domain_loose Y H G (flank j 0)))

@[simp] theorem OSvector_enclose (s : ℕ) (x : insideAt Λ l K false (flank j 0) s) :
    λp (enclose Y H G V₊ false s x)= κ₀ s (asField Y H j false s x) := assemble_enclose ..

lemma field_ticket (s : ℕ) (x : Dome K) (h : x ∈ insideAt Λ l K false (flank j 0) s)
    (p : ticket Y H G s x ∈ D false (flank j 0)) :
    λp ⟨ticket Y H G s x,p⟩=κ₀ s (asField Y H j false s ⟨x,h⟩) := OSvector_enclose Y H V G j C χ s ⟨x,h⟩

lemma physical_enclose (s : ℕ) (x : insideAt Λ l K true (flank j 0) s) :
    physicalKet Y H V G j C χ (enclose Y H G V₊ true s x) =
      bud Y H V s G.history G.clipped j false C χ (admit Y H s j (asField Y H j true s x)) := by
  let f : insideAt Λ l K false (flank j 0) s := ⟨x.val, insideAt_loose s x.property⟩
  exact OSvector_enclose Y H V G j C χ s f

/-- Pair any two insertions in resolution geometry, without a common
chosen height. Their OS inner product IS selected reading. This could not be
asserted yet for their canonical projections to the spatially continuous part. -/
theorem registered_pair (x y : Domain Y H G false (flank j 0)) :
    inner ℂ (λp x) (λp y)= Ψ
      ⟨flipMark j (tent Y H) x.val * y.val, paired_forever Y H G j x.val y.val x.property y.property⟩ := by
  obtain ⟨s,⟨x,rfl⟩,y,rfl⟩ := ((eventually_enclosed Y H G x).and (eventually_enclosed Y H G y)).exists
  let f := aureole K j 0 x.val * y.val
  have h : flipMark j K (ticket Y H G s x.val)*ticket Y H G s y.val=ticket Y H G s f := (paired_today ..).symm
  have he : ∀ (v : flipMark j K (enclose Y H G V₊ false s x).val * (enclose Y H G V₊ false s y).val ∈ D false univ),
    (⟨_,v⟩ : D false univ) = ⟨ticket Y H G s f,ticket_loose ..⟩ := fun _ => Subtype.ext h
  rw [he,os_ticket_val,OSvector_enclose,OSvector_enclose,earns]; exact Eq.refl _

lemma expectation (x : Domain Y H G false (flank j 0)) :
    inner ℂ (doorstep Y H V G.history G.clipped j false C χ) (λp x)=
      Ψ ⟨x.val, domain_le_lawDomain Y H G V₊ x.property⟩ := by
  obtain ⟨s,f,rfl⟩ := (eventually_enclosed Y H G x).exists
  rw [OSvector_enclose]
  change _ = Ψ ⟨ticket Y H G s f.val,ticket_loose ..⟩
  rw [os_ticket_val]; exact call Y H V s G.history G.clipped j false C χ (asField Y H j false s f)

@[simp] lemma vacuum_ticket : λp ⟨1,domain_one ..⟩=doorstep Y H V G.history G.clipped j false C χ := by
  rw [show (⟨1,domain_one ..⟩ : D false V₊) = enclose Y H G V₊ false 0 1 from Subtype.ext (ticket_one Y H G 0).symm,
    OSvector_enclose]; exact Selected.root Y H V 0 G.history G.clipped j false C χ

theorem physical_dense : DenseRange (physicalKet Y H V G j C χ) := by
  apply (reserved_actor Y H V G.history G.clipped j C χ).mono
  intro x p; obtain ⟨s,h⟩ := mem_iUnion.mp p; obtain ⟨f,rfl⟩ := h
  exact ⟨enclose Y H G V₊ true s (fromField Y H j s f), physical_enclose Y H V G j C χ s (fromField Y H j s f)⟩

noncomputable def fullDomain : Submodule ℂ (indoor Y H V G.history G.clipped j false C χ) :=
  LinearMap.range (physicalKet Y H V G j C χ)

theorem fullDomain_dense : Dense (fullDomain Y H V G j C χ : Set (indoor Y H V G.history G.clipped j false C χ)) :=
  physical_dense Y H V G j C χ

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
