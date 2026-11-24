import YM.SU5.Reconstruct.Regions
/-!
# Common gauge-invariant Euclidean domain at the elected character

Positive input marks are test-fields at resolution heights. Define their
placement into the full OS representations (at the SAME character from
any axis), using the polynomial prescription itself. Everything has a strict
singlet interpretation and a bounded physical realChartFootprint (Regions.pressured). Prove computation
of the full form on all these positive polynomials. We show elsewhere that
those with room even in
the OPEN halfspace are dense in the selected Hilbert spaces. Do not assert
that their projections to the spatially-continuous part have this same Gram!
More estimates needed for that. One-point readings already survive in those
projections. This is a Euclidean test domain, not asserting either pointlike
fields or a *-homomorphism on those spaces for contact products.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 270000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Tapestry Tapestry.Altitude PhaseChoice
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
open Tower.Selected Set MeshClock Tapestry.Exhibition
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  {L:Rack Λ l}{B:Clay Λ l}{T:ℕ→ℕ→Tariff}{t:ℕ→Tariff}(D:Fashion Y H i k I E L B T t)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "Dₚ" => D.toExhibition
local notation "V" => D.univ_
local notation "Q" => G.history
local notation "Qt" => G.clipped
local notation "χ" => Dome (tent Y H)
local notation "O" => Altitude.Cloud (Dome (tent Y H))
local notation "P₀" s:max => vistaFinish Y H s (Dₚ)
variable (C : ∀ j:Axis, Tower.Arena Y H G.history.circuit j 0 false)
local notation "𝔇" i:max => displayAlgebra Y H V Q Qt i false (C i)
variable (c: (displayAlgebra Y H D.univ_ G.history G.clipped 0 false (C 0)) →⋆ₐ[ℂ] ℂ)
-- beam orientations at the same Sch functional
noncomputable abbrev inAxis (j:Axis) := displacement Y H V Q Qt 0 false (C 0) c j (C j)
noncomputable abbrev entire (j: Axis) := indoor Y H V Q Qt j false (C j) (inAxis Y H D G C c j)
noncomputable abbrev continuousH (j:Axis):= fort Y H V Q Qt j false (C j) (inAxis Y H D G C c j)

variable (j:Axis)
local notation "U₀" => flank j 0
local notation "u₀" => PhaseChoice.atZero Λ
local notation "𝜔" => (PhaseChoice.atZero Λ).oppose Λ j (tent Y H)
local notation "S★" => sch Y H D G C c
local notation "qA" i:max => inAxis Y H D G C c i
local notation "H₀" => entire Y H D G C c j
local notation "HC" => continuousH Y H D G C c j
local notation "β" s:max => bud Y H V s Q Qt j false (C j) (qA j)
local notation "Π₀" s:max => land Y H V s Q Qt j false (C j) (qA j)
local notation "Ω" => doorstep Y H V Q Qt j false (C j) (qA j)
local notation "Ωc" => vocation Y H V Q Qt j false (C j) (qA j)
local notation "η₀" => purpose K (0:ℤ) j true
abbrev upperRoom (j:Axis) := {u:RSpace|0 < u j}
lemma upper_in : upperRoom j⊆ flank j 0:=fun x v=>(show 0<x j from v).le

variable {s:ℕ}
lemma arrival {x:Altitude.Cloud (Dome K)} (p:x ∈ PolAt Y H s (flank j 0)) : ((P₀ s) x).val∈purpose K (meshface (Λ:=Λ) 0 s) j false:=
   PhaseChoice.practiced Y H V j (Dₚ) (stamped Y H j p Set.Subset.rfl)
lemma arrival_phys {x:Altitude.Cloud (Dome K)} (p:x ∈ PolAt Y H s (flank j 0)) : ((P₀ s) x).val∈purpose K (meshface (Λ:=Λ) 0 s) j true:= by
  apply (purpose_ok ..).2
  refine ⟨((purpose_ok ..).1 (arrival Y H D j p)).1,fun _=>?_⟩
  exact (enclave_spec K).1 ((Dₚ).finishCoherent Y H s x p (inside_budget Y H p))

/-- Full Gram fields built at this axis (certified budgets even with
coincident factors). -/
def preparePoly (s:ℕ) : PolAt Y H s (flank j 0) →ₗ[ℂ] Tower.Field Y H s j 0 true where
  toFun x:=⟨((P₀ s) x.val).val,arrival_phys Y H D j x.property⟩
  map_add' x y:=Subtype.ext (congrArg (fun z:Dome K=> z.val) (map_add (P₀ s) x.val y.val))
  map_smul' a x:=Subtype.ext (congrArg (fun z:Dome K=> z.val) (map_smul (P₀ s) a x.val))
def widenInput (s:ℕ) : Tower.Field Y H s j 0 true →ₗ[ℂ] Tower.Field Y H s j 0 false where
  toFun := admit Y H s j
  map_add' _ _:=Subtype.ext rfl
  map_smul' _ _:=Subtype.ext rfl

def locatePoly (s:ℕ) : PolAt Y H s (flank j 0) →ₗ[ℂ] entire Y H D G C c j :=
    (arriving Y H V s Q Qt j false (C j) (qA j)).comp ((widenInput Y H j s).comp (preparePoly Y H D j s))
local notation "read" s:max p:max => locatePoly Y H D G C c j s p
lemma locate_step {x:O} (u:x ∈ PolAt Y H s (flank j 0)) (v:x ∈ PolAt Y H (s+1) U₀) :
    (read (s+1) ⟨x,v⟩)=(read s ⟨x,u⟩):=by
  let t : Tower.Field Y H s j 0 false:=⟨_,arrival Y H D j u⟩
  let t' : Tower.Field Y H (s+1) j 0 false:=⟨_,arrival Y H D j v⟩
  change (β (s+1)) t'=(β s) t
  have h : t'=Raise Y H G.history.circuit j 0 false s (s+1) (by omega) t := by
    have ht: (P₀ (s+1)) x= Exhibition.liftD Y H s D.toExhibition ((P₀ s) x):=
        Decking.joins _ s x _ (inside_budget Y H u)
    apply Subtype.ext; change ((P₀ (s+1)) x).val=stream _ _ _ s (s+1-s) _; rw [ht,lifts_here Y H V,show s+1-s=1 by omega]; rfl
  rw [h,flourishes]
lemma located_higher {r:ℕ}{x:O} (h:s ≤ r)(p:x∈ PolAt Y H s U₀)(q:x∈PolAt Y H r U₀):
    (read r ⟨x,q⟩)=(read s ⟨x,p⟩):= by
  induction r,h using Nat.le_induction with
  | base=> rfl
  | succ r v ih=> exact (locate_step Y H D G C c j (polAt_up Y H v p) q).trans (ih _)

lemma poly_gram (x y:PolAt Y H s (flank j 0)) :
    inner ℂ (locatePoly Y H D G C c j s x) (locatePoly Y H D G C c j s y) =
      (S★) (𝜔 x.val * y.val):=by
  have a := stamped Y H j x.property Set.Subset.rfl
  have b := stamped Y H j y.property Set.Subset.rfl
  have he:= sch_axes Y H D G C c j s ((shorter χ s).mul_mem ((u₀).respectsCut Λ l j K a) (inside_budget Y H y.property))
  rw [he]; change inner ℂ ((β s) _) ((β s) _)=_
  rw [earns]; apply congrArg (fun x=> response Y H V s Q Qt j false (C j) (qA j) x); apply Subtype.ext
  change _ = ((P₀ s) ((𝜔) _*_)).val
  unfold vistaFinish; rw [reflectionHat Λ l j u₀ s _ _ ((Dₚ).glass Y H j u₀) s.zero_le a b, atZ]; rfl

lemma poly_mean (x:PolAt Y H s U₀) : inner ℂ Ω (read s x)=(S★) x.val:=by
  rw [sch_axes Y H D G C c j s (inside_budget Y H x.property)]
  exact call ..
lemma transmitted (x:PolAt Y H s U₀) :
    inner ℂ Ωc ((Π₀ s) (⟨_,arrival Y H D j x.property⟩))=(S★) x.val:=by
  rw [sch_axes Y H D G C c j s (inside_budget Y H x.property)]
  exact land_call ..

-- `contact`: don't do this for all P products! identify precisely.
lemma dual_measure (s:ℕ)(u v:Set RSpace)(d:Disjoint u v)
    (x:PolAt Y H s u)(y:PolAt Y H s v) :
    S★ (x.val*y.val)=response Y H V s Q Qt j false (C j) (qA j)
      ((fieldArg Y H ((P₀ s) x.val)) * fieldArg Y H ((P₀ s) y.val)) := by
  have h₁:= (well_spec ..).mp x.property
  have h₂:= (well_spec ..).mp y.property
  rw [sch_axes Y H D G C c j s ((shorter χ s).mul_mem (inside_budget Y H x.property) (inside_budget Y H y.property)), depart_pair Y H V G D.toExhibition h₁.1 h₂.1 (Disjoint.preimage _ d)]; rfl
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
