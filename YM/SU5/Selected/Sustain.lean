import YM.SU5.Selected.Solitaire
/-!
# Quantitative survival after vacuum selection. Same hierarchy from any room / axis.

This is the precise `Parcel` nonfactorization criterion. Recall from
`Centrist` that this is gauge--matter coupling in THAT sense, not the
claims of nontrivial S-matrix or failure of Wick of gauge-fixed fields.
We actually prove the lower bound in a selected **extreme vacuum state**
on the slab algebra, and uniqueness of its invariant vector (up to
multiples) with respect to *all joint vacuum projected directions being
used* (not heat alone and no continuous spatial translation assumed).
Includes as before the reading of an internally multi-site chiral mark at
a fixed level and a fixed physical localization of all its streamed
representatives. See the separate task of multi-observable products on the
selected states, and of relativistic interpretation/continuum.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 480000
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
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "Ω" => seat0 Y H V Q j strict C
local notation "ω" => floorV Y H Q.circuit j 0 strict C
local notation "Λ₀" => traveller Y H V Q Qt j strict C
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
open TopologicalSpace OS.Ground SelectionAnalysis
local notation "Θ₁" => atCharacter Y H V Q Qt j strict C f
local notation "M" => Marks (tent Y H) strict

/-- This computes on the FULL common local marked system (so also all lifts of supported strict
and narrow tests). -/
def response (x : Marks (tent Y H) strict) := f (located Y H V s Q Qt j strict C x)
lemma drive_response {F : observable (tent Y H) strict} (v : Veranda Y H s j strict F) :
    Θ₁ (entrance Y H V s Q Qt j strict C v.fwd v.pos)=response Y H V s Q Qt j strict C f F := by
  rw [setup]; unfold response
  apply congrArg f; apply Subtype.ext; exact (onAny Y H V s Q Qt j strict C v).symm

lemma across_response (x : M) (j' : Axis) (C' : Arena Y H Q.circuit j' 0 strict) :
    response Y H V s Q Qt j' strict C' (displacement Y H V Q Qt j strict C f j' C') x=
    response Y H V s Q Qt j strict C f x :=
  congrArg f (adjust_adj Y H V s Q Qt j' strict C' j C x)

/-- All responses compute on the same tower history D. -/
lemma moves_up (F : observable (tent Y H) strict) (n : ℕ) :
    response Y H V (s+n) Q Qt j strict C f (upward Y H Q strict F s n)=
      response Y H V s Q Qt j strict C f F := by
  unfold response; apply congrArg f; apply Subtype.ext
  have h := cap_level (F:=F) Y H V s Q Qt j strict C (s+n) (Nat.le_add_right s n)
  rw [show s+n-s=n by omega] at h; exact h
lemma survives_check (P : Panel Y H V Q Qt j strict C) (k : Issued Y H V Q Qt j strict C P)
    (x : Marks (tent Y H) strict) : ∫ i, response Y H V s Q Qt j strict C (P.character i) x ∂P.μ = E s x.val :=
   (k.ground (located Y H V s Q Qt j strict C x)).trans
     (inspected (F := (x : observable _ _)) Y H V s Q Qt j strict C)

-- use integral of THE mark not a cluster from shrinking F's. Allow choose from
-- any additionally specified measure-one set later needed. Exact same lower bound
-- as the given law, no epsilon loosened.
lemma sustains_many (P : Panel Y H V Q Qt j strict C) (h : Issued Y H V Q Qt j strict C P)
    (x : Marks (tent Y H) strict) : ∃ᶠ y in ae P.μ,
      ‖E s x.val‖ ≤ ‖response Y H V s Q Qt j strict C (P.character y) x‖ := by
  letI := h.normalized
  intro k
  let c := ‖E s x.val‖; let f y := response Y H V s Q Qt j strict C (P.character y) x; let L y := ‖f y‖
  have hv : ∀ᵐ y ∂P.μ,L y<c := k.mono fun i h => lt_of_not_ge h
  have hs : L ≤ᵐ[P.μ] fun _ => c := hv.mono fun _ h => h.le
  have ht : Continuous f := h.weak _
  have Hx := (ht.norm).integrable_of_hasCompactSupport (μ:=P.μ) (HasCompactSupport.of_compactSpace _)
  have he : (∫ i,L i ∂P.μ) = ∫ _i,c ∂P.μ := by
    refine le_antisymm (integral_mono_ae Hx (integrable_const _) hs) ?_
    change _ ≤ ∫ i,‖f i‖ ∂P.μ
    have hp : c=‖∫ i,f i ∂P.μ‖ := congrArg norm (survives_check Y H V s Q Qt j strict C P h x).symm
    rw [integral_const,probReal_univ,one_smul,hp]
    exact norm_integral_le_integral_norm _
  obtain ⟨r,k',hk⟩ := (((integral_eq_iff_of_ae_le Hx (integrable_const _) hs).1 he).and hv).exists
  exact ne_of_lt hk k'

section purchase
-- Test charge on the wider property (strict=false). Don't say each of
-- the factors alone must be a gauge singlet. The selected responses are on all
-- even arguments and themselves preserve the local gauge comparisons.
variable (C' : Arena Y H Q.circuit j 0 false)
local notation "𝔄'" => displayAlgebra Y H V Q Qt j false C'
local notation "𝔅'" => driveAlgebra Y H V Q Qt j false C'
local notation "X" => observable K true
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
variable {s' d q : ℕ} {z : SU.Slot} {o : Cover} {S : Finset Cover}

def bosonLabel (J : Calibration) (x : observable J true) : observable J false := ⟨x.val, x.property.1,nofun⟩

/-- Keep the quantitative component witness, not just the one-point equality on Ω. -/
structure Survivor (z : SU.Slot) (o : Cover) (q d : ℕ) (S : Finset Cover) (F : observable (tent Y H) true)
    (f : (displayAlgebra Y H V Q Qt j false C') →⋆ₐ[ℂ] ℂ) : Prop where
  link : FixedLink Y H V s Q Qt z o q d S F
  responds : 1/4 ≤ ‖response Y H V s Q Qt j false C' f (bosonLabel K F)‖
  resolves (n : ℕ) (v : Veranda Y H (s+n) j false (bosonLabel K (upward Y H Q true F s n))) :
    atCharacter Y H V Q Qt j false C' f (entrance Y H V (s+n) Q Qt j false C' v.fwd v.pos) =
      response Y H V s Q Qt j false C' f (bosonLabel K F)
  factor_failure : ¬ CF.Pannier.Chancel.Parcel K (Window.family z) (booty o d q)
    S (pigmentReading Y H V s Q Qt j C' f)
  victory : Victory Y H V Q Qt false j C' f

lemma survive {F : observable (tent Y H) true} (h : FixedLink Y H V s Q Qt z o q d S F)
    {f : (displayAlgebra Y H V Q Qt j false C') →⋆ₐ[ℂ] ℂ}
    (k : Victory Y H V Q Qt false j C' f) (x : 1/4 ≤ ‖response Y H V s Q Qt j false C' f (bosonLabel K F)‖) :
    Survivor Y H V s Q Qt j C' z o q d S F f := by
  let B := bosonLabel K F; let G := (booty o d q)
  have hp := (FilTest h.mark_mem).widen
  let E' := pigmentReading Y H V s Q Qt j C' f
  have hx : E' F.val=response Y H V s Q Qt j false C' f B := reads_color Y H V s Q Qt j C' f (show Marks K false from B)
  refine ⟨h,x,fun n v => ?_, fun p => ?_,k⟩
  · rw [drive_response Y H V (s+n) Q Qt j false C' f v]; exact moves_up Y H V s Q Qt j false C' f B n
  have h₀ : E' F.val=0 := (scopedColor Y H V s Q Qt j C' f S).detects h.anchor_inj p h.mark_mem
  have hy : 1/4≤‖E' F.val‖ := hx.symm ▸ x
  rw [h₀,norm_zero] at hy; norm_num at hy

lemma chosen {F : observable (tent Y H) true} (p : FixedLink Y H V s Q Qt z o q d S F)
    {P : Panel Y H V Q Qt j false C'} (h : Issued Y H V Q Qt j false C' P)
    (c : ∀ j, Arena Y H Q.circuit j 0 false) : ∃ᶠ x in ae P.μ,
      Survivor Y H V s Q Qt j C' z o q d S F (P.character x) ∧
        ∀ k:Axis, Survivor Y H V s Q Qt k (c k) z o q d S F
          (displacement Y H V Q Qt j false C' (P.character x) k (c k)) := by
  let B := (show Marks K false from bosonLabel K F)
  apply ((sustains_many Y H V s Q Qt j false C' P h B).and_eventually (full_house Y H V Q Qt j false C' P h c)).mono
  intro x t
  have ht := (p.mixed.trans (show ‖E s F.val‖ ≤ _ from t.1))
  refine ⟨survive Y H V s Q Qt j C' p t.2.1 ht, fun k => survive Y H V s Q Qt k (c k) p (t.2.2 k) ?_⟩
  rw [across_response]; exact ht

/-- Unconditional application. Includes the trajectories/traveller and the responses in one course. -/
theorem selection_on_satin (ε η : ℝ) (hu : 0 < η) :
    ∃ (P : Preparation) (l : ℕ), ε < P.x ∧ P.d ≤ η ∧ P.nominated (VolumeCape.Dream.Nimbus l) ∧
    ∃ (H : Real.exp 1 ≤ P.x) (Y : Course P (VolumeCape.Dream.Nimbus l))
      (a b : ℕ → ℕ) (I : ℕ → Family (tent Y H) → ℕ → ℂ)
      (E : ℕ → Family (tent Y H) → ℂ) (V : Universal Y H a b I E)
      (G : SatinVerification.GroundExtension (i := a) (k := b) (E := E) Y H)
      (q d w s : ℕ) (c : ∀ j:Axis, Arena Y H G.history.circuit j 0 false)
      (A' : Panel Y H V G.history G.clipped 0 false (c 0)),
        Issued Y H V G.history G.clipped 0 false (c 0) A' ∧
        (∀ᵐ x ∂A'.μ, Victory Y H V G.history G.clipped false 0 (c 0) (A'.character x)) ∧
        (∀ F j, ∫ i, response Y H V j G.history G.clipped 0 false (c 0) (A'.character i) F ∂A'.μ = E j F.val) ∧
        ∀ z:SU.Slot, ∀ o : Cover, ∃ F : observable (tent Y H) true,
          ∃ x:A'.X,
            Survivor Y H V s G.history G.clipped 0 (c 0) z o q d (Sen o (payout d q w)) F (A'.character x) ∧
            ∀ k : Axis, Survivor Y H V s G.history G.clipped k (c k) z o q d (Sen o (payout d q w)) F
              (displacement Y H V G.history G.clipped 0 false (c 0) (A'.character x) k (c k)) := by
  obtain ⟨P,l,u,k,W,H,Y,a,b,I,E,V,G,q,d,w,s,h⟩ := first_step ε η hu
  let c (i:Axis) := Classical.choice (voyage_H Y H V G.history.circuit i 0 false)
  obtain ⟨A',g⟩ := display_receives Y H V G.history G.clipped 0 false (c 0)
  letI := g.normalized; refine ⟨P,l,u,k,W,H,Y,a,b,I,E,V,G,q,d,w,s,c,A',g,(full_house Y H V G.history G.clipped 0 false (c 0) A' g c).mono fun _ u => u.1, fun F j=> survives_check Y H V j G.history G.clipped 0 false (c 0) A' g F,fun z o => ?_⟩
  obtain ⟨F,w,_⟩ := h z o
  exact ⟨F,(chosen Y H V s G.history G.clipped 0 (c 0) w g c).exists⟩
end purchase
end YM.CF.Buffered.Afterglow.Tower.Selected
#check @YM.CF.Buffered.Afterglow.Tower.Selected.selection_on_satin
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.selection_on_satin
