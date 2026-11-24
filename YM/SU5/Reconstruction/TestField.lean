import VerifiedSatinSelectedSectors
import YM.SU5.Reconstruction.SewFlows
import YM.SU5.Reconstruction.Footprint
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6500
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
open Selected PhaseChoice PhaseChoice.SameCharacter PhaseChoice.Theory
open Tapestry Tapestry.Altitude Tapestry.Exhibition

/-!
# The full OS Hilberts sewn from the same Euclidean polynomial algebra

Use full compass `indoor` (spatial representation possibly discontinuous). Do not adopt a
new spatial topology on that data, but explicitly recover this whole Hilbert from the
gauge-invariant local polynomials used to define the interaction. Norm and inner
identification, densities and invariances. This is still Euclidean, including the slabs,
which are required of positive Euclidean width. No claim of Minkowskian locality here.
-/

open Set
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H

section assembly
variable (K' : Calibration)
lemma one_rung_licensed {s : ℕ} {f : Dome (tent Y H)} {wide : Bool} {S : Finset Cover} {U : Set RSpace}
    (h : InTest (tent Y H) wide S false f.val) (t : CovCover (tent Y H) f.val)
    (u : silhouette Λ l s S ⊆ U) :
    pinhole (Dome (tent Y H)) s f ∈ circum Λ l (tent Y H) wide U (Set.Iic s) :=
  oneSlotWell Λ (tent Y H) l wide (handstamp U) (Set.Iic s) s (Set.mem_Iic.mpr (le_refl s)) ⟨S,h,supported_iff.mpr u⟩
    ((enclave_spec K).2 t)

lemma licensed_flank {s : ℕ} {wide : Bool} {U : Set RSpace} {j : Axis}
    {f : Cloud (Dome (tent Y H))} (p : f∈ circum Λ l K wide U (Set.Iic s)) (t : U⊆flank j 0) :
    f∈ Sunlight.cloister Λ l j (PhaseChoice.atZero Λ) (tent Y H) s := stamped Y H j
      (show f∈ circum Λ l K wide U (Set.univ∩ Set.Iic s) from by rwa [Set.univ_inter]) t

lemma field_exists (j : Axis) (s : ℕ) (x : Tower.Field Y H s j 0 true) : ∃ (S : Finset Cover),
    InTest K true S false x.val ∧ silhouette Λ l s S ⊆ flank j 0 := by
  obtain ⟨S,h,t⟩ := (show ∃ S:Finset Cover, InTest K true S false x.val ∧ Tower.region j (meshface (Λ:=Λ) 0 s) (tent Y H).ℓ S from ((purpose_ok ..).1 x.property).1)
  rw [area0] at t
  refine ⟨S,h,supported_iff.mp ?_⟩
  have hp : Tapestry.printedHere Λ l s S (flank j 0) := by
    rw [show (0:ℝ)=markZ Λ s 0 from (by simp [markZ])]; exact brought Λ l s j 0 S t
  change Tapestry.printedHere Λ l s S (handstamp (flank j 0))
  rw [stamp_flank]; exact hp

noncomputable abbrev euclideanHalf (Λ : Preparation) (l : ℕ) (Z : Calibration) (j : Axis) :=
  localEuclidean Λ l Z true (flank j 0)

lemma eventually_cloister (j : Axis) {f : Cloud (Dome (tent Y H))} (p : f∈ euclideanHalf Λ l K j) :
    ∀ᶠ n : ℕ in atTop, f∈ Sunlight.cloister Λ l j (PhaseChoice.atZero Λ) (tent Y H) n := by
  obtain ⟨s,U,h,t,m⟩ := p
  have hx:= licensed_flank Y H m t
  filter_upwards [eventually_ge_atTop s] with n hn using spacing_stamp Y H j hn hx

end assembly

-- elected character (axis d)
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ} {E : ℕ → Family (tent Y H) → ℂ}
  (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H) {L : Rack Λ l} {B : Clay Λ l}
  (D : Exhibition Y H i k I E L B)
variable (j d : Axis) (T : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
local notation "χ₀" => Dome (tent Y H)
local notation "Ĉ" => euclideanHalf Λ l (tent Y H) j
variable (c : (displayAlgebra Y H V G.history G.clipped d false (T d)) →⋆ₐ[ℂ] ℂ)
local notation "χ" => Selected.displacement Y H V G.history G.clipped d false (T d) c j (T j)
local notation "rχ" => resident Y H V G d false (T d) c
local notation "ρ" => indoor Y H V G.history G.clipped j false (T j) χ
local notation "P" => procession Y H V G.history G.clipped j false (T j) χ
local notation "Ω" => doorstep Y H V G.history G.clipped j false (T j) χ
local notation "Ψ" => matchGNS Y H V G j false (T j) d (T d) c
local notation "𝒱" s:max x:max => Selected.arriving Y H V s G.history G.clipped j false (T j) χ x
local notation "Θ" => onDrawing Y H V G D d T rχ
local notation "w" n:max => Sunlight.cloister Λ l j (PhaseChoice.atZero Λ) (tent Y H) n

-- show a test that enters whole lives in physical positive domain. value pinned.
noncomputable def analysisAt {f : Cloud (Dome (tent Y H))} {s : ℕ} (p : f∈ w s) :
    indoor Y H V G.history G.clipped j false (T j) χ :=
  𝒱 s (⟨((vistaFinish Y H s D) f).val, practiced Y H V j D p⟩ : Tower.Field Y H s j 0 false)
local notation "α" => analysisAt Y H V G D j d T c

lemma analyst {f : Cloud χ₀} {s : ℕ} (p : f∈w s) :
    Ψ (α p)= PhaseChoice.declaim Y H V G j D d T rχ p :=
  matchGNS_fields Y H V G j false (T j) d (T d) c s _

lemma analysisAt_eq {f : Cloud χ₀} {s t : ℕ} (p : f∈w s) (q : f∈w t) :
    α p=α q := by
  apply (Ψ).injective
  rw [analyst,analyst]
  rcases le_total s t with ht|ht
  · exact (declaim_all Y H V G j D d T rχ ht p q).symm
  exact declaim_all Y H V G j D d T rχ ht q p

lemma analysisAt_inner {f g : Cloud χ₀} {s : ℕ} (p : f∈ w s) (q : g∈ w s) :
    inner ℂ (α p) (α q)= Θ (Sunlight.oppose Λ j (PhaseChoice.atZero Λ) K f*g) :=
  ((Ψ).inner_map_map (α p) (α q)).symm.trans (by rw [analyst,analyst]; exact cabin_form ..)

private lemma law_plus {x y : Cloud χ₀} {s : ℕ} (p : x∈w s) (q : y∈w s) :
    α ((w s).add_mem p q) = α p+α q := by
  let r := fun (x : Cloud χ₀) (p:x∈w s) => (⟨((vistaFinish Y H s D) x).val,practiced Y H V j D p⟩ : Tower.Field Y H s j 0 false)
  have h : r _ ((w s).add_mem p q) = r _ p+r _ q := Subtype.ext (congrArg (fun x : χ₀=> x.val) (map_add (vistaFinish Y H s D) x y))
  change 𝒱 s (r _ ((w s).add_mem p q))=𝒱 s (r _ p)+𝒱 s (r _ q)
  rw [h,map_add]

private lemma law_scalar {x : Cloud χ₀} {s : ℕ} (p : x∈w s) (z : ℂ) :
    α ((w s).smul_mem p z) = z • α p := by
  let r := fun (x : Cloud χ₀) (p:x∈w s) => (⟨((vistaFinish Y H s D) x).val,practiced Y H V j D p⟩ : Tower.Field Y H s j 0 false)
  have h : r _ ((w s).smul_mem p z) = z • r _ p := Subtype.ext (congrArg (fun x : χ₀=> x.val) (map_smul (vistaFinish Y H s D) z x))
  change 𝒱 s (r _ ((w s).smul_mem p z))=z • 𝒱 s (r _ p)
  rw [h,map_smul]

private noncomputable def shell (x : euclideanHalf Λ l (tent Y H) j) : ℕ := (Eventually.exists (eventually_cloister Y H j x.property)).choose
private lemma inspection (x : euclideanHalf Λ l (tent Y H) j) : x.val ∈ w (shell Y H j x) :=
  (Eventually.exists (eventually_cloister Y H j x.property)).choose_spec
noncomputable def scan : euclideanHalf Λ l (tent Y H) j →ₗ[ℂ] indoor Y H V G.history G.clipped j false (T j) χ where
  toFun x := analysisAt Y H V G D j d T c (inspection Y H j x)
  map_add' x y := by
    obtain ⟨n,h,k⟩ := ((eventually_cloister Y H j x.property).and (eventually_cloister Y H j y.property)).exists
    rw [analysisAt_eq Y H V G D j d T c (inspection Y H j x) h,
      analysisAt_eq Y H V G D j d T c (inspection Y H j y) k]
    exact (analysisAt_eq Y H V G D j d T c _ ((w n).add_mem h k)).trans (law_plus Y H V G D j d T c h k)
  map_smul' z x := by
    let hx := inspection Y H j x
    exact (analysisAt_eq Y H V G D j d T c _ ((w (shell Y H j x)).smul_mem hx z)).trans (law_scalar Y H V G D j d T c hx z)
local notation "Φ" => scan Y H V G D j d T c
lemma scan_works (x : Ĉ) {n : ℕ} (p : x.val∈w n) : Φ x=α p := analysisAt_eq Y H V G D j d T c (inspection Y H j x) p
lemma scan_inner (x y : Ĉ) : inner ℂ (Φ x) (Φ y)= Θ (Sunlight.oppose Λ j (PhaseChoice.atZero Λ) K x.val*y.val) := by
  obtain ⟨n,h,k⟩ := ((eventually_cloister Y H j x.property).and (eventually_cloister Y H j y.property)).exists
  rw [scan_works Y H V G D j d T c x h,scan_works Y H V G D j d T c y k]; exact analysisAt_inner ..

lemma scan_pinhole (s : ℕ) (x : Tower.Field Y H s j 0 true) :
    ∃ y : Ĉ, (∃ z : χ₀,z.val=x.val ∧ y.val=pinhole χ₀ s z) ∧
      Φ y= Selected.bud Y H V s G.history G.clipped j false (T j) χ (Selected.admit Y H s j x) := by
  obtain ⟨S,h,t⟩ := field_exists Y H j s x
  let f : χ₀ := ⟨x.val,field_test Y H s j 0 true x⟩
  have p := one_rung_licensed Y H (f:=f) (U:=silhouette Λ l s S) h
    (((purpose_ok ..).1 x.property).2 rfl) Set.Subset.rfl
  let y : Ĉ := ⟨_, local_in t (local_at (silhouette_compact ..) p)⟩
  let e : y.val∈w s := licensed_flank Y H p t
  refine ⟨y,⟨f,rfl,rfl⟩,?_⟩
  rw [scan_works Y H V G D j d T c y e]; apply congrArg (Selected.bud Y H V s G.history G.clipped j false (T j) χ)
  exact Subtype.ext (congrArg (fun x : χ₀ => x.val) ((vistaDressing Y H D).outcrop (auxiliaryPad K) s f))
lemma scan_unit : Φ 1 = Ω := by
  -- calculate lowest
  rw [scan_works Y H V G D j d T c 1 (show (1 : Cloud χ₀)∈ w 0 from (w 0).one_mem), ← Selected.root Y H V 0]
  apply congrArg (Selected.bud Y H V 0 G.history G.clipped j false (T j) χ)
  exact Subtype.ext (congrArg (fun x : χ₀ => x.val) ((vistaDressing Y H D).crown1 (auxiliaryPad K) 0))

/-- In fact range is the canonical dense domain `stroll`; no loss from restricting to
singlets or working just with rung-supported local (compact) polynomials. -/
lemma scan_range : LinearMap.range (scan Y H V G D j d T c)=
    stroll Y H V G.history G.clipped j false (T j) χ := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change (Φ x)∈ (stroll Y H V G.history G.clipped j false (T j) χ : Set (ρ))
    rw [stroll_exact]
    exact mem_iUnion.mpr ⟨shell Y H j x, _, rfl⟩
  intro x h
  change x∈ (stroll Y H V G.history G.clipped j false (T j) χ : Set (ρ)) at h
  rw [stroll_exact] at h
  obtain ⟨s,y,rfl⟩ := Set.mem_iUnion.mp h
  obtain ⟨b,hb,f,rfl⟩ := artist_fits_slab Y H s j false y
  obtain ⟨S,t,q⟩ := f.property
  obtain ⟨g,t,h⟩ := nearest_bud Y H V s G.history G.clipped j (T j) f hb t q
  have ht := congrArg (arrive Y H V G.history G.clipped j false (T j) χ) h
  rw [← Selected.turns, ← Selected.turns] at ht
  obtain ⟨a,b,w'⟩ := scan_pinhole Y H V G D j d T c (s+1) g.val
  exact ⟨a,w'.trans ht⟩

lemma scan_dense : DenseRange (scan Y H V G D j d T c) := by
  change Dense (LinearMap.range (scan Y H V G D j d T c) : Set (ρ))
  rw [scan_range,stroll_exact]
  exact stroll_dense Y H V G.history G.clipped j false (T j) χ

end YM.CF.Buffered.Afterglow.Tower.Reconstruction
