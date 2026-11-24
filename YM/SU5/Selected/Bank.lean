import YM.SU5.Selected.Bary
import YM.SU5.Selected.Equate
import YM.SU5.Selected.CanCount

/-!
# The actual component field (Euclidean resolution)

Specialize the ergodic criterion to Satin on **one** Coherent law, across
all directions. Use actual representation on Arena determined by that
`Universal`. No transfer to an older candidate space. Keep all support and
all level budgets from this extension. No claim here of measurability of
evaluation on any other kind of mark.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Theory Set MeshClock
local notation "Sq"=>squeeze Y H V G j strict C
local notation "A₀"=>catalog Y H V G j strict C
local notation "St"=>stationC Y H V G j strict C

noncomputable def compress : (St) →ₗ[ℂ] (A₀) where
  toFun x:= ⟨Sq x.val,closes_caps Y H V G j strict C x.property⟩
  map_add' x y := Subtype.ext (map_add Sq x.val y.val)
  map_smul' z x := Subtype.ext (map_smul Sq z x.val)
noncomputable def heatOp (r:ℝ≥0) : St := ⟨advance Y H V G.history.circuit j 0 strict C r,
  station_heat Y H V G j strict C r⟩
local notation "Q"=>heatOp Y H V G j strict C
noncomputable def shiftOp(a:Trans j)(x:marks (timeMesh Λ)) : St :=
  ⟨shift Y H V G j strict C a x,station_U Y H V G j strict C (shifts_activate Y H V G j strict C a x)⟩
local notation "U"=>shiftOp Y H V G j strict C
noncomputable def boxElement (s u:ℕ)(x:Entry Y H s j strict u)(p:0<u) : St :=
  ⟨(B s x p),station_box Y H V G j strict C (boxes_activate Y H V G j strict C s u x p)⟩
local notation "cP"=>compress Y H V G j strict C
noncomputable def approach : Set (St) := Set.range (Q) ∪ Set.range (fun p:Trans j × marks (timeMesh Λ)=> U p.1 p.2)

section
lemma omega_build : DenseRange (fun p : St => p.val (Ω).val) := by -- (Ω).val syntax fix
  apply (sounds Y H V G.history.circuit j 0 strict C).mono
  intro x a; obtain ⟨s,p⟩ := mem_iUnion.mp a; obtain ⟨y,rfl⟩:=p
  obtain ⟨i, ⟨f, rfl⟩, p⟩:= ((field_entry Y H j strict s y).and (eventually_gt_atTop (0:ℕ))).exists
  exact ⟨boxElement Y H V G j strict C s i f p,lays Y H V s G.history G.clipped j strict C i f p⟩
lemma approach_star {x : St}(p:x∈approach Y H V G j strict C) : star x∈approach Y H V G j strict C:=by
  rcases p with ⟨a,rfl⟩|⟨⟨u,v⟩,rfl⟩
  · exact Or.inl ⟨a,Subtype.ext (advance_adjoint Y H V G.history.circuit j 0 strict C a).symm⟩
  exact Or.inr ⟨(u,-v),Subtype.ext (shift_star Y H V G j strict C u v).symm⟩
end

variable (d : Axis) (C' : Arena Y H G.history.circuit d 0 strict)
local notation "α"=>catalog Y H V G d strict C'
local notation "ω'"=>seat0 Y H V G.history d strict C'

-- identify spectra *before* pulling phases
noncomputable def earlyMap : (α)≃⋆ₐ[ℂ](A₀) := (catalogEquiv Y H V G d strict C' j C).choose
local notation "φ"=>earlyMap Y H V G j strict C d C'
local notation "𝒰"=>connector Y H V G d strict C' j C
lemma matches_map (x:α) : (φ x).val=(𝒰).conjStarAlgEquiv x.val := (catalogEquiv Y H V G d strict C' j C).choose_spec x

noncomputable def bank : Transaction (α) (St) Γ where
  station := (St).subtype
  corner := (A₀).subtype.comp (φ).toStarAlgHom
  mono_ := Subtype.val_injective.comp (φ).injective
  mark := (φ).symm.toStarAlgHom.toAlgHom.toLinearMap.comp (compress Y H V G j strict C) -- may not name
  match_P b:= by change (φ ((φ).symm (cP b))).val=_; rw [StarAlgEquiv.apply_symm_apply]; rfl
  original := Ω
  unit := scalar_norm ..
  searches:=omega_build Y H V G j strict C
  steps:= approach Y H V G j strict C
  star_move _:= approach_star Y H V G j strict C
  grounds x:= by
    rw [full_joint]; constructor
    · intro ⟨s,v⟩ y p; rcases p with ⟨r,rfl⟩ | ⟨⟨a,n⟩,rfl⟩
      · exact s r
      exact v a n
    intro h; exact ⟨fun r=> h (Q r) (Or.inl ⟨_,rfl⟩),fun i v=>h (U i v) (Or.inr ⟨(i,v),rfl⟩)⟩
local notation "T"=>bank Y H V G j strict C d C'

lemma bar_move (x:α) : inner ℂ Ω (((T).corner x) Ω)=inner ℂ ω' (x.val ω') := by
  change inner ℂ Ω ((φ x).val Ω) = _; rw [matches_map, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    ←connector_omega Y H V G d strict C' j C,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]

instance : MeasurableSpace (Resident α) := borel _
instance : BorelSpace (Resident α) := ⟨rfl⟩
noncomputable def residents : Measure (Resident α) := (bank Y H V G d strict C' d C').ensemble
local notation "μ"=>residents Y H V G strict d C'
instance : IsProbabilityMeasure μ := Transaction.normalized _
instance : Measure.Regular μ  := show Measure.Regular (bank Y H V G d strict C' d C').ensemble from inferInstance
lemma all_residents : (T).Bary μ := by
  constructor; intro a
  exact (((bank Y H V G d strict C' d C').barcode).use_char a).trans
    ((bar_move Y H V G d strict C' d C' a).trans (bar_move Y H V G j strict C d C' a).symm)

lemma almostGround : ∀ᵐ x∂μ, (T).FixedPhase x := by
  obtain ⟨p,hp⟩:= horizons Y H V G j strict C
  exact Transaction.generically T μ (all_residents Y H V G j strict C d C') p hp

instance open_worth : Measure.IsOpenPosMeasure μ := by
  let R := bank Y H V G d strict C' d C'
  refine R.full_support ?_
  intro a p h
  have hh : (earlyMap Y H V G d strict C' d C' a)=0 := faithful Y H V G d strict C' _ (show _ from h)
  apply p; exact (earlyMap Y H V G d strict C' d C').injective (hh.trans (map_zero _).symm)

lemma weighty {p:Resident α → Prop} (a:α)(b:ℝ)(g:b≤ ‖inner ℂ ω' (a.val ω')‖)
    (t:∀ᵐ x∂μ,p x) : ∃ x, p x ∧ b≤ ‖eye x a‖ :=
  (bank Y H V G d strict C' d C').succeeds b a
    (g.trans_eq (congrArg norm (bar_move Y H V G d strict C' d C' a).symm)) t
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.weighty
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.almostGround
