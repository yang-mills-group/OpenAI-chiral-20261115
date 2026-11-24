import YM.SU5.Selected.Fixture

/-!
# The abelian cap algebra at all levels of the Satin coherent law

Omega here in the *joint* fixed subspace (not heat alone). Work with
any Veranda. Operators equality, not just a distribution of cap means.
The permutation theorem for distinct labels suffices because it's true for
inputs with arbitrary repeated marks.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
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
open Set

/-- Every `Field` fits *unshifted* in an entry of positive width. -/
theorem field_entry (s : ℕ) (x : Fₛ s) :
    ∀ᶠ u : ℕ in atTop, ∃ f : Entry Y H s j strict u, f.val = x := by
  have h := (purpose_ok ..).1 x.property
  obtain ⟨S,hS,h⟩ := (h.1 : ∃ S, InTest K true S false x.val ∧
      Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S)
  rw [area0] at h
  have hu : Tendsto (fun v : ℕ => ruler Λ.block * (v:ℤ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop' (ruler_gene _) -- ordered ring?
  have h' : ∀ᶠ u : ℕ in atTop, ∀ t ∈ S, t j + (K).ℓ ≤ ruler Λ.block * (u:ℤ) :=
    S.eventually_all.mpr fun t _ => hu.eventually_ge_atTop _
  exact h'.mono (fun d hv => ⟨(⟨x,S,hS, fun t ht => ⟨h t ht, hv t ht⟩ ⟩ : Entry Y H s j strict d),rfl⟩)

noncomputable def observableOf (s : ℕ) (x : Fₛ s) : observable K strict :=
  ⟨x.val,(exam j _ K ((purpose_ok ..).1 x.property).1).1, ((purpose_ok ..).1 x.property).2⟩

lemma cap_entry (s u : ℕ) (f : Entry Y H s j strict u) (h : 0 < u) :
    (P s) (observableOf Y H j strict s f.val) = (π).comp ((B s f h).comp ι₀) := by
  apply onAny Y H V s G.history G.clipped j strict C
    (⟨0,u,h,f,(relocate_zero K j (test_entry ..)).symm⟩ :
      Veranda Y H s j strict (observableOf Y H j strict s f.val))

lemma cap_actor (s : ℕ) (x : Fₛ s) :
    ((P s) (observableOf Y H j strict s x)) Ω = π ((κ s) x) := by
  obtain ⟨u, ⟨f, rfl⟩, p⟩ := ((field_entry Y H j strict s x).and (eventually_gt_atTop (0:ℕ))).exists
  rw [cap_entry Y H V G j strict C s u f p]
  exact congrArg (π) (lays Y H V s G.history G.clipped j strict C u f p)

abbrev disc (x : Beacon K strict) : (Γ) →L[ℂ] (Γ) := (P x.1) x.2
local notation "cD" => disc Y H V G j strict C

lemma cyclic : DenseRange fun (x : Beacon (tent Y H) strict) => cD x Ω := by
  let T := itinerary Y H V G.history.circuit j 0 strict C
  have he : DenseRange (π ∘ fun x : T => x.val) :=
    (show Surjective π from fun x : Γ => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x⟩).denseRange.comp
      (show DenseRange (fun x : T => x.val) by simpa [DenseRange] using (sounds Y H V G.history.circuit j 0 strict C))
      (π).continuous -- order?
  apply he.mono
  rintro y ⟨x,rfl⟩
  obtain ⟨s,hs⟩ := mem_iUnion.mp x.property
  obtain ⟨f,hf⟩ := hs
  exact ⟨(s,observableOf Y H j strict s f),(cap_actor Y H V G j strict C s f).trans (congrArg (π) hf)⟩

private lemma positions (x y u v : Beacon K strict) :
    inner ℂ Ω ((cD x * cD y * cD u * cD v) Ω) =
    inner ℂ Ω ((cD x * cD u * cD y * cD v) Ω) := by
  let f : Fin 4 → Beacon K strict := ![x,y,u,v]
  have ht := Vacancy.any_order Y H V G.history G.clipped j strict C f [0,1,2,3] [0,2,1,3]
    (by decide) (List.Perm.cons 0 (List.Perm.swap ..))
  exact ht

lemma commutes (u v : Beacon K strict) : Commute (cD u) (cD v) := by
  change (cD u) * (cD v) = (cD v) * (cD u)
  apply DFunLike.coe_injective
  apply (cyclic Y H V G j strict C).equalizer (cD u * cD v).continuous (cD v * cD u).continuous
  funext x
  apply (cyclic Y H V G j strict C).eq_of_inner_right ℂ
  intro y
  rw [← ContinuousLinearMap.adjoint_inner_right (cD y) Ω, ← ContinuousLinearMap.adjoint_inner_right (cD y) Ω,
    disc,mirror_cap Y H V _ G.history G.clipped j strict C]
  exact positions Y H V G j strict C (y.1,dual Y H j strict y.2) u v x

lemma scalar_norm : ‖Ω‖ = 1 := vane Y H V G.history.circuit j 0 strict C
lemma faithful_of_commute (x : (Γ) →L[ℂ] (Γ)) (h : ∀ f, Commute x (cD f))
    (p : x Ω = 0) : x = 0 := by
  apply DFunLike.coe_injective
  apply (cyclic Y H V G j strict C).equalizer x.continuous (0 : (Γ) →L[ℂ] (Γ)).continuous
  funext f
  change (x * cD f) Ω = 0
  rw [(h f).eq]
  change cD f (x Ω) = 0
  rw [p,map_zero]

private theorem cli_top (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] : IsSemitopologicalSemiring (W →L[ℂ] W) := inferInstance
private theorem cli_star (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] : ContinuousStar (W →L[ℂ] W) := inferInstance
instance : IsSemitopologicalSemiring ((Γ) →L[ℂ] (Γ)) := cli_top (Γ)
instance : ContinuousStar ((Γ) →L[ℂ] (Γ)) := cli_star (Γ)

/-- Concrete unital C*-algebra on the joint fixed space. -/
noncomputable def catalog := StarAlgebra.adjoin ℂ (Set.range cD) |>.topologicalClosure
local notation "A₀"=> catalog Y H V G j strict C

lemma included (x : Beacon (tent Y H) strict) : cD x ∈ A₀ :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ (Set.range cD) (Set.mem_range_self x))

lemma catalog_comm (x y : A₀) : x*y=y*x := by
  let U:= StarAlgebra.adjoin ℂ (Set.range cD)
  have hp {x y} (hx : x ∈ Set.range cD) (hy : y ∈ Set.range cD) : x*y=y*x := by
    obtain ⟨u,rfl⟩ := hx
    obtain ⟨v,rfl⟩ := hy
    exact (commutes Y H V G j strict C u v).eq
  have ht {x} (hx : x ∈ Set.range cD) : star x ∈ Set.range cD := by
    obtain ⟨u,rfl⟩ := hx
    exact ⟨(u.1,dual Y H j strict u.2),(mirror_cap (F:=u.2) Y H V u.1 G.history G.clipped j strict C).symm⟩
  haveI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ (fun _ hx _ hy => hp hx hy)
    (fun _ hx _ hy => hp hx (ht hy))
  letI := U.commSemiringTopologicalClosure (fun x y => IsMulCommutative.is_comm.comm x y)
  exact (show ∀ (x y : U.topologicalClosure), x*y=y*x from fun x y => mul_comm x y) x y

instance catalog_closed : IsClosed (A₀ : Set ((Γ) →L[ℂ] (Γ))) := isClosed_closure
noncomputable instance : CommCStarAlgebra (A₀) := {
    StarSubalgebra.cstarAlgebra (A₀) with mul_comm := catalog_comm Y H V G j strict C }

lemma faithful (x : A₀) (h : x.val Ω = 0) : x = 0 := by
  apply Subtype.ext
  refine faithful_of_commute Y H V G j strict C x.val (fun f => ?_) h
  exact congrArg Subtype.val (catalog_comm Y H V G j strict C x (⟨_, included Y H V G j strict C f⟩ : A₀))

lemma cyclic_algebra : DenseRange fun (x : A₀) => x.val Ω := by
  apply (cyclic Y H V G j strict C).mono
  rintro y ⟨x,rfl⟩
  exact ⟨⟨_,included Y H V G j strict C x⟩, rfl⟩

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.catalog_comm
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.faithful
