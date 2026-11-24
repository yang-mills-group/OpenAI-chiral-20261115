import YM.SU5.May.RegistrationBase
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
namespace Spine

open Aria Germ Alliance SelectionAnalysis Set
variable (P : Spine) (x : P.Spectrum0 3) (j : Axis)
local notation "C" => P.room
local notation "Y" => P.run
local notation "L" => P.large
local notation "P₁" => P.par
local notation "V" => P.law
local notation "G" => P.projection
local notation "H" => P.history
local notation "H₁" => P.projection.clipped
local notation "χ" => P.mayChar x j
local notation "I₀" => P.mayHil x j
local notation "J" => P.advocate 3 x j
local notation "X" => P.ColorHil j J
local notation "B" s:max f:max => Selected.bud Y L V s H H₁ j false (C j) χ f
local notation "Ω" => Selected.doorstep Y L V H H₁ j false (C j) χ
local notation "Ωₓ" => P.colorZero j J

/-!
Clock and continuous sector identification project on the same displayed
response. `mayIntertwineS` and `mayPayments` below are between the actual
continuous sectors picked by the two theories on χ, with the same aperture
units as in the original experiment. (Neither CP1 nor these constructions assert
that continuity is purchased on the *whole* Hilbert space.)
-/
local notation "Uₓ" => P.mayIntertwine x j
local notation "U₀" => (Uₓ).toLinearIsometry.toContinuousLinearMap
local notation "T" => timeMesh P.par
local notation "S" => P.physicalEnergy j J
local notation "R" => Selected.ride Y L V H H₁ j false (C j) χ
local notation "κ" => P.voyageF j J
local notation "κ'" => Selected.turnstile Y L V H H₁ j false (C j) χ
local notation "ℳ" => marks (timeMesh P.par)
-- match clocks of the two readings, on all actors with full payments
private def mayTick (s n : ℕ) (f : P.naturalVox j s) : P.naturalVox j s :=
  ⟨tick Y L s j 0 false (2*n) f.val, by rw [← P.wishing]; exact P.shifts_keep j _ f.property⟩

lemma mayMesh_clock' (s n : ℕ) (f : P.naturalVox j s) :
    (R).E (whenly T s n) (Uₓ (P.province j J s f)) = Uₓ ((S).E (whenly T s n) (P.province j J s f)) := by
  rw [P.mayIntertwine_actor, Selected.ride_ticks]
  let p : P.birthF j s (P.voxTest j s f.val) := ⟨f, rfl⟩
  have he:= P.releasedLater j J s n p
  rw [P.holdsF j J s _ f rfl, P.holdsF j J s _ (P.mayTick j s n f) (P.wishing j s f n).symm] at he
  rw [← he, P.mayIntertwine_actor]; rfl

lemma mayMesh_clock (s n : ℕ) :
    (U₀).comp ((S).E (whenly T s n)) = ((R).E (whenly T s n)).comp U₀ := by
  apply ContinuousLinearMap.ext_on (P.maySpan x j)
  rintro _ ⟨⟨t,f⟩,rfl⟩; change
    Uₓ ((S).E (whenly T s n) (P.province j J t f)) = (R).E (whenly T s n) (Uₓ (P.province j J t f))
  rw [← matchR T s (max t s) n (le_max_right ..), ← P.mayProvince_raise x j (le_max_left t s) f]
  exact (P.mayMesh_clock' x j _ _ _).symm
lemma mayClock (t : ℝ≥0) :
    (U₀).comp ((S).E t) = ((R).E t).comp U₀ := by
  ext1 f
  suffices he : (fun t=> Uₓ ((S).E t f)) = (fun (t:ℝ≥0) => (R).E t (Uₓ f)) by exact congrFun he t
  apply (fills T).denseRange_val.equalizer
    ((Uₓ).continuous.comp ((S).continuousE f)) ((R).continuousE (Uₓ f)); funext d
  obtain ⟨s,n,e⟩ := MeshClock.split T d.property
  dsimp only [Function.comp_apply]; rw [←e]
  exact DFunLike.congr_fun (P.mayMesh_clock x j s n) f

lemma mayEdge (t : ℝ) :
    (U₀).comp ((S).edge t) = ((R).edge t).comp U₀ := within_energy (S) (R) U₀ (P.mayClock x j) t

private def mayPlay (s : ℕ) (a : Trans j) (i : ℤ) (f : P.naturalVox j s) : P.naturalVox j s :=
  ⟨sail Y L s j 0 false a.val a.property (2*i) f.val,P.sailNatur j s a.property i f⟩
lemma mayMesh_play (s : ℕ) (a : Trans j) (i : ℤ) (f : P.naturalVox j s) :
    ((κ').crew a).play (notch T s i) (Uₓ (P.province j J s f)) =
      Uₓ (((κ).crew a).play (notch T s i) (P.province j J s f)) := by
  rw [P.mayIntertwine_actor, Selected.turnstile_in, P.meets]
  let p : P.birthF j s (P.voxTest j s f.val) := ⟨f, rfl⟩
  have he:= P.released j J s a.property i p
  rw [P.holdsF j J s _ f rfl, P.holdsF j J s _ (P.mayPlay j s a i f) (P.sailImg j s a.property i f)] at he
  rw [← he, P.mayIntertwine_actor]; rfl
lemma mayPlays_map (a : Trans j) (d : ℳ) :
    (U₀).comp (((κ).crew a).play d) = (((κ').crew a).play d).comp U₀ := by
  obtain ⟨s,i,rfl⟩ := notch_exists T d
  apply ContinuousLinearMap.ext_on (P.maySpan x j)
  rintro _ ⟨⟨t,f⟩,rfl⟩; change
    Uₓ (((κ).crew a).play (notch T s i) (P.province j J t f)) = ((κ').crew a).play (notch T s i) (Uₓ (P.province j J t f))
  rw [← notch_up T s (max t s) (le_max_right ..) i, ← P.mayProvince_raise x j (le_max_left t s) f]
  exact (P.mayMesh_play x j _ _ _ _).symm
lemma mayPlays (a : Trans j) (d : ℳ) (f : X) :
    Uₓ (((κ).crew a).play d f) = ((κ').crew a).play d (Uₓ f) := DFunLike.congr_fun (P.mayPlays_map x j a d) f

-- Full continuous-space sector and its projection.
abbrev maySaunters := Selected.saunters Y L V H H₁ j false (C j) (P.mayChar x j)
local notation "ℙ" => P.maySaunters x j
abbrev mayFort := Selected.fort Y L V H H₁ j false (C j) (P.mayChar x j)
local notation "J₀" => P.mayFort x j
local notation "πχ" => (ℙ).orthogonalProjectionOnto
local notation "ℤ'" => P.ManyF j J
local notation "𝔽" => P.Viewers j J
local notation "Pχ" => P.wealth j J
local notation "ϑ" => P.enter j J

lemma maySector (v : X) : v∈𝔽 ↔ Uₓ v ∈ ℙ := by
  change _∈ (κ).aviator _ ↔ _∈ (κ').aviator _
  rw [Alliance.assembled, Alliance.assembled]; apply forall_congr'; intro i; apply imp_congr_right; intro _
  let p (d:ℳ) := ((κ).crew i).play d v
  change ContinuousAt p 0 ↔ ContinuousAt (fun d=> ((κ').crew i).play d (Uₓ v)) 0
  rw [show (fun d=> ((κ').crew i).play d (Uₓ v)) = Uₓ ∘ p from funext (fun d=> (P.mayPlays x j i d v).symm)]
  exact (Uₓ).isometry.isEmbedding.isInducing.continuousAt_iff

noncomputable def mayIntertwineS : P.ManyF j J ≃ₗᵢ[ℂ] P.mayFort x j where
  toFun v := ⟨Uₓ v.val,(P.maySector x j v.val).1 v.property⟩
  invFun v := ⟨(Uₓ).symm v.val, (P.maySector x j ((Uₓ).symm v.val)).2 ((Uₓ).apply_symm_apply v.val |>.symm ▸ v.property)⟩
  map_add' _ _ := Subtype.ext (map_add ..)
  map_smul' _ _ := Subtype.ext (map_smul ..)
  left_inv v := Subtype.ext ((Uₓ).left_inv v.val)
  right_inv v := Subtype.ext ((Uₓ).right_inv v.val)
  norm_map' v := (Uₓ).norm_map v.val
local notation "Z" => P.mayIntertwineS x j
lemma mayCross_enter (v : ℤ') : (Z v).val = Uₓ (ϑ v) := rfl
lemma mayWealth (f : X) : (𝔽).orthogonalProjectionOnto f = Pχ f := by
  apply Subtype.ext; change (𝔽).starProjection f = P.visitors j J f
  rw [P.visitors_op]
lemma mayPayments (f : X) : πχ (Uₓ f) = Z (Pχ f) := by
  apply ext_inner_left ℂ
  intro g; obtain ⟨v,rfl⟩:= (Z).surjective g
  calc
    _ = inner ℂ (Uₓ v.val) (Uₓ f) := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left («K»:=ℙ) (Z v) _
    _ = inner ℂ (ϑ v) f := (Uₓ).inner_map_map _ _
    _ = inner ℂ v (Pχ f) := by
      have e := P.mayWealth x j f
      exact ((𝔽).inner_orthogonalProjectionOnto_eq_of_mem_left (𝕜:=ℂ) v f).symm.trans
        (congrArg (fun (z:ℤ') => inner ℂ v z) e)
    _ = _ := ((Z).inner_map_map v (Pχ f)).symm

lemma maySaunters_full : ℙ=⊤ ↔ 𝔽=⊤ := by
  constructor
  · intro h; apply top_unique; intro v _; apply (P.maySector x j v).2; rw [h]; trivial
  intro h; apply top_unique; intro v _; obtain ⟨g,rfl⟩ := (Uₓ).surjective v
  exact (P.maySector x j g).1 (h.symm ▸ Submodule.mem_top)

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
