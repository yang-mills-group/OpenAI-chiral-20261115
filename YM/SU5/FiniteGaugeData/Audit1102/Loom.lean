import YM.CF.Vp929.Roof.Fit
import YM.CF.Buffered.Laws
import YM.SU5.FiniteGaugeData.Audit1102.ProductLaws

set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.SU5.FiniteGaugeData.Audit1102
open Function Finset MeasureTheory ProbabilityTheory
open YM
open Lattice CF Push.GridApprox
open SU Lat Cube Skye Scree
open YM.CF.VolumeCape YM.CF.VolumeCape.Cane YM.CF.VolumeCape.Dream
open YM.CF.VolumeCape.Mesh
open YM.CF.Buffered.Advance
open scoped Classical

/-- Radius in gauge sites, including both output stencils and the auxiliary mixing range. -/
def lawRadius (C : Side) : ℕ := 2 * Fringe C + reachT C

private lemma stencil_subset {n : Side} (r : ℕ) (S : Support (More n))
    (e : actualEdges (c:=More n) (S : Set (Seat n))) : win r e.val ⊆ halo r S := by
  apply Corona.halo_mono le_rfl
  intro x hx
  have h : x = e.val.1 ∨ x = e.val.1 + step e.val.2 := by simpa [Skye.ends] using hx
  rcases h with rfl | rfl
  · exact e.property.1
  · exact e.property.2

private lemma apart {n : Side} (C : Side) {S T : Support (More n)}
    (h : ∀ x∈S, ∀ y∈T, lawRadius C < separation x y) :
    stone (More n) (halo (Fringe C) S) (halo (Fringe C) T) (reachT C) := by
  intro x hx y hy
  obtain ⟨a,ha,ax⟩ := halo_spec.mp hx
  obtain ⟨b,hb,by'⟩ := halo_spec.mp hy
  have ab := h a ha b hb
  have t := separation_triangle a x b
  have u := separation_triangle x y b
  rw [separation_comm b y] at by'
  unfold lawRadius at ab
  omega

private def restrictTo {I A : Type*} (S : Finset I) (v : I → A) (i : S) := v i
private def extendFrom {I A : Type*} (S : Finset I) (v₀ : I → A) (v : S → A) (i : I) : A :=
  if h : i ∈ S then v ⟨i,h⟩ else v₀ i
private lemma extend_m {I A : Type*} [MeasurableSpace A] (S : Finset I) (v₀ : I → A) :
    Measurable (extendFrom S v₀) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i∈S
  · simpa [extendFrom,h] using
      (measurable_pi_apply (⟨i,h⟩ : S) : Measurable (fun v : S → A => v ⟨i,h⟩))
  · simp only [extendFrom,h,dif_neg,not_false_eq_true]
    exact measurable_const

private lemma scene_m {n : Side} (C : Side) (K : ℕ → ℝ) (V : Pane n) :
    Measurable (sceneQ C K n V) :=
  (sceneM C K n).of_uncurry_left

/-- The completed finite-range-in-law input supplies both fields of Buffered.LoomLaw,
at a radius independent of the torus. The ordinary measurability condition is on the
physical auxiliary map, with the gauge configuration held fixed. -/
theorem bufferedLaw {n : Side} (C : Side) (K : ℕ → ℝ) {l : Loom n}
    (hl : ∀ V : Pane n, Measurable (fun z => l (V,z))) (H : Haven C K n l) :
    LoomLaw l (lawRadius C) := by
  classical
  obtain ⟨μ,hμ,ind,law⟩ := H
  letI := hμ
  constructor
  · intro S V W h
    change (depot n).map (extract S ∘ fun z => l (V,z)) =
      (depot n).map (extract S ∘ fun z => l (W,z))
    rw [← Measure.map_map (extract_mp S) (hl V), ← Measure.map_map (extract_mp S) (hl W),
      law V,law W,Measure.map_map (extract_mp S) (scene_m C K V),
      Measure.map_map (extract_mp S) (scene_m C K W)]
    apply congrArg (fun f => ((Borel.Aerial.valsf n).prod μ).map f)
    funext z e
    change sceneQ C K n V z e.val = sceneQ C K n W z e.val
    apply sceneL C K n V W z z e.val
    · apply agrees_mono h
      exact (stencil_subset _ _ e).trans (Corona.halo_mono (by unfold lawRadius; omega) (Subset.refl S))
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
  · intro S T sep V
    let F := halo (Fringe C) S
    let G := halo (Fringe C) T
    have hFG := apart C sep
    have dis : Disjoint F G := Finset.disjoint_left.mpr fun x u v => by
      have z := hFG x u x v
      rw [separation_self] at z
      omega
    have fr (D : Support (More n)) :
        Measurable (restrictTo D : Borel.Aerial.Frame n → (D → SU.E)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply i.val
    have fi : IndepFun (restrictTo F) (restrictTo G) (Borel.Aerial.valsf n) :=
      Borel.independenceTape SU.group.probHaar (fr F) (fr G)
        (fun x y h => funext fun i => h i.val i.property)
        (fun x y h => funext fun i => h i.val i.property) dis
    have wi : IndepFun (restrictTo F) (restrictTo G) μ := ind F G hFG
    have wr (D : Support (More n)) :
        Measurable (restrictTo D : Read.Wor (More n) C → (D → _)) := measurable_of_countable _
    have joint := product_readings (fr F) (fr G) (wr F) (wr G) fi wi
    have inhabited : Nonempty (Read.Wor (More n) C) := by
      by_contra ha
      have empty : (Set.univ : Set (Read.Wor (More n) C)) = ∅ := by
        ext x
        exact (ha ⟨x⟩).elim
      have hbad := congrArg (fun s => μ s) empty
      simpa using hbad
    let w₀ : Read.Wor (More n) C := Classical.choice inhabited
    let f₀ : Borel.Aerial.Frame n := 1
    let eval (D : Support (More n)) :=
      (extract D ∘ sceneQ C K n V) ∘
        Prod.map (extendFrom (halo (Fringe C) D) f₀) (extendFrom (halo (Fringe C) D) w₀)
    have em (D : Support (More n)) : Measurable (eval D) :=
      ((extract_mp D).comp (scene_m C K V)).comp ((extend_m _ f₀).prodMap (extend_m _ w₀))
    have factor (D : Support (More n)) :
        eval D ∘ Prod.map (restrictTo (halo (Fringe C) D)) (restrictTo (halo (Fringe C) D)) =
        extract D ∘ sceneQ C K n V := by
      funext z e
      apply sceneL C K n V V _ z e.val
      · exact fun _ _ _ => rfl
      · intro x hx
        simp [extendFrom,restrictTo,stencil_subset _ _ e hx]
      · intro x hx
        simp [extendFrom,restrictTo,stencil_subset _ _ e hx]
    have measured := joint.comp (em S) (em T)
    change IndepFun (eval S ∘ Prod.map (restrictTo F) (restrictTo F))
      (eval T ∘ Prod.map (restrictTo G) (restrictTo G)) _ at measured
    rw [factor S,factor T] at measured
    exact transfer_readings (hl V) (scene_m C K V) (law V) (extract_mp S) (extract_mp T) measured

theorem nimbusLaw {n : Side} (i : ℕ) {l : Loom n}
    (hl : ∀ V : Pane n, Measurable (fun z => l (V,z))) (H : Dream.Nimbus i n l) :
    LoomLaw l (lawRadius (plot i).C) := bufferedLaw (plot i).C (plot i).K hl H

end YM.SU5.FiniteGaugeData.Audit1102
