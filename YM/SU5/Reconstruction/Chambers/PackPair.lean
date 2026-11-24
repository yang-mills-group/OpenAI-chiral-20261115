import YM.SU5.Reconstruction.Chambers.AllHorizons
import YM.SU5.Reconstruction.Chambers.Transverse
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
namespace Chambers
open Selected SlabMark MeshClock Schedule SelectionAnalysis
open Schedule.Fixture Schedule.Compose
set_option quotPrecheck false
local notation "D" => Domain Y H G
local notation "R" => RSpace
local notation "Γ" => (MeshClock.marks (timeMesh Λ))
variable {α : Type*}
variable (j₀ : Axis) (C : ∀ j : Axis, Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j₀ false (C j₀) →⋆ₐ[ℂ] ℂ)
local notation "F" => osValue Y H V G j₀ (C j₀) χ
local notation "I" j:max => indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped j₀ false (C j₀) χ j (C j))
local notation "u'" j:max=> displacement Y H V G.history G.clipped j₀ false (C j₀) χ j (C j)
local notation "C'" j:max=> (C j)
local notation "W" j:max => fort Y H V G.history G.clipped j false (C j) (u' j)
local notation "K'" j:max=> mainsea Y H V G.history G.clipped j false (C j) (u' j)
local notation "S" j:max=> ride Y H V G.history G.clipped j false (C j) (u' j)
local notation "P" j:max=> peninsula Y H V G.history G.clipped j false (C j) (u' j)
local notation "Ωr" j:max=> doorstep Y H V G.history G.clipped j false (C j) (u' j)
local notation "Ωc" j:max=> vocation Y H V G.history G.clipped j false (C j) (u' j)


section basic
-- every family of local probes can be given all-axis budgets even with
-- arbitrary shapes. use for gauge pieces and with contact-tests
-- included before the moving-stage readings
lemma available (A : α→ Sky (tent Y H)) (h : ∀ i,A i∈ Domain Y H G false Set.univ) :
    Nonempty (Presentable Y H G A) := by
  choose U t e b using fun i=> (compact_domain Y H G).1 (h i)
  choose a' b' p hp using fun i j=> shutters (daylight (timeMesh Λ)) j (t i)
  let X : Schedule.Fixture (marks (timeMesh Λ)) α:= ⟨a',fun i j=> b' i j - a' i j,fun i j=> sub_pos.mpr (p i j)⟩
  refine ⟨X, fun j i=> domain_mono Y H G ?_ (b i)⟩; intro x e0
  change (a' i j:ℝ) ≤ x j ∧ x j ≤ (a' i j:ℝ)+((b' i j:ℝ)-(a' i j:ℝ))
  obtain ⟨c,d⟩ := hp i j x e0
  exact ⟨c.le, d.le.trans_eq (by ring)⟩
end basic

section duet
-- Bool for reading two inserts. for connection to the nonfactorizing (both conditioned
-- and unconditioned), on the same moving frame. all of this works in that same footprint.
local notation "D₀" => (marks (timeMesh Λ))
local notation "X₀" => D false Set.univ

noncomputable def duet {A : Type*}(x y:A) : Bool → A
| false => x
| true => y
local notation "l₂" => ([false,true] : List Bool)
@[simp] lemma duet_first {A : Type*}{x y:A} : duet x y false=x := rfl
@[simp] lemma duet_second {A : Type*}{x y:A} : duet x y true=y := rfl

structure SpaceFor (Λ : Preparation) (X W' : Set RSpace) where
  registerQ : Schedule.Fixture (marks (timeMesh Λ)) Bool
  back : Axis→ placement Λ
  printed (j : Axis) (k : Bool) : duet X W' k ⊆ strip j (registerQ.low k j) (((registerQ.low k j):ℝ) + ((registerQ.width k j):ℝ))
  zero_fits : (0 : Bool → RSpace) ∈ registerQ.ready back (fun _=>[false,true])

local notation "B" => Schedule.Fixture
variable (W₁ W₂ : Set RSpace)
local notation "T₀" => (SpaceFor Λ W₁ W₂)

lemma budget_pair (Λ : Preparation) (a : IsCompact W₁)(b : IsCompact W₂)
    (c : ∀ j:Axis,∀ x∈W₁,∀ y∈ W₂,x j< y j) : Nonempty (SpaceFor Λ W₁ W₂) := by
  choose h t u v hv₁ hv₂ hv₃ hx hy using fun j=> choose_grip (daylight (timeMesh Λ)) j a b (c j)
  choose a' e using fun j=> very_early (daylight (timeMesh Λ)) (a:=(h j:ℝ))
  let x : Schedule.Fixture (marks (timeMesh Λ)) Bool :=
    ⟨duet h u,duet (fun i=> t i - h i) (fun i=> v i-u i),fun i j=>?_⟩; swap; · cases i; exact sub_pos.mpr (hv₁ j); exact sub_pos.mpr (hv₃ j)
  refine ⟨x,(fun i=> eject i (a' i)),?_,?_⟩
  · intro j i; cases i
    · intro k l; specialize hx j k l; change ↑(h j)≤ k j ∧ k j ≤ ↑(h j)+(↑(t j)-(h j:ℝ)); exact ⟨hx.1.le,hx.2.le.trans_eq (by ring)⟩
    intro k l; specialize hy j k l; change ↑(u j) ≤ k j ∧ k j ≤ ↑(u j)+(↑(v j)-(u j:ℝ)); exact ⟨hy.1.le,hy.2.le.trans_eq (by ring)⟩
  intro i; refine ⟨?_,⟨?_,trivial⟩⟩
  · rw [if_pos rfl]; change 0 < _ - paste (eject i (a' i)) i
    unfold paste Schedule.Fixture.start; dsimp [x]; simp; exact e i -- tune
  rw [if_pos rfl]; change 0 < (Schedule.Fixture.start x i _ true) i - (Schedule.Fixture.stop x i _ false) i
  simp only [Schedule.Fixture.start,Schedule.Fixture.stop,x,Pi.add_apply,Pi.zero_apply, Pi.single_eq_same,duet_second,duet_first,zero_add]; change 0 < (u i:ℝ) - (↑(h i)+((t i:ℝ)-↑(h i)))
  linarith [hv₂ i]

local notation "Z" => duet W₁ W₂
variable {W₁ W₂}
variable (t : SpaceFor Λ W₁ W₂)
lemma still_separated (p : Bool→ RSpace) (u : p∈ t.registerQ.ready t.back (fun _=>[false,true])) :
    ∀ i:Axis,∀ x∈ slides (p false) W₁,∀ y∈slides (p true) W₂, x i < y i := by
  rintro i _ ⟨x,h,rfl⟩ _ ⟨y,c,rfl⟩; let T':= t.registerQ;
  have v:= t.printed i false h; have w:= t.printed i true c
  have b : 0 < T'.start i p true i-T'.stop i p false i := (u i).2.1
  simp only [Schedule.Fixture.start,Schedule.Fixture.stop,Pi.add_apply,Pi.single_eq_same] at b ⊢
  linarith only [b,w.1, v.2] -- tune abbreviation

noncomputable def given {x y : Sky (tent Y H)} (p : x∈ Domain Y H G false W₁) (q : y∈ Domain Y H G false W₂) : Presentable Y H G (duet x y) :=
  ⟨t.registerQ, by intro i v; cases v; exact domain_mono Y H G (t.printed i false) p; exact domain_mono Y H G (t.printed i true) q⟩

variable {x y : Sky (tent Y H)} (p : x∈ Domain Y H G false W₁) (q : y∈Domain Y H G false W₂)
noncomputable def pairedReading (j : Axis) :=
  prices Y H V G j₀ C χ (duet x y) (given Y H G t p q) (fun _=> l₂) t.back j
local notation "R₁" => pairedReading Y H V G j₀ C χ t p q
local notation "Us" => (t.registerQ.ready t.back (fun _=> [false,true]))
include V

lemma grid_pair (g : Bool→ Selected.placement Λ)(v : Schedule.Fixture.enter g∈ t.registerQ.ready t.back (fun _=> [false,true])) :
    ∀ j:Axis, ∃ a : Domain Y H G false (slides (coordinates Λ (g false)) W₁ ∪ slides (coordinates Λ (g true)) W₂),
      a.val=move K (g false) x * move K (g true) y ∧
      pairedReading Y H V G j₀ C χ t p q j (Schedule.Fixture.enter g)= F ⟨a.val, domain_le_lawDomain Y H G _ a.property⟩ := by
  have h := still_separated t (Schedule.Fixture.enter g) v
  have h₁:= moving Y H V G (g false) x p; have h₂:= moving Y H V G (g true) y q
  let g' := (duet x y); have c : generate Y H (duet x y) g l₂ = _ := show generate Y H (duet x y) g l₂=move K (g false) x * move K (g true) y from (by simp only [generate_step,generate_nil,duet_first,duet_second,mul_one]);
  intro j; obtain ⟨a,k⟩:= prices_here Y H V G j₀ C χ g' (given Y H G t p q) (fun _=>[false,true]) t.back l₂ (by decide) (fun _=> .refl _) j g v
  have he := domain_mult Y H G h₁ h₂ (Set.disjoint_left.mpr (fun {i} w r=> lt_irrefl _ (h 0 i w i r)))
  exact ⟨⟨generate Y H (duet x y) g l₂, c.symm ▸ he⟩, c,k.trans (dif_pos a)⟩

-- continuity is unrestricted (projection formula), agreement of analytic data ONLY on chambers.
lemma pair_bound (j : Axis)(p : x∈ Domain Y H G false W₁)(q:y∈D false W₂):
    AnalyticOnNhd ℝ (pairedReading Y H V G j₀ C χ t p q j) Us := internal_analytic Y H V G j₀ C χ _ (given Y H G t p q) _ _ l₂ (by decide) (fun _ => .refl _) _

lemma pair_across (j k:Axis) : EqOn (R₁ j) (R₁ k) (t.registerQ.ready t.back (fun _=> l₂)) :=
  full_continuous_extension Y H V G j₀ C χ _ (given Y H G t p q) _ _ l₂ (by decide) (fun _=>.refl _) _ _

lemma pair_center (a : Domain Y H G false Set.univ) (v : a.val=x*y) (j : Axis) : pairedReading Y H V G j₀ C χ t p q j 0 = F a := by
  have he : (Schedule.Fixture.enter (0:Bool→placement Λ))=0 := rfl
  obtain ⟨z,w,k⟩:= grid_pair Y H V G j₀ C χ t p q 0 (he.symm ▸ t.zero_fits) j; rw [he] at k
  rw [k]; apply congrArg F; apply Subtype.ext; change z.val = a.val; rw [w,v]; simp only [Pi.zero_apply,move_by_zero]
end duet
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
