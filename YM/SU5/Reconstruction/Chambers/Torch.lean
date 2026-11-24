import YM.SU5.Reconstruction.Chambers.PackPair
import YM.SU5.Reconstruction.FirstWindows.Link
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

open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
-- Carry managed glass probes through continuum chamber interpretation and budget
-- variation. PairedBooks remember all lifts at all levels (incl dense gate),
-- not interpreting new PURE basis at off-grid. The continuation of the split-
-- witness experiment is of FOUR READINGS on these charged insertions, each
-- resolved by the appointed flow. The gauge-vs-matter cut, like curvature
-- and CRow syntax, is decided at the observing resolution; not saying
-- separately resolved contact-pieces still pure/independent.
local notation "E₂"=> Bool→RSpace
variable (W₁ W₂ : Set RSpace) (s:ℕ)
variable (B : SpaceFor Λ W₁ W₂)

def field_of (x : insideAt Λ l (tent Y H) false W₁ s) : Domain Y H G false W₁ := ⟨ticket Y H G s x.val,ticket_mem Y H G x.property⟩

section pair
variable (x : Dome (tent Y H)) (y : Dome (tent Y H))
variable (a : x∈ insideAt Λ l (tent Y H) false W₁ s)(b : y∈ insideAt Λ l (tent Y H) false W₂ s)
-- computed exactly through the moving pair RECIPE (incl spending positions in the one Compass).
-- At origin it's the seated reading; on Grid use grid_pair even if placements not visible @ s;
-- away, interpreting via analytic matrix of the same slots.
noncomputable def film (x y : Dome (tent Y H))(a : x∈insideAt Λ l (tent Y H) false W₁ s)
    (b : y∈insideAt Λ l (tent Y H) false W₂ s) := pairedReading Y H V G j₀ C χ B (ticket_mem Y H G a) (ticket_mem Y H G b)

local notation "v₀"=> film Y H V G j₀ C χ W₁ W₂ s B x y a b
local notation "regionA"=> B.registerQ.ready B.back (fun _ => [false,true])
lemma torch_axis(i j:Axis):Set.EqOn (film Y H V G j₀ C χ W₁ W₂ s B x y a b i) (v₀ j) regionA := pair_across Y H V G j₀ C χ B (ticket_mem _ _ _ a) (ticket_mem _ _ _ b) i j
lemma torch_analytic (i:Axis): AnalyticOnNhd ℝ (film Y H V G j₀ C χ W₁ W₂ s B x y a b i) regionA := pair_bound Y H V G j₀ C χ B i (ticket_mem _ _ _ a) (ticket_mem _ _ _ b) -- order

lemma torch_center (e : Disjoint W₁ W₂)(i j:Axis) : film Y H V G j₀ C χ W₁ W₂ s B x y a b i 0 =
    sameRead Y H V G j (C j) (u' j) s (x*y) := by
  let f := ticket Y H G s (x*y)
  apply Eq.trans <| pair_center Y H V G j₀ C χ B (ticket_mem Y H G a) (ticket_mem Y H G b) ⟨f,ticket_loose ..⟩ (ticket_separated Y H G a b e) i
  unfold sameRead; rw [os_across Y H V G]

local notation "κ₀" => ticket Y H G s
lemma torch_read (z : Bool → Selected.placement Λ)(h : Schedule.Fixture.enter z∈ regionA ) (i:Axis) (U : Set RSpace)
    (r : Domain Y H G false U)
    (t : r.val=move K (z false) (ticket Y H G s x) * move K (z true) (κ₀ y)) :
    film Y H V G j₀ C χ W₁ W₂ s B x y a b i (Schedule.Fixture.enter z)=
      osValue Y H V G j₀ (C j₀) χ ⟨r.val,domain_le_lawDomain Y H G U r.property⟩ := by
  obtain ⟨x,t',v⟩:= grid_pair Y H V G j₀ C χ B (ticket_mem Y H G a) (ticket_mem Y H G b) z h i
  apply v.trans; apply congrArg F; apply Subtype.ext; exact t'.trans t.symm
end pair

section charge
variable (j : Axis) (S' : Finset Cover) (p q : Cover)
local notation "A"=>bufferedHull Λ l s (reflectedBox j 0 (streetBox K p S'))
local notation "B₁"=>bufferedHull Λ l s (streetBox K q S')
local notation "B'₁" => SpaceFor Λ A B₁
variable (R' : SpaceFor Λ (bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p S'))) (bufferedHull Λ l s (streetBox (tent Y H) q S')))
local notation "U₀" => R'.registerQ.ready R'.back (fun _=>[false,true])
local notation "A₀" x:max=> leg j p x
local notation "U₁" x:max=> reposition (tent Y H) q x
local notation "MP" => film Y H V G j₀ C χ A B₁ s R'
variable (d u₀ : ℕ) (f : Marks (tent Y H) true) (ζ: SU.Slot) (o : Cover) (δ : ℝ)
variable (h : LinkCheck Y H V G j (C j) (displacement Y H V G.history G.clipped j₀ false (C j₀) χ j (C j)) s p q S' ζ o u₀ d f δ)

-- pay for exact interacting experiment (neutral first-gauge at s)
noncomputable def canon := film Y H V G j₀ C χ A B₁ s R' (A₀ (fromStrict f)) (U₁ (fromStrict f))
      (insideAt_loose s h.first) (insideAt_loose s h.second)

variable {h f d u₀ o ζ δ}
lemma at_site (δ : ℝ) (f : Marks (tent Y H) true)
    (h : LinkCheck Y H V G j (C j) (u' j) s p q S' ζ o u₀ d f δ) (k:Axis):
    1/32 ≤ ‖canon Y H V G j₀ C χ s j S' p q R' d u₀ f ζ o δ h k 0‖ := by
  unfold canon; rw [torch_center Y H V G j₀ C χ _ _ _ _ _ _ _ _ h.apart k j]; exact h.answer

local notation "δt"=> (u' j) -- tune q mark
variable (f)
local notation "Pa"=> OnCharge Y H G j s p q S'
variable {f} {a b x y : Dome (tent Y H)}

noncomputable def relay {x y : Dome (tent Y H)} (v : OnCharge Y H G j s p q S' x y) := film Y H V G j₀ C χ A B₁ s R' (A₀ x) (U₁ y) v.left v.right
local notation "Mr" => relay Y H V G j₀ C χ s j S' p q R'

lemma division (δ : ℝ) (f : Marks (tent Y H) true)
    (h : LinkCheck Y H V G j (C j) (u' j) s p q S' ζ o u₀ d f δ)
    (p₁ : Pa a b) (p₂ : Pa x y)(p₃ : Pa (x*a) (y*b))
    (u : NoDecompose Y H V G j (C j) (u' j) s p q ζ u₀ d S' o a b x y)(k : Axis) :
    0 < ‖Mr p₃ k 0 - Mr p₁ k 0 * Mr p₂ k 0‖ := by
  unfold relay
  rw [torch_center Y H V G j₀ C χ A B₁ s R' _ _ _ _ h.apart k j, torch_center Y H V G j₀ C χ A B₁ s R' _ _ _ _ h.apart k j,torch_center Y H V G j₀ C χ A B₁ s R' _ _ _ _ h.apart k j]; exact u.operational

variable (f d u₀ ζ o δ)
local notation "kA" h:max=> canon Y H V G j₀ C χ s j S' p q R' d u₀ f ζ o δ h

noncomputable def Fuel (h : LinkCheck Y H V G j (C j) (u' j) s p q S' ζ o u₀ d f δ) :=
   ∃ (a b x y : Dome (tent Y H)) (_u : NoDecompose Y H V G j (C j) (u' j) s p q ζ u₀ d S' o a b x y)
      (p₁ : Pa a b) (p₂ : Pa x y)(p₃ : Pa (x*a) (y*b)) (e:ℝ), 0<e ∧
     (∀ᶠ q' : Bool→ RSpace in 𝓝 0, q'∈ U₀ ∧ ∀ k : Axis,
          1/33 ≤ ‖(kA h) k q'‖ ∧ e≤ ‖Mr p₃ k q' - Mr p₁ k q' * Mr p₂ k q'‖) ∧
     -- even continuing throughout chamber; no claims about contacts of the supports at
     -- lower edge. At any allowed displacements can budget arbitrarily near them a cert
     -- bought in the compass space *with these same probes*, simultaneous nonzero.
     ∀ q':Bool→ RSpace, q'∈ U₀ → ∃ᶠ g':Bool→ RSpace in 𝓝 q',
       g' ∈ U₀ ∧ ∀ k:Axis,(kA h) k g'≠0 ∧ Mr p₃ k g' ≠ Mr p₁ k g'*Mr p₂ k g'
end charge
end Chambers
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
