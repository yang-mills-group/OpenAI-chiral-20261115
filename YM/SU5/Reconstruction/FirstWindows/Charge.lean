import YM.SU5.Reconstruction.FirstWindows.Link
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 5000
set_option maxHeartbeats 500000
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
open CF.Pannier.Chancel CF.Pannier.Chancel.Cliplet Py.Rate.Pannier
  Fock Lat Lifted Peaks Spire Tenant Vale
  SlabMark MeshClock Tapestry.Exhibition Tapestry.Altitude
attribute [local instance] opCStarAlgebra
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
set_option quotPrecheck false

section charges
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
variable (s : ℕ) (p w : Cover)
local notation "F" => osValue Y H V G j C χ
local notation "Psi" => sameRead Y H V G j C χ s
local notation "g'₀" A:max => bufferedHull Λ l s (reflectedBox j 0 (streetBox (tent Y H) p A))
local notation "g'₁" A:max => bufferedHull Λ l s (streetBox (tent Y H) w A)
variable (S : Finset Cover) (z : SU.Slot) (o : Cover) (u d : ℕ) (f : Marks (tent Y H) true)
local notation "D₀" => g'₀ S -- tune
local notation "D₁" => g'₁ S
local notation "z₀" => leg j p (fromStrict f)
local notation "z₁" => reposition (tent Y H) w (fromStrict f)
-- explicitly no unfolding at application surprises, also proves polynomial through algebra eval at common level
local notation "E₀" => insideAt Λ l K true
local notation "Ω" => ((Set.univ : Set ℕ) ∩ Set.Iic s)
local notation "κ" => ticket Y H G s
open SelectionAnalysis Spectral Germ
variable (δ : ℝ)
local notation "B₀" => (peninsula Y H V G.history G.clipped j false C χ).E
local notation "R" => (peninsula Y H V G.history G.clipped j false C χ).U
local notation "W" x:max => compassKet Y H V G j C χ x

lemma validate_link
    (h : Survivor Y H V s G.history G.clipped j C z o u d S f χ)
    (v : Exceeds Y H V s G.history G.clipped j C χ δ f z S o u d p w) :
    LinkCheck Y H V G j C χ s p w S z o u d f δ := by
  have ht := FilTest h.link.mark_mem
  have t : InTest K false (reflectedBox j 0 (streetBox K p S)) false (leg j p (fromStrict f)).val :=
    leg_narrow (x:=fromStrict f) j p ht
  have e : InTest K false (streetBox K w S) false (reposition (tent Y H) w (fromStrict f)).val :=
    other_narrow (y:=fromStrict f) w ht
  have lz : z₀ ∈ E₀ D₀ s := by
    apply (mem_insideAt ..).2; refine ⟨⟨_,t.widen,hull_support _ _ _ _⟩,fun _=>?_⟩
    rw [leg_strict]; exact ((marksSpec true _).2 rfl)
  have rz : z₁ ∈ E₀ D₁ s := by
    apply (mem_insideAt ..).2; refine ⟨⟨_,e.widen,hull_support _ _ _ _⟩,fun _=>?_⟩
    rw [reposition_strict]; exact ((marksSpec true _).2 rfl)
  have sa : ∀ i : Axis, ∀ x ∈ g'₀ S, ∀ y ∈ g'₁ S, x i+δ≤ y i := fun i _ a _ b => separated_hulls Λ l s _ i (v.shelf.span_positions i) a b
  have b := separated_disjoint Λ l s _ j (v.shelf.span_positions j)
  have hz := v.shelf
  let Tt' := mirrorInMarks Y H j true (relocateWorld Y H true p f) * relocateWorld Y H true w f
  let ψm := response Y H V s G.history G.clipped j false C χ
  have val' : Psi (z₀*z₁) = ψm (bosonLabel K Tt') := by
    rw [pigment_here]
    have e : (z₀*z₁).val=Tt'.val := hz.whole_twin.symm
    rw [e]; exact reads_color Y H V s G.history G.clipped j C χ (bosonLabel K Tt')
  refine ⟨v,h,lz,rz,sa,b,⟨compact_hull ..,compact_hull ..⟩,?covers,?cur,?paid,?fee,?finance,?rep,fun t=>?_⟩
  case covers => exact (((V.pick.grow_i.comp G.history.growsA).tendsto_atTop).eventually (unwrapped Y H s _))
  case cur =>
    apply (PhaseChoice.circum Λ l K false (D₀∪D₁) Ω).mul_mem
    · apply wellGrows Λ K l false (PhaseChoice.handstamp D₀) (PhaseChoice.handstamp (D₀∪D₁)) Ω Ω Set.Subset.rfl (Set.preimage_mono Set.subset_union_left)
      exact narrow_price Y H s t (hull_support _ _ _ _) lz
    apply wellGrows Λ K l false (PhaseChoice.handstamp D₁) (PhaseChoice.handstamp (D₀∪D₁)) Ω Ω Set.Subset.rfl (Set.preimage_mono Set.subset_union_right)
    exact narrow_price Y H s e (hull_support _ _ _ _) rz
  case paid => exact ticket_separated Y H G lz rz b
  case fee => rw [val']; exact hz.consumption
  case finance => exact decomposition_fails Y H V G j C χ s p w hz.paid (detached_disjoint hz.structured) h.link.anchor_inj
  case rep =>
    obtain ⟨x,y,hx,hy,_,hv,pv,_⟩ := v.extendsTo
    let x' : Dome (tent Y H) := reposition K p (fromStrict f)
    have xp : x'.val=x.val := (congrArg Subtype.val (reposition_strict Y H p f)).trans hx.symm
    have yp : (z₁).val=y.val := (congrArg Subtype.val (reposition_strict Y H w f)).trans hy.symm
    let r : x'∈E₀ (flank j 0) s := by
      have ha : x' ∈ insideAt Λ l K false (flank j 0) s := (positive_today Y H j s x').2 (xp.symm ▸ x.property)
      refine (mem_insideAt x' s).2 ⟨((mem_insideAt x' s).1 ha).1,?_⟩; rw [show x'=fromStrict (relocateWorld Y H true p f) from reposition_strict ..]; exact (marksSpec true _).2
    let v : z₁ ∈ E₀ (flank j 0) s := by
      have ha := (positive_today (q:=false) Y H j s z₁).2 (yp.symm ▸ y.property)
      exact (mem_insideAt z₁ s).2 ⟨((mem_insideAt z₁ s).1 ha).1,((mem_insideAt z₁ s).1 rz).2⟩
    let X:= enclose Y H G (flank j 0) true s ⟨x',r⟩
    let Z:=enclose Y H G (flank j 0) true s ⟨z₁,v⟩
    have ex : flipMark j (tent Y H) X.val=κ z₀ := flipMark_ticket Y H G j s x'
    let A0 := land Y H V s G.history G.clipped j false C χ
    have h' : W X=A0 x := compass_land Y H V G j C χ s x x' xp r (ticket_mem Y H G r)
    have v' : W Z=A0 y := compass_land Y H V G j C χ s y z₁ yp v (ticket_mem Y H G v)
    refine ⟨X,Z,ex,rfl,?_,?_,?_⟩
    · let X' : Domain Y H G false (flank j 0) := ⟨X.val,domain_loose _ _ _ _ X.property⟩
      let Z' : Domain Y H G false (flank j 0) := ⟨Z.val,domain_loose _ _ _ _ Z.property⟩
      apply (registered_pair Y H V G j C χ X' Z').trans
      apply congrArg F; apply Subtype.ext; change flipMark j _ X.val * κ z₁ = _; rw [ex]; exact (ticket_separated Y H G lz rz b).symm
    · rw [val', ←show scene Y H V s G.history G.clipped j false C χ x y 0= ψm (bosonLabel K Tt') from pv,peninsula_window, h', v']
      simp only [Pi.zero_apply, Real.toNNReal_zero,OS.Semigroup.eZero]; rw [show diameter (a:=j) 0 = 0 from map_zero (OS.Semigroup.SEP j),OS.Semigroup.uZero]; rfl
    filter_upwards [hv] with a hc; rw [h', v']; rw [peninsula_window] at hc; exact hc
  exact twin_silent j p w t
end charges
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
