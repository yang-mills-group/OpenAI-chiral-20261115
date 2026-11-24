import YM.SU5.Reconstruction.FirstWindows.Half
/-!
# Displacements on the future test domain; arbitrarily remote half-space density.

OS vectors realize ALL `placement` motions (so also spectator/time simultaneously
on this arbitrary-fine grid). Merely representing on the grid does not assert they
are all continuous spatially.
-/
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
open SlabMark MeshClock
variable {J : Calibration} {q : Bool} {U W : Set RSpace}
local notation "D" => Domain Y H G

variable (j : Axis)
local notation "V₊" => flank j 0
local notation "V₋" => (mirrorE j 0 '' (flank j 0))
local notation "M" => timeMesh Λ

-- only a discrete group dense in R; don't use imaginary hol for this support billing.
theorem even_flank {a b : ℝ} (v : placement Λ) (p : a+(v j).val≥ b) :
    slides (coordinates Λ v) (flank j a) ⊆ flank j b := by
  rintro _ ⟨x,h,rfl⟩
  exact le_trans p (add_le_add_left (show a ≤ x j from h) (v j).val)

include V in
lemma later_frame (x : Sky K) (u : placement Λ) (p : x ∈ D q V₊) (h : 0 ≤ (u j).val) : move K u x ∈ D q V₊ :=
  domain_mono Y H G (even_flank j u (by rwa [zero_add])) (moving Y H V G u x p)

-- clocks unified in `atEstate`. The positive-time mark becomes a genuine
-- moving Hilbert vector on this actual representation.
variable (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "I₀"=> indoor Y H V G.history G.clipped j false C χ
local notation "κ₀" t:max x:max=> bud Y H V t G.history G.clipped j false C χ x
local notation "I₁"=> fort Y H V G.history G.clipped j false C χ
local notation "λp" => OSvector Y H V G j C χ
local notation "Ξ" => atEstate Y H V G.history G.clipped j false C χ
local notation "R" => ride Y H V G.history G.clipped j false C χ

theorem transported_ket (x : Sky (tent Y H)) (h : x ∈ D false V₊)
    (v : placement Λ) (t : 0 ≤ (v j).val) (p : move K v x ∈ D false V₊) :
    OSvector Y H V G j C χ ⟨move K v x,p⟩ = (Ξ v) (λp ⟨x,h⟩) := by
  obtain ⟨s,⟨z,rfl⟩,f,hF,rfl⟩ := ((stamps_eventually v).and ((domain_eventually Y H G).1 h)).exists
  rw [show (⟨move K (stamps Λ s z) _ , p⟩ : D false V₊)=⟨ticket Y H G s (reposition K z f), (move_at Y H V G _ s f z rfl) ▸ p⟩ from Subtype.ext (move_at Y H V G _ s f z rfl),
    field_ticket Y H V G j C χ s _ (show reposition K z f∈ insideAt Λ l K false V₊ s from
      insideAt_mono (even_flank j (stamps Λ s z) (by rwa [zero_add])) (here_cov Y H false V₊ s z f hF)),
    field_ticket Y H V G j C χ s _ hF]
  let g := asField Y H j false s ⟨f,hF⟩
  have hz : 0 ≤ z j := (bell_le M s 0 (z j)).1 (by change 0 ≤ bell M s (z j) at t; unfold bell; simpa [bell] using t)
  have he := apt_rides Y H V s G.history G.clipped j false C χ g z (z j).toNat (Int.toNat_of_nonneg hz)
  change κ₀ s _ = (Ξ (fun k=> notch M s (z k))) (κ₀ s g)
  rw [he]
  apply congrArg (bud Y H V s G.history G.clipped j false C χ)
  let W := aptMoves Y H V s G.history j false C g z (z j).toNat (Int.toNat_of_nonneg hz)
  have hv := congrArg Subtype.val W
  rw [world_val] at hv
  exact Subtype.ext hv.symm

theorem physical_move (x : Sky (tent Y H)) (h : x ∈ D true V₊)
    (v : placement Λ) (t : 0 ≤ (v j).val) (p : move K v x ∈ D true V₊) :
    physicalKet Y H V G j C χ ⟨move K v x,p⟩ = (Ξ v) (physicalKet Y H V G j C χ ⟨x,h⟩) :=
  transported_ket Y H V G j C χ x (domain_loose Y H G V₊ h) v t
    (domain_loose Y H G V₊ p)

namespace TimeMesh
/-- Vertical stamp (and displacement). -/
noncomputable def along (Λ : Preparation) (j : Axis) (s n : ℕ) : placement Λ := stamps Λ s (Pi.single j (n:ℤ))
lemma at_self (s n) : ((along Λ j s n j).val)=(whenly (timeMesh Λ) s n:ℝ) := by
  unfold along; rw [stamps_at, Pi.single_eq_same]; exact natural_time _ _ _
lemma heat (s n : ℕ) : atEstate Y H V G.history G.clipped j false C χ (along Λ j s n) =
    (R).E (whenly (timeMesh Λ) s n) := by
  let f := along Λ j s n
  have hh : (fun k : Trans j=> along Λ j s n k.val)=0 := funext fun k=> by unfold along; rw [stamps_at, Pi.single_eq_of_ne k.property, notch_zero]; rfl
  unfold atEstate; rw [show Real.toNNReal (↑(along Λ j s n j)) = whenly M s n from (by rw [show ↑(along Λ j s n j)=(whenly M s n:ℝ) from at_self ..]; exact Real.toNNReal_coe), hh,Germ.Alliance.raw_zero]; rfl
lemma flank_mono {a b : ℝ} (p : b ≤ a) : flank j a ⊆ flank j b := fun _ h => p.trans h

theorem time_heat (x : Sky (tent Y H)) (p : x ∈ D true V₊) (s n : ℕ) :
    move K (along Λ j s n) x ∈ Domain Y H G true (flank j (whenly (timeMesh Λ) s n)) ∧
    ∀ p1 : move K (along Λ j s n) x ∈ D true V₊,
      (R).E (whenly (timeMesh Λ) s n) (physicalKet Y H V G j C χ ⟨x,p⟩)=
        physicalKet Y H V G j C χ ⟨move K (along Λ j s n) x,p1⟩ := by
  have ht := at_self (Λ:=Λ) j s n
  refine ⟨domain_mono Y H G (even_flank j _ (by rw [ht,zero_add])) (moving Y H V G _ x p),fun p' =>?_⟩
  rw [physical_move Y H V G j C χ _ p (along Λ j s n) (by rw [ht]; positivity),heat]

lemma dense_flanks (a : ℝ) :
    Dense {x : I₀| ∃ (f : Sky (tent Y H)), f∈Domain Y H G true (flank j a) ∧ ∃ p:f∈Domain Y H G true V₊,physicalKet Y H V G j C χ ⟨f,p⟩=x} := by
  obtain ⟨n,h⟩ := exists_nat_gt (a/(mill M 0 : ℝ))
  let t := whenly M 0 n; have hp : a ≤ t := by
    refine ((div_lt_iff₀ (show 0 < (mill M 0:ℝ) from mill_pos M 0)).1 h).le.trans_eq ?_
    simp only [t,whenly]; push_cast; rfl
  apply (((R).whole t).dense_image ((R).E t).continuous (physical_dense Y H V G j C χ)).mono
  rintro _ ⟨x,⟨f,rfl⟩,rfl⟩; let g:= move K (along Λ j 0 n) f.val
  have h := time_heat Y H V G j C χ f.val f.property 0 n
  have hz : g∈Domain Y H G true V₊ := domain_mono Y H G (flank_mono j t.property) h.1
  exact ⟨g,domain_mono Y H G (flank_mono j hp) h.1,hz,(h.2 hz).symm⟩
end TimeMesh

def strictlyPositive (j : Axis) : Set RSpace := {x | 0 < x j}
lemma interior_positive (a : ℝ) (h : 0 < a) : flank j a ⊆ strictlyPositive j := fun _ p=> h.trans_le p
lemma closed_positive : strictlyPositive j ⊆ flank j 0 := fun x h => (show 0 < x j from h).le

noncomputable def positiveKet : Domain Y H G true (strictlyPositive j) →ₗ[ℂ] I₀ :=
  (physicalKet Y H V G j C χ).comp (Submodule.inclusion (domain_mono Y H G (closed_positive j)))

theorem future_dense : DenseRange (positiveKet Y H V G j C χ) := by
  apply (TimeMesh.dense_flanks Y H V G j C χ 1).mono
  rintro _ ⟨f,h,p,rfl⟩
  exact ⟨⟨_,domain_mono Y H G (interior_positive j 1 zero_lt_one) h⟩,rfl⟩

end YM.CF.Buffered.Afterglow.Tower.FirstWindows
