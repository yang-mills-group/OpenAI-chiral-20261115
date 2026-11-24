import YM.SU5.Reconstruction.Nymph.Steps
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
namespace Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false
open SelectionAnalysis OS.Semigroup
variable (iA:Axis) (R : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped iA false (R iA) →⋆ₐ[ℂ] ℂ)
local notation "P" => D false Set.univ
local notation "ν" => marks (dainty Λ)
local notation "c" j:max => displacement Y H V G.history G.clipped iA false (R iA) χ j (R j)
variable (j:Axis)
local notation "A" => indoor Y H V G.history G.clipped j false (R j) (c j)
local notation "Q" => ride Y H V G.history G.clipped j false (R j) (c j)
local notation "Ξ" => atEstate Y H V G.history G.clipped j false (R j) (c j)
local notation "X" => OSvector Y H V G j (R j) (c j)
local notation "T" => flank j 0
local notation "N" => Domain Y H G false (flank j 0)
local notation "V₀" => turnstile Y H V G.history G.clipped j false (R j) (c j)
local notation "B" i:max p:max => stride (tent Y H) i p
local notation "μ" j1:max => osValue Y H V G j1 (R j1) (c j1)
set_option quotPrecheck false
local notation "Ψ" => osValue Y H V G iA (R iA) χ
local notation "r" => PhaseChoice.SameCharacter.resident Y H V G iA false (R iA) χ
lemma relax_shape (x:ν)(a b:ℝ) (p:b ≤ a+(x:ℝ)) (f:Sky (tent Y H))(h:f∈D q (flank j a)) : (B j x) f∈ D q (flank j b) :=by
  apply domain_mono Y H G _ (stride_region Y H G j x f h); rintro _ ⟨v,h,rfl⟩; apply le_trans p; change a+(x:ℝ) ≤ v j + eject j (x:ℝ) j; rw [eject_at]; exact add_le_add_left (show _ ≤ v j from h) _
lemma pitch_bar {x:ν}(p:0≤ (x:ℝ)) (f: N) : (B j x) f.val ∈ N := relax_shape Y H G j x 0 0 (by simpa using p) f.val f.property
lemma economic (x:ν)(f:Sky (tent Y H))(p:f∈ D q Set.univ): (B j x) f∈D q Set.univ := slides_univ (eject j (x:ℝ)) ▸ stride_region Y H G j x f p
lemma column_cost (x:ν)(f:Domain Y H G false Set.univ) : Ψ ⟨(B j x) f.val,economic Y H G j x _ f.property⟩= Ψ f :=by
  obtain ⟨s,⟨p,h⟩,g,rfl⟩ := ((eventually_toned x).and (eventually_enclosed Y H G f)).exists
  let y:=cruise j (tent Y H) (2*p) g.val
  let z:=economic Y H G j x (enclose Y H G Set.univ false s g).val (enclose Y H G Set.univ false s g).property
  rw [show (⟨(B j x) _,z⟩:P)=⟨ticket Y H G s y,ticket_loose ..⟩ from Subtype.ext (stride_mark Y H G j x s p h g.val),os_ticket_val, os_enclose,← audition_here Y H V G iA R χ]
  exact elect_sold Y H V G j s iA R (r) p g.val.property
local notation "∆₀" => unify Y H V G iA j R χ
lemma time_even (x:ν) (p:0≤ (x:ℝ))(f:N): (Q).E (Real.toNNReal (x:ℝ)) (X f)= X ⟨(B j x) f.val, pitch_bar Y H G j p f⟩ :=by
  apply (∆₀).injective; rw [unify_heat,carries_marks,carries_marks]
  let Z₁:= (SameCharacter.resident Y H V G iA false (R iA) χ); let Δ₁:=engaged Y H V G j false (R j) iA (R iA) Z₁
  let ht := Acting.clock Y H V G j false (R j) Δ₁; let π:=Acting.voice Y H V G j false (R j) Δ₁
  let χ' := appointVector Y H V G iA j R χ
  obtain ⟨s,⟨v,h⟩,f,rfl⟩:= ((eventually_toned x).and (eventually_enclosed Y H G f)).exists
  let α:=asField Y H j false s f; let k:=v.toNat
  have hv: 0≤v:= (bell_le (dainty Λ) s 0 v).1 ((le_of_eq (show bell (dainty Λ) s 0=0 by simp [bell])).trans (by rw [show bell (dainty Λ) s v=x from congrArg Subtype.val h]; exact p)) -- type bind
  have he₀: (x:ℝ) = (pitchMill Λ s (2*k):ℝ):=by rw [←h,← glint_perch,show ((notch (dainty Λ) s v):ℝ)= bell (dainty Λ) s (k:ℤ) from (Int.toNat_of_nonneg hv).symm ▸ rfl]; exact natural_time .. -- cast
  let X₀ : N:= ⟨(B j x) (enclose Y H G (flank j 0) false s f).val,pitch_bar Y H G j p (enclose Y H G _ false s f)⟩
  let b:= bout Y H j false s (2*k) α; let g:= fromField Y H j s b
  have hz : g.val=cruise j K (2*v) f.val:=by
    apply Subtype.ext
    change chime K j ((2*k:ℕ):ℤ) _=chime K j _ _
    rw [Nat.cast_mul,Nat.cast_ofNat,show (k:ℤ)=v from Int.toNat_of_nonneg hv]; rfl
  change ht (Real.toNNReal (x:ℝ)) (χ' _) = χ' X₀
  rw [show X₀= enclose Y H G T false s g from Subtype.ext (show (B j x) (ticket Y H G s f.val) = ticket Y H G s g.val from (stride_mark Y H G j x s v h f.val).trans (congrArg (ticket Y H G s) hz.symm)),he₀,Real.toNNReal_coe]; simp only [χ', appoint_hit]; exact (Acting.read_stride Y H V G j false (R j) s k Δ₁ α).symm

section actor
variable (s : Trans j)
lemma flat_plane (x:ν)(f:Sky (tent Y H))(h:f∈ D q T) : (B s.val x) f∈ D q T :=by
  apply domain_mono Y H G _ (stride_region Y H G s.val x f h); rintro _ ⟨v,h,rfl⟩; change 0≤ v j+eject s.val (x:ℝ) j; simpa [s.property.symm] using (show 0≤v j from h)
noncomputable def glimpse (x:ν) : N→ N:= fun f=>⟨(B s.val x) f.val,flat_plane Y H G j s x f.val f.property⟩
local notation "P'" => glimpse Y H G j s
lemma arrange_even (x:ν) : ∃ T' : indoor Y H V G.history G.clipped j false (R j) (c j) ≃ₗᵢ[ℂ] A,∀ f, T' (X f)=X (P' x f):=by
  have p :=attains_full_axis Y H V G iA j R χ
  have ht(x y:N)(v:ν): flipMark j (tent Y H) (P' v x).val * (P' v y).val= (B s.val v) (flipMark j K x.val*y.val):=by rw [stride_mul,stride_other v s.val j s.property]; rfl
  apply Selected.gram_impl («A»:=indoor Y H V G.history G.clipped j false (R j) (c j)) («B»:=indoor Y H V G.history G.clipped j false (R j) (c j)) (f:=fun f=> X f) (g:=fun f=> X (P' x f)) p _ _
  · apply p.mono; rintro _ ⟨y,rfl⟩; have he:P' x (P' (-x) y)=y:= by apply Subtype.ext; change (B s.val x) ((B s.val (-x)) _) = _; rw [stride_add,add_neg_cancel,stride_zero]
    exact ⟨P' (-x) y,congrArg X he⟩
  intro f g; rw [registered_pair,registered_pair,os_across Y H V G]; symm
  set y : P:=⟨flipMark j (tent Y H) f.val * g.val, paired_forever Y H G j _ _ f.property g.property⟩; -- careful orientation set
  refine Eq.trans (congrArg (Ψ) (show _=(⟨(B s.val x) y.val,economic Y H G s.val x y.val y.property⟩:P) from Subtype.ext (ht f g x))) (column_cost Y H V G iA R χ s.val x y)

noncomputable def bring (x:ν) : indoor Y H V G.history G.clipped j false (R j) (c j) ≃ₗᵢ[ℂ] A := Classical.choose (arrange_even Y H V G iA R χ j s x)
local notation "U" s:max => bring Y H V G iA R χ j s
@[simp] lemma rises_even (x:ν)(f : Domain Y H G false (flank j 0)) : (U s) x (X f)= X (P' x f) := Classical.choose_spec (arrange_even Y H V G iA R χ j s x) f
noncomputable def swinger : Players (marks (dainty Λ)) (indoor Y H V G.history G.clipped j false (R j) (c j)) where
 play x:= ((U s) x).toLinearIsometry.toContinuousLinearMap
 pulls a b:= le_of_eq (((U s) a).norm_map b)
 play_zero:=by
   apply DFunLike.ext'
   apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _) -- last method needs args?
   funext f; exact (rises_even Y H V G iA R χ j s 0 f).trans (congrArg X (Subtype.ext (stride_zero ..)))
 piles v w:=by
   apply DFunLike.ext'
   apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
   funext f
   change (U s) v ((U s) w (X f)) = (U s) (v+w) (X f); rw [rises_even,rises_even,rises_even]; exact congrArg X (Subtype.ext (stride_add ..))
local notation "Ue" s:max=> swinger Y H V G iA R χ j s
lemma swappable (i : Trans j) (v w:ν) : ((Ue s).play v).comp ((Ue i).play w) = ((Ue i).play w).comp ((Ue s).play v):=by
 apply DFunLike.ext'; apply (attains_full_axis Y H V G iA j R χ).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
 funext f; change (U s) v ((U i) w (X f))=(U i) w ((U s) v (X f)); simp only [rises_even]; exact congrArg X (Subtype.ext (stride_cross ..))
noncomputable def outfit : Alliance (Trans j) (marks (dainty Λ)) (indoor Y H V G.history G.clipped j false (R j) (c j)) where
 crew s:=Ue s
 cCom s := fun i => swappable Y H V G iA R χ j s i
end actor

end Nymph
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
