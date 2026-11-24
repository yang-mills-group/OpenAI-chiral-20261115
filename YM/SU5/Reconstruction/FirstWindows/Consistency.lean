import YM.SU5.Reconstruction.FirstWindows.MovingKets
/-!
# Reconciliation of the selected-vacuum Hilbert constructions (per axis)

No extra equality purchase on panels. The two different algorithms for
transferring one character at time axis base to other coordinate axes
(`engaged` used in Appointment, `displacement` used in Glasshouse) give
on EACH SAME axis the same Hilbert space theory (unitary carrying test vectors,
clocks, spatial shifts and generators for the corresponding slab algebras).
Use with `Marks, Appointment`. In particular time roots (hence ALL times)
and spectral sign convention are the same. (Using an argument by analytic
continuation on the *entire* spaces, no continuity of other coordinates.)
This does NOT yet give an intertwiner of the different axes' theories.
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
open SlabMark MeshClock PhaseChoice
variable (j0 j : Axis) (R : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (χ : displayAlgebra Y H V G.history G.clipped j0 false (R j0) →⋆ₐ[ℂ] ℂ)
set_option quotPrecheck false
local notation "C₁" => R j0
local notation "C" => R j
local notation "x" => SameCharacter.resident Y H V G j0 false (R j0) χ
local notation "c₂" => Selected.displacement Y H V G.history G.clipped j0 false (R j0) χ j (R j)
local notation "Δ" => engaged Y H V G j false (R j) j0 (R j0) (SameCharacter.resident Y H V G j0 false (R j0) χ)
local notation "VB" => (Δ).space
local notation "A" => indoor Y H V G.history G.clipped j false (R j) c₂
local notation "D" => Domain Y H G false (flank j 0)
local notation "γ" s:max => Acting.voice Y H V G j false C Δ s
local notation "π" s:max=> bud Y H V s G.history G.clipped j false (R j) c₂
local notation "Ω₁" => OSvector Y H V G j (R j) c₂
local notation "Ξ" => ride Y H V G.history G.clipped j false (R j) c₂
local notation "ℛ" => Acting.clock Y H V G j false C Δ

noncomputable def appointVector : Domain Y H G false (flank j 0) →ₗ[ℂ] (Δ).space :=
  assemble Y H G (flank j 0) false (fun s => (γ s).comp (asField Y H j false s)) (fun s t h f =>
    Acting.climbs Y H V G j false (R j) Δ s (asField Y H j false s f) t h)

local notation "W" => appointVector Y H V G j0 j R χ

@[simp] theorem appoint_hit (s : ℕ) (f : insideAt Λ l K false (flank j 0) s) :
    W (enclose Y H G (flank j 0) false s f)= (γ s) (asField Y H j false s f) := assemble_enclose ..

lemma choirForm (s : ℕ) (f g : Tower.Field Y H s j 0 false) :
    inner ℂ ((π s) f) ((π s) g)=inner ℂ ((γ s) f) ((γ s) g) := by
  let a (z : Tower.Field Y H s j 0 false) := futureMark Y H s j false z
  let h := mirrorInMarks Y H j false (a f)*a g
  rw [earns,engaged_form Y H V G j false (R j) j0 (R j0) x s f g h rfl,
    SameCharacter.sameReading,across_response]

lemma appoint_form (f g : D) : inner ℂ (Ω₁ f) (Ω₁ g)=inner ℂ (W f) (W g) := by
  obtain ⟨s,⟨v,rfl⟩,w,rfl⟩ := ((eventually_enclosed Y H G f).and (eventually_enclosed Y H G g)).exists
  rw [appoint_hit,appoint_hit,OSvector_enclose,OSvector_enclose]
  exact choirForm ..

lemma attains_appointment : DenseRange (appointVector Y H V G j0 j R χ) := by
  apply (Acting.densely Y H V G j false (R j) Δ).mono
  intro z p; obtain ⟨s,h⟩ := mem_iUnion.mp p; obtain ⟨f,rfl⟩ := h
  exact ⟨enclose Y H G (flank j 0) false s (fromField Y H j s f), appoint_hit Y H V G j0 j R χ s (fromField Y H j s f)⟩

lemma attains_full_axis : DenseRange (OSvector Y H V G j (R j) c₂) := by
  apply (physical_dense Y H V G j (R j) c₂).mono
  rintro _ ⟨f,rfl⟩; exact ⟨⟨f.val,domain_loose Y H G _ f.property⟩,rfl⟩

lemma reach : ∃ X : indoor Y H V G.history G.clipped j false (R j) c₂ ≃ₗᵢ[ℂ] (Δ).space,
    ∀ w, X (Ω₁ w)= W w := Selected.gram_impl («A»:=indoor Y H V G.history G.clipped j false (R j) c₂) («B»:=VB)
    (attains_full_axis Y H V G j0 j R χ) (attains_appointment Y H V G j0 j R χ) (appoint_form Y H V G j0 j R χ)

noncomputable def unify : indoor Y H V G.history G.clipped j false (R j) c₂ ≃ₗᵢ[ℂ] (Δ).space :=
  (reach Y H V G j0 j R χ).choose

local notation "X" => unify Y H V G j0 j R χ

@[simp] theorem carries_marks (z:D) : X (Ω₁ z) = W z := (reach Y H V G j0 j R χ).choose_spec z
lemma carries_buds (s : ℕ) (f : Tower.Field Y H s j 0 false) : X ((π s) f)=(γ s) f := by
  have h := carries_marks Y H V G j0 j R χ (enclose Y H G (flank j 0) false s (fromField Y H j s f))
  rw [OSvector_enclose,appoint_hit] at h; exact h
@[simp] theorem unifies_vacuum : X (doorstep Y H V G.history G.clipped j false C c₂)=(Δ).ground := by
  rw [← Selected.root Y H V 0 G.history G.clipped j false C c₂, carries_buds,Acting.unison]

-- Agreement on all clocks, not just τ at height0. Later compare to the
-- ambitious continuum targets on either of these.
lemma unifies_mesh (s n : ℕ) (z : A) :
    X ((Ξ).E (whenly (timeMesh Λ) s n) z)= ℛ (whenly (timeMesh Λ) s n) (X z) := by
  apply congrFun (a:=z) ((attains_full_axis Y H V G j0 j R χ).equalizer
    ((X).continuous.comp ((Ξ).E (whenly (timeMesh Λ) s n)).continuous)
    ((ℛ (whenly (timeMesh Λ) s n)).continuous.comp (X).continuous) _)
  funext f
  obtain ⟨t,⟨p,rfl⟩,h⟩ := ((eventually_enclosed Y H G f).and (eventually_ge_atTop s)).exists
  let q := asField Y H j false t p
  let y : ℕ := Λ.R.L.val^(t-s)*n; let A' := whenly (timeMesh Λ) t y
  have ht : whenly (timeMesh Λ) s n= A' := ?_
  · dsimp only [Function.comp_apply]
    rw [OSvector_enclose, ht]
    change X ((Ξ).E A' ((π t) _))= ℛ A' (X ((π t) _))
    unfold A'; rw [ride_ticks, carries_buds,carries_buds,Acting.clock_voice]
  -- cast
  exact (MeshClock.matchR (timeMesh Λ) s t n h).symm

lemma unify_heat (a:ℝ≥0) (z:A) : X ((Ξ).E a z)=ℛ a (X z) := by
  suffices h : (fun a:ℝ≥0=> X ((Ξ).E a z))=(fun a=> ℛ a (X z)) from congrFun h a
  apply (MeshClock.fills (timeMesh Λ)).denseRange_val.equalizer
    ((X).continuous.comp ((Ξ).continuousE z)) ((Δ).price_every Y H V G j false (R j) (X z))
  funext v; obtain ⟨s,t,e⟩ := MeshClock.split _ v.property
  dsimp only [Function.comp_apply]; rw [← e]; exact unifies_mesh ..

lemma unify_spatial (a : Trans j) (p : marks (timeMesh Λ)) (z : indoor Y H V G.history G.clipped j false (R j) c₂) :
    X ((turnstile Y H V G.history G.clipped j false C c₂ |>.crew a).play p z)=
      Acting.lattice Y H V G j false C Δ a p (X z) := by
  obtain ⟨s,u,rfl⟩ := notch_exists (timeMesh Λ) p
  apply congrFun (a:=z) ((attains_full_axis Y H V G j0 j R χ).equalizer
    ((X).continuous.comp (ContinuousLinearMap.continuous _))
    ((ContinuousLinearMap.continuous _).comp (X).continuous) _)
  funext w; obtain ⟨t,h,⟨p,rfl⟩⟩ := ((eventually_ge_atTop s).and (eventually_enclosed Y H G w)).exists
  dsimp only [Function.comp_apply]; rw [OSvector_enclose,← notch_up (timeMesh Λ) s t h,turnstile_in,
    carries_buds,carries_buds,Acting.space_voice]

lemma unify_slab (s w:ℕ)(f:Entry Y H s j false w)(p:0<w)(z:A) :
    X (procession Y H V G.history G.clipped j false C c₂ (entrance Y H V s G.history G.clipped j false C f p) z)=
      Acting.watches Y H V G j false C Δ s w f p (X z) := by
  apply congrFun (a:=z) ((attains_full_axis Y H V G j0 j R χ).equalizer
    ((X).continuous.comp (ContinuousLinearMap.continuous _))
    ((ContinuousLinearMap.continuous _).comp (X).continuous) _)
  funext a; obtain ⟨t,⟨a,rfl⟩,h⟩ := ((eventually_enclosed Y H G a).and (eventually_ge_atTop s)).exists
  dsimp only [Function.comp_apply]; rw [OSvector_enclose,slot_high _ _ _ _ _ _ _ _ _ _ f p t h,carries_buds,carries_buds,
    Acting.same_box Y H V G j false C Δ _ h,Acting.act_voice]


section analytic
open OS.Semigroup
local notation "FI" => Acting.halfSpaceFunction Y H V G j false C Δ
local notation "MJ" => Acting.unitaryTime Y H V G j false C Δ
lemma unifies_interior (a : ℂ) (p : 0 < a.im) (v : A) :
    X ((Ξ).F (-Complex.I*a) v) = FI a (X v) := by
  let G₀ := {z:ℂ|0<z.im}
  let f (z:ℂ) := ((Ξ).F (-Complex.I*z)) v
  let g (z:ℂ) := FI z (X v)
  have hh : AnalyticOnNhd ℂ f G₀ := fun i h=>
    ((ContinuousLinearMap.apply ℂ (A).space v).analyticAt _).comp
      ((Selected.ride_anal Y H V G.history G.clipped j false C c₂) i h)
  have ht : AnalyticOnNhd ℂ g G₀ := fun i h=>
    ((ContinuousLinearMap.apply ℂ (VB).space (X v)).analyticAt _).comp (Acting.linker_analytic Y H V G j false (R j) Δ i h)
  have hp : AnalyticOnNhd ℂ (X ∘ f) G₀ := fun i h=>
    ((X).toLinearIsometry.toContinuousLinearMap.analyticAt _).comp (hh i h)
  let F' (t : ℝ≥0) := (t:ℝ)*Complex.I
  have he (t : ℝ≥0) (q : 0<t) : X (f (F' t))= g (F' t) := by
    have h: -Complex.I * F' t=duration t:= by simp [duration,F',mul_comm _ Complex.I, ←mul_assoc]
    unfold f g F'; unfold F' at h
    rw [Acting.linker_at Y H V G j false (R j) Δ q,h,(Ξ).roots_heat q,unify_heat]
  refine hp.eqOn_of_preconnected_of_frequently_eq ht (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0 |>.isPreconnected) (z₀:=F' 1) (by simp [G₀,F']) ?_ p
  intro h
  -- approach along dense real ray from interior
  have hw:Tendsto F' (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (F' 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (show Continuous F' from by unfold F'; fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with i hi
    intro w; apply (mem_Ioi.mp hi).ne'; apply NNReal.coe_injective
    simpa [F'] using congrArg Complex.im (show F' i=F' 1 from w)
  obtain ⟨k,v,q⟩ := ((hw.eventually h).and self_mem_nhdsWithin).exists
  exact v (he k (zero_lt_one.trans (mem_Ioi.mp q)))

lemma unifies_real_time (t : ℝ) (v : A) : X ((Ξ).edge t v)= MJ t (X v) := by
  apply congrFun (a:=v) (((Ξ).whole 1).equalizer
    ((X).continuous.comp ((Ξ).edge t).continuous)
    ((MJ t).continuous.comp (X).continuous) _)
  funext w; dsimp only [Function.comp_apply]; rw [unify_heat,(Ξ).high]
  let a : ℂ := (t:ℂ)+(↑(1:ℝ≥0):ℝ)*Complex.I
  rw [show duration 1+sideways t = -Complex.I*a by apply Complex.ext <;> simp [duration,sideways,a], unifies_interior Y H V G j0 j R χ a (show 0<a.im by simp [a])]
  unfold a; rw [Acting.linked Y H V G j false (R j) Δ zero_lt_one, mul_apply_eq_comp]
end analytic
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
