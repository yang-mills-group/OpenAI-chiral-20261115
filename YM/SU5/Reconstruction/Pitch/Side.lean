import YM.SU5.Reconstruction.Pitch.Grid
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
namespace Pitch
open Nymph
open SlabMark MeshClock PhaseChoice Chambers Germ
variable {J : Calibration} {y w : Set RSpace} {q : Bool}
local notation "L" => Λ.R.L
local notation "D" => Domain Y H G
set_option quotPrecheck false

-- root genuine shift in lateral instrument. This DOESN'T preselect another Receipt. Use unselected exact grammar as requested.
variable (a:Axis) (C : Arena Y H G.history.circuit a 0 false)
local notation "A"=> Ark.Ht Y H G.history.circuit a 0 false C
local notation "γ"=> Aurora Y H V G.history a false C
local notation "Ω"=> floorV Y H G.history.circuit a 0 false C
local notation "fΨ"=> LightBudget.prepaid Y H V G a C
local notation "F"=> Domain Y H G false (flank a 0)
local notation "τ′" => marks (loomD Λ)
variable (t: marks (loomD Λ))

lemma prior_invariant (x:Domain Y H G false Set.univ): courseValue Y H V G (plusLaw Y H G a t x)=courseValue Y H V G x:=by
 obtain ⟨s,⟨v,h⟩,f,rfl⟩:= ((eventually_pitched t).and (eventually_enclosed Y H G x)).exists
 let y:=cruise a K v f.val
 let X':= enclose Y H G Set.univ false s f
 rw [show plusLaw Y H G a t (enclose Y H G Set.univ false s f)=⟨ticket Y H G s y,ticket_loose ..⟩ from Subtype.ext (trek_mark Y H G a t s v h f.val),course_ticket_val]
 rw [course_enclose]; exact shift_eFull Y H V a f.val.property v
variable (j:Trans a)
noncomputable def bystander (a:Axis)(t:τ′)(j:Trans a) : Domain Y H G false (flank a 0) →ₗ[ℂ] Domain Y H G false (flank a 0) where
 toFun f:=⟨trek K j.val t f.val,spectator_play Y H G t a j.val j.property.symm _ _ f.property⟩
 map_add' f g:=Subtype.ext (map_add (trek K j.val t) f.val g.val)
 map_smul' k f:=Subtype.ext (map_smul (trek K j.val t) k f.val)
local notation "ST" t:max=> bystander Y H G a t j
lemma nonzeal : ∃ T: (Ark.Ht Y H G.history.circuit a 0 false C)≃ₗᵢ[ℂ] (Ark.Ht Y H G.history.circuit a 0 false C),∀ f, T (fΨ f)=fΨ ((ST t) f):=by
 have h:DenseRange fΨ:= by
    apply (LightBudget.advance_dense Y H V G a C 0).mono; rintro x ⟨v,_,_,b,rfl⟩; exact Set.mem_range_self (i:= (⟨v,b⟩:F))
 refine Selected.gram_impl («A»:=A) (B:=A) h ?_ ?_
 · apply h.mono; rintro _ ⟨x,rfl⟩; refine ⟨(ST (-t)) x,?_⟩; apply congrArg (fΨ); apply Subtype.ext; change trek K j.val t (trek K j.val (-t) x.val)= _; rw [trek_add,add_neg_cancel,trek_zero]
 intro f g; rw [LightBudget.initial_pair,LightBudget.initial_pair]; symm
 refine Eq.trans (congrArg (courseValue Y H V G) ?_) (prior_invariant Y H V G j.val t ⟨_,paired_forever Y H G a _ _ f.property g.property⟩)
 apply Subtype.ext; change flipMark a K (trek K j.val t f.val)* (trek K j.val t g.val)= trek K j.val t _; rw [trek_mul,trek_other t j.val a j.property]
noncomputable def unrooted : (Ark.Ht Y H G.history.circuit a 0 false C) ≃ₗᵢ[ℂ] (Ark.Ht Y H G.history.circuit a 0 false C) := Classical.choose (nonzeal Y H V G a C t j)
local notation "U" p:max=>unrooted Y H V G a C p j
lemma staysRoot (f: F) : (U t) (fΨ f)= fΨ ((ST t) f):= Classical.choose_spec (nonzeal Y H V G a C t j) f
lemma slidesBack (f:A): (U t).symm f= (U (-t)) f:=by
 suffices h : ⇑(((U (-t))).trans (U t))=id from ((U t).injective (by rw [LinearIsometryEquiv.apply_symm_apply]; exact (congrFun h f).symm))
 have h:DenseRange fΨ:= by
    apply (LightBudget.advance_dense Y H V G a C 0).mono; rintro x ⟨v,_,_,b,rfl⟩; exact Set.mem_range_self (i:= (⟨v,b⟩:F))
 refine h.equalizer (LinearIsometryEquiv.continuous _) continuous_id ?_; funext x; change (U t) ((U (-t)) (fΨ x)) = _; rw [staysRoot,staysRoot]; apply congrArg (fΨ); apply Subtype.ext; change trek K j.val t (trek K j.val (-t) x.val)= _; rw [trek_add,add_neg_cancel,trek_zero]
open Finset
variable (s:ℕ)
local notation "κ" s:max => actor Y H s G.history.circuit a 0 false C
local notation "F₀" s:max=> Tower.Field Y H s a 0 false
lemma side_allowed {Kt:Finset Cover} (z:ℤ)(p:Tower.region a (meshface (Λ:=Λ) 0 s) (tent Y H).ℓ Kt): Tower.region a (meshface (Λ:=Λ) 0 s) (K).ℓ (address j.val z Kt):=by
 intro i k; obtain ⟨y,b,rfl⟩:= Finset.mem_image.mp k; rw [moves,if_neg j.property.symm]; exact p y b
noncomputable def inStep (z:ℤ)(f:Tower.Field Y H s a 0 false): Tower.Field Y H s a 0 false:=by
 refine ⟨chime K j.val z f.val,(purpose_ok ..).2 ⟨?_,nofun⟩⟩
 obtain ⟨Kt,b,v⟩:= ((purpose_ok ..).1 f.property).1
 exact ⟨_,flow_port K j.val _ b,side_allowed Y H a j s z v⟩
lemma shiftedActor (z:ℤ)(h: notch (loomD Λ) s z=t)(f: F₀ s): (U t) ((κ s) f)=(κ s) (inStep Y H a j s z f):=by
 have he(f:F₀ s) : LightBudget.prepaid Y H V G a C (enclose Y H G (flank a 0) false s (fromField Y H a s f))=(κ s) f:=by rw [LightBudget.prepaid_enclose,as_fromField]
 rw [←he, staysRoot, ←he]; apply congrArg (fΨ); apply Subtype.ext; change trek K j.val t (ticket Y H G s _) = ticket Y H G s _; rw [trek_mark Y H G j.val t s z h]; rfl
local notation "E₁"=> advance Y H V G.history.circuit a 0 false C
local notation "Ut"=> (U t).toLinearIsometry.toContinuousLinearMap
private lemma rise_reset (k:ℕ) : Commute (U t).toLinearIsometry.toContinuousLinearMap (advance Y H V G.history.circuit a 0 false C (whenly (timeMesh Λ) s k)):=by
 obtain ⟨r,v,z,h⟩:= ((eventually_ge_atTop s).and (eventually_pitched t)).exists
 apply test_high Y H V r G.history a false C; intro i w f
 change (U t) (advance Y H V G.history.circuit a 0 false C _ ((κ i) f)) = E₁ _ ((U t) ((κ i) f)); rw [advance_at]
 simp only [limited_time Y H V s G.history.circuit a 0 false C (2*k) (v.trans w),shiftedActor Y H V G a C t j i (castor (loomD Λ) r i z) ((notch_up (loomD Λ) r i w z).trans h)]
 exact congrArg (κ i) (Subtype.ext (twin_slide j.val a _ _ (field_test Y H i a 0 false f).paid.choose_spec))
private lemma rise_shift (l':Trans a)(z:ℤ): Commute (U t).toLinearIsometry.toContinuousLinearMap (shiftStamp Y H V G.history G.clipped a false C l' (notch (timeMesh Λ) s z)).val :=by
 obtain ⟨r,v,z',h⟩:= ((eventually_ge_atTop s).and (eventually_pitched t)).exists
 apply test_high Y H V r G.history a false C; intro i w f
 let g:= ((ladder Y H V G.history.circuit a 0 false C).crew l').play
 change (U t) (((ladder Y H V G.history.circuit a 0 false C).crew l').play _ ((κ i) f)) = g _ ((U t) ((κ i) f)); unfold g; rw [on_ladder]
 simp only [sailV_at Y H V s G.history.circuit a 0 false l'.val l'.property C (2*z) i (v.trans w),shiftedActor Y H V G a C t j i (castor (loomD Λ) r i z') ((notch_up (loomD Λ) r i w z').trans h)]
 exact congrArg (κ i) (Subtype.ext (twin_slide j.val l'.val _ _ (field_test Y H i a 0 false f).paid.choose_spec))
lemma commutesBeam (n:ℕ): Commute (U t).toLinearIsometry.toContinuousLinearMap (traveller Y H V G.history G.clipped a false C n).val :=by
 cases h: rolodex a n with
 | inl v=>rw [traveller, comp_apply,h]; exact rise_reset Y H V G a C t j v.1 v.2
 | inr v=>rw [traveller,comp_apply,h]; exact rise_shift Y H V G a C t j v.2.1 v.1 v.2.2
lemma inhabitsBeam (x:A)(p:x∈ γ): (U t) x∈ γ:=by
 apply (in_flight Y H V G.history G.clipped a false C).1; intro n
 have h:= DFunLike.congr_fun (commutesBeam Y H V G a C t j n).eq x
 change (U t) ((traveller Y H V G.history G.clipped a false C n).val x)=(traveller Y H V G.history G.clipped a false C n).val ((U t) x) at h
 rw [(in_flight Y H V G.history G.clipped a false C).2 p n] at h; exact h.symm
local notation "J₀"=>groundRoom Y H V G.history a false C
noncomputable def beamSwirl : groundRoom Y H V G.history a false C ≃ₗᵢ[ℂ] groundRoom Y H V G.history a false C where
 toFun x:=⟨(U t) x.val,inhabitsBeam Y H V G a C t j x.val x.property⟩
 invFun x:=⟨(U t).symm x.val,by rw [slidesBack]; exact inhabitsBeam Y H V G a C (-t) j _ x.property⟩
 left_inv _:= Subtype.ext ((U t).left_inv _)
 right_inv _:= Subtype.ext ((U t).right_inv _)
 map_add' x y:= Subtype.ext (map_add (U t) x.val y.val)
 map_smul' r x:= Subtype.ext (map_smul (U t) r x.val)
 norm_map' x:=(U t).norm_map x.val
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
