import YM.SU5.Reconstruction.Pitch.Side
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

variable (a:Axis) (C : Arena Y H G.history.circuit a 0 false)
local notation "A"=> Ark.Ht Y H G.history.circuit a 0 false C
local notation "γ"=> Aurora Y H V G.history a false C
local notation "Ω"=> floorV Y H G.history.circuit a 0 false C
local notation "fΨ"=> LightBudget.prepaid Y H V G a C
local notation "F"=> Domain Y H G false (flank a 0)
local notation "τ′" => marks (loomD Λ)
variable (t: marks (loomD Λ))
variable (j:Trans a) (s:ℕ)
local notation "κ" s:max=>actor Y H s G.history.circuit a 0 false C
local notation "F₀" s:max=>Tower.Field Y H s a 0 false
local notation "U" p:max=>unrooted Y H V G a C p j
local notation "U₁" p:max=>beamSwirl Y H V G a C p j
local notation "Π" s:max=> cap Y H V s G.history G.clipped a false C
local notation "Bx" s:max f:max p:max=>boxOp Y H V s G.history G.clipped a false C _ f p
open Finset
variable (v:ℕ)(z:ℤ)(h:notch (loomD Λ) s z=t)(f:Entry Y H s a false v) (w₀:0<v)

noncomputable def lateral : Entry Y H s a false v:=by
 refine ⟨inStep Y H a j s z f.val,?_⟩
 obtain ⟨T,p,q⟩:=f.property
 exact ⟨_,flow_port K j.val z p, fun x u=>by obtain ⟨x,b,rfl⟩:= Finset.mem_image.mp u; rw [moves,if_neg j.property.symm]; exact q x b⟩
local notation "Ξ"=> lateral Y H a j s v z f
include h
lemma beam_box : (U t).toLinearIsometry.toContinuousLinearMap.comp (Bx s f w₀)=(Bx s (Ξ) w₀).comp (U t).toLinearIsometry.toContinuousLinearMap:=by
 apply test_high Y H V s G.history a false C; intro i w x
 let X₀:=furnished Y H s G.history a false v f i w
 change (U t) ((Bx s f w₀) _)= (Bx s (Ξ) w₀) ((U t) _)
 simp only [snatch Y H V s G.history G.clipped a false C v (lateral Y H a j s v z f) w₀ w, snatch Y H V s G.history G.clipped a false C v f w₀ w,
   shiftedActor Y H V G a C t j i (castor (loomD Λ) s i z) ((notch_up (loomD Λ) _ i w z).trans h)]
 apply congrArg _; apply Subtype.ext; let r:=castor (loomD Λ) s i z
 change chime K j.val r (slabT Y H i a false _ X₀ x).val= (slabT Y H i a false _ _ (inStep Y H a j i r x)).val; rw [slab_eq,slab_eq,chime_product]; apply congrArg₂ (·*·)
 · exact (acreage_X Y H G j.val s (i-s) (test_entry Y H s a false f) z).symm
 exact twin_slide j.val a _ _ (field_test Y H i a 0 false x).paid.choose_spec
omit h
local notation "J₀"=>groundRoom Y H V G.history a false C
local notation "Qr"=> (γ).orthogonalProjectionOnto
lemma beam_projection (x:A): (U₁ t) (Qr x)= Qr ((U t) x):=by
 apply ext_inner_left ℂ; intro y
 change inner ℂ (y: (J₀).space) _= _
 -- test y = U symm y
 nth_rw 1 [← (U₁ t).apply_symm_apply y]; rw [LinearIsometryEquiv.inner_map_map,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] -- tune
 change inner ℂ ((U t).symm y.val) _ = _; rw [←LinearIsometryEquiv.inner_map_map (U t), LinearIsometryEquiv.apply_symm_apply]
include h
lemma beam_shifts (k k':observable (tent Y H) false)(p:k'.val=chime K j.val z k.val) : (U₁ t).conjStarAlgEquiv ((Π s) k)=(Π s) k':=by
 obtain ⟨P⟩:= anyporch Y H s a false k
 let X':= lateral Y H a j s P.span z P.fwd
 have hx:X'.val.val=relocate K a P.rise k'.val:=by
    change chime K j.val z P.fwd.val.val = _; rw [P.yes,p]; exact twin_slide j.val a _ _ (marksSpec false k).1.paid.choose_spec
 rw [cap_moved_entry Y H V G a false C s P.span X' k' P.pos P.rise hx,onAny Y H V s G.history G.clipped a false C P]
 ext1 x
 change (U₁ t) (Qr ((Bx s P.fwd P.pos) ((U₁ t).symm x).val))= Qr ((Bx s X' P.pos) x.val)
 rw [beam_projection]
 have ht:=beam_box Y H V G a C t j s P.span z h P.fwd P.pos
 let X: A:= x.val
 change Qr ((U t) ((Bx s P.fwd P.pos) ((U t).symm X)))= Qr ((Bx s X' P.pos) X)
 apply congrArg Qr; exact Eq.trans (DFunLike.congr_fun ht ((U t).symm X)) (congrArg (Bx s X' P.pos) ((U t).apply_symm_apply X))

omit h
lemma vac_swirl : (U₁ t) (seat0 Y H V G.history a false C)= seat0 Y H V G.history a false C:=by
 obtain ⟨s,v,p⟩:= notch_exists (loomD Λ) t
 apply Subtype.ext; change (U t) Ω=Ω; rw [vacua Y H V G.history.circuit a 0 false C s,shiftedActor Y H V G a C t j s v p]; apply congrArg _; exact Subtype.ext (chime_unit K j.val v)
-- generate. To show coLaw EVEN all advances preserve contour by self phase equality; choose only at p=one to build actual Star map. Note `unrooted` projections stronger available all p. Can implement all s using cap height upgrade but don't need.
local notation "Dγ"=> displayAlgebra Y H V G.history G.clipped a false C
local notation "BigZ"=> (U₁ (eyeD Λ)).conjStarAlgEquiv
noncomputable def stripe (J:Calibration) (a:Axis)(z:ℤ)(x:observable J false):observable J false := (asLoose J) (cruise a J z (show Dome J from ⟨x.val,x.property.1⟩))
private lemma turn_mem : displayAlgebra Y H V G.history G.clipped a false C ≤ StarSubalgebra.comap (U₁ (eyeD Λ)).conjStarAlgEquiv.toStarAlgHom (displayAlgebra Y H V G.history G.clipped a false C):=by
 apply StarSubalgebra.topologicalClosure_minimal
 · apply StarAlgebra.adjoin_le; rintro y ⟨⟨s,w⟩,rfl⟩
   change (BigZ ((Π s) w)) ∈ Dγ
   let z:= (Λ.R.L.val:ℤ)^s
   rw [beam_shifts Y H V G a C (eyeD Λ) j s z eyeD_at.symm w (stripe K j.val z w) rfl]; exact cap_displayed Y H V s G.history G.clipped a false C (stripe K j.val z w)
 exact (displayClosed Y H V G.history G.clipped a false C).preimage (show Continuous (U₁ (eyeD Λ)).conjStarAlgEquiv from beam_cont (H₀:=J₀) (U₁ (eyeD Λ)))
where beam_cont {H₀:Hilbert}(u:H₀≃ₗᵢ[ℂ]H₀):Continuous u.conjStarAlgEquiv:=(StarAlgEquiv.isometry u.conjStarAlgEquiv).continuous
noncomputable def turn_cap : (Dγ) →⋆ₐ[ℂ] (Dγ) := (((BigZ).toStarAlgHom).comp ((displayAlgebra Y H V G.history G.clipped a false C).subtype)).codRestrict Dγ (fun x=> turn_mem Y H V G a C j x.property)
lemma turn_takes (f: Marks K false): turn_cap Y H V G a C j (display Y H V s G.history G.clipped a false C f)= display Y H V s G.history G.clipped a false C (stripe K j.val ((Λ.R.L.val:ℤ)^s) f):= Subtype.ext (beam_shifts Y H V G a C (eyeD Λ) j s ((Λ.R.L.val:ℤ)^s) eyeD_at.symm f (stripe K j.val _ f) rfl)
end Pitch
end YM.CF.Buffered.Afterglow.Tower.FirstWindows
