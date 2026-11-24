import GaugeFieldConstruction.SylvanΛL
/-!
 # Real-time Ward stress continuation supplement. Test contours in relative coordinates.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
variable {n:ℕ}(k:Fin n)
abbrev τNearRT (k:Fin n):NearPair (n+1) where
 i := k.castSucc
 j := k.succ
 next := rfl
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "N_τ" => τNearRT k
abbrev remXRT (β: Type*)(v:Fin (n+1)→β) := remΛ k.castSucc v
abbrev addXRT {β:Type*}(v:Fin n→β)(b:β): Fin (n+1)→β:= k.castSucc.insertNth (α:=fun _=> β) b v
@[simp] lemma tNextRT : k.castSucc.succAbove k=ιⱼ:=by simp
lemma insertSelfRT {β:Type*}(v:Fin n→β)(b:β) : addXRT k v b ιⱼ=v k:=by
 change k.castSucc.insertNth _ _ _=_; rw[← tNextRT k, Fin.insertNth_apply_succAbove]
lemma tDiffRT : ιᵢ ≠ ιⱼ:= Fin.ne_of_lt (show (ιᵢ) < _ from Fin.mk_lt_mk.mpr (by simp))
noncomputable def ElevXRt : (E4× Points n)≃L[ℝ] (E4 ×Points n):= LinearEquiv.toContinuousLinearEquiv {
 toFun z:=(z.2 k +z.1,z.2)
 invFun z:=(z.1-z.2 k,z.2)
 left_inv x:=by simp
 right_inv x:=by simp
 map_add' x y:=by ext1; all_goals first|rfl| (change (x.2+y.2) k+(_+_)=(_+_)+(_+_); rw [PiLp.add_apply]; abel)
 map_smul' a x:=by simp [smul_add] }
noncomputable abbrev κMoverRT (k:Fin n) := (ElevXRt k).trans (TulipΛL k.castSucc)
local notation "K_μ" => κMoverRT k
lemma motionKnownRT (x:E4× Points n): K_μ x=points (addXRT k x.2.ofLp (x.2 k+x.1)):=rfl
lemma mosIRt (x:E4× Points n): K_μ x ιᵢ=x.2 k+x.1:=by rw [motionKnownRT]; simp[addXRT]
lemma mosJRt (x:E4× Points n): K_μ x ιⱼ=x.2 k:=by rw [motionKnownRT]; exact insertSelfRT ..
lemma measureIRt : MeasurePreserving K_μ:=by
 apply (measureΛL _).comp; let M(w:Points n)(i:E4):= w k+i
 let T:=fun w: Points n × E4=> (id w.1, M w.1 w.2);
 have h:MeasurePreserving T:= (@MeasurePreserving.id (Points n) _ volume).skew_product (show Measurable fun w:Points n×E4 => M w.1 w.2 by unfold M; fun_prop) (Eventually.of_forall fun w=> (measurePreserving_add_left volume (w k)).map_eq)
 exact (Measure.measurePreserving_swap).comp (h.comp Measure.measurePreserving_swap)
noncomputable def χTestRT (b:Test4): Joint n→L[ℂ] Joint (n+1):=
 let HB:Joint n→L[ℂ] Probe (E4 × Points n):={
    toFun g:= Probe.combine b g
    map_add' g h:=by ext1; simp [mul_add]
    map_smul' a h:=by ext1; simp [mul_left_comm]
    cont:=Probe.normCont.comp (continuous_const.prodMk continuous_id) }
 Probe.along (K_μ).symm ∘L HB
lemma priceIRT (b:Test4)(f:Joint n)(z:E4×Points n): χTestRT k b f (K_μ z)= b z.1 * f z.2:=by
 simp [χTestRT]
lemma priceCompRt (b:Test4)(p:HasCompactSupport ⇑b)(f:Joint n)(h:HasCompactSupport ⇑f): HasCompactSupport ⇑(χTestRT k b f):=by
 change HasCompactSupport ((Probe.combine b f) ∘ (K_μ).symm); exact (Probe.compact_combine p h).comp_homeomorph (K_μ).symm.toHomeomorph
lemma priceWithinRT (b:Test4)(p:tsupport b⊆spacelike)(f:Joint n) : tsupport (χTestRT k b f) ⊆ (N_τ).gap:=by
 let J:=(fun z:Points (n+1) => ((K_μ).symm z).1); have hc:Continuous J:= continuous_fst.comp (K_μ).symm.continuous
 have H:tsupport (χTestRT k b f) ⊆ J ⁻¹' tsupport b:= closure_minimal (by
    rintro z u; obtain ⟨w,rfl⟩:= (K_μ).surjective z; simp only [J,Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]; apply subset_tsupport; intro h; apply u; rw [priceIRT k b f w,show b w.1=0 from h,zero_mul]) ((isClosed_tsupport _).preimage hc)
 intro z h; obtain ⟨w,rfl⟩:= (K_μ).surjective z
 have hp:= H h; simp only [J,Set.mem_preimage,ContinuousLinearEquiv.symm_apply_apply] at hp
 change K_μ w ιⱼ - K_μ w ιᵢ ∈ spacelike
 rw [mosJRt,mosIRt,sub_add_eq_sub_sub,sub_self,zero_sub,lateral,clock_neg, Mink.rest_neg,norm_neg,abs_neg]; exact (lateral _).1 (p hp)
#print axioms measureIRt
end YM.NSF.Boundary
end
