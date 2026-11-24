/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Floats
/-!
 # Plane only group and half turn conjugator. adapt checked starting A13 full Ortho.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.PlaneL
open Matrix Function Set Filter
open Ortho (oneParameter)
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology ContDiff InnerProductSpace
open YM.Work.A13 (plane_eliminates plane_givens motionHom motionHom_injective motionHom_mirror)
private abbrev bandL:=Subgroup.closure {r:Ortho|∃ i j:Axis,i ≠ j ∧ ∃ t,r=oneParameter (Ortho.plane i j) t}
private lemma bandL_le : bandL≤ orbit:= Subgroup.closure_le _|>.2 (by rintro _ ⟨i,j,h,t,rfl⟩; exact paid _ _)
private lemma squash (i : Axis) (v : E4) (s : Finset Axis) (h : i ∉ s) :
    ∃ g ∈ bandL, ∀ j ∈ s, Ortho.move g v j = 0 := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, bandL.one_mem, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨hij, his⟩ := (show i ≠ j ∧ i ∉ s by simpa using h)
    obtain ⟨b, hb, hbs⟩ := ih his
    obtain ⟨t, ht⟩ := plane_eliminates hij (Ortho.move b v)
    let r := Ortho.oneParameter (Ortho.plane i j) t
    have hr : r ∈ bandL := Subgroup.subset_closure (show ∃ _ _ :Axis,_ ∧ ∃ (_:ℝ),_ from ⟨i,j,hij,t,rfl⟩)
    refine ⟨r * b, bandL.mul_mem hr hb, ?_⟩
    intro k hk
    rw [Ortho.move_mul]
    rcases Finset.mem_insert.mp hk with he | hm
    · subst k; exact ht
    have hki : k ≠ i := fun e => his (e ▸ hm)
    have hkj : k ≠ j := fun e => hj (e ▸ hm)
    exact ((plane_givens hij (Ortho.move b v) t).2.2 k hki hkj).trans (hbs k hm)

private lemma align (i : Axis) (v : E4) :
    ∃ g ∈ bandL, ∃ c : ℝ, Ortho.move g v = c • basis i := by
  obtain ⟨g, hg, hall⟩ := squash i v (Finset.univ.erase i) (by simp)
  refine ⟨g, hg, Ortho.move g v i, PiLp.ext ?_⟩
  intro k
  by_cases h : k = i
  · subst k; simp
  simp [h, hall k (by simp [h])]

private lemma reflection_conjugate (i : Axis) {v : E4} (hv : v ≠ 0) :
    ∃ g ∈ bandL,
      motionHom (g⁻¹ * Signed.reflect i * g) = (ℝ ∙ v)ᗮ.reflection := by
  obtain ⟨g, hg, c, hc⟩ := align i v
  refine ⟨g, hg, ?_⟩
  let f := motionHom g
  have he : f v = c • basis i := hc
  have hcn : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv (f.injective (by simpa using he))
  have ht : (ℝ ∙ v)ᗮ.map (f.toLinearEquiv : E4 →ₗ[ℝ] E4) = (ℝ ∙ basis i)ᗮ := by
    rw [Submodule.map_orthogonal_equiv, Submodule.map_span, Set.image_singleton]
    change (ℝ ∙ f v)ᗮ = _
    rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hcn)]
  have hm : (ℝ ∙ basis i)ᗮ.reflection = f.symm.trans ((ℝ ∙ v)ᗮ.reflection.trans f) :=
    (congrArg (fun A : Submodule ℝ E4 => A.reflection) ht.symm).trans
      (Submodule.reflection_map f (ℝ ∙ v)ᗮ)
  rw [map_mul, map_mul, map_inv, motionHom_mirror]
  change f⁻¹ * (ℝ ∙ basis i)ᗮ.reflection * f = (ℝ ∙ v)ᗮ.reflection
  rw [hm]
  apply LinearIsometryEquiv.ext; intro x
  change f.symm (f ((ℝ ∙ v)ᗮ.reflection (f.symm (f x)))) = _
  simp

private lemma sigma2L (i): Jj i * Jj i=1 := Ortho.ext _ _ fun x=> by
  rw [Ortho.move_mul]; ext j
  rw [Signed.mirrored,Ortho.move_one]; split_ifs <;> simp_all [Jj]
private lemma keyPlaneL {i j:Axis}(h:i≠j)(t:ℝ)(b:Axis): let r:= oneParameter (Ortho.plane i j) t; Jj b * r * Jj b = if b=i ∨ b=j then oneParameter (Ortho.plane i j) (-t) else r :=by
 let r:=oneParameter (Ortho.plane i j) t
 apply Ortho.ext
 intro x; ext1 p; rw [Ortho.move_mul,Ortho.move_mul]
 let y:= Ortho.move (Jj b) x
 obtain ⟨d,e,k⟩:=plane_givens h y t
 by_cases l:b=i∨b=j
 · rw [if_pos l]; obtain ⟨f,g,c⟩:= plane_givens h x (-t)
   change Ortho.move (Signed.reflect b) (Ortho.move (oneParameter _ _) y) p=_
   rw [Signed.mirrored]
   by_cases v:p=i
   · subst p; rw [f,d]; rcases l with rfl|rfl <;> simp [y,Jj,h,Ne.symm h] <;> ring
   by_cases w:p=j
   · subst p; rw[g,e]; rcases l with rfl|rfl <;> simp [y,Jj,h,Ne.symm h] <;> ring
   rw [k p v w,c p v w]; rcases l with rfl|rfl <;> simp [v,w,y,Jj]
 rw [if_neg l]; obtain ⟨f,g,c⟩:=plane_givens h x t
 change Ortho.move (Signed.reflect b) (Ortho.move (oneParameter _ _) y) p=_
 rw [Signed.mirrored]
 have ⟨u,z⟩:= not_or.mp l
 by_cases v:p=i
 · subst p; simp [Ne.symm u,Ne.symm z,d,f,y,Jj] -- if simp doesn't use d
 by_cases w:p=j
 · subst p; simp [Ne.symm u,Ne.symm z,e,g,y,Jj]
 rw [k p v w,c p v w]; by_cases a:p=b
 · subst b; simp [y,Jj]
 simp [a,y,Jj]
private lemma keyBandL {r:Ortho}(h:r∈ bandL)(b:Axis): Jj b * r * Jj b∈ bandL:=by
 have v:Jj b = (Jj b)⁻¹:= (inv_eq_of_mul_eq_one_right (sigma2L b)).symm
 apply Subgroup.closure_induction (p:=fun r _=> Jj b*r*Jj b∈bandL) _ _ _ _ h
 · rintro _ ⟨i,j,h,t,rfl⟩
   rw [keyPlaneL h]; split_ifs<;> exact Subgroup.subset_closure (show ∃ _ _:Axis,_ ∧ ∃ _:ℝ, _ from ⟨i,j,h,_,rfl⟩)
 · rw[mul_one,sigma2L]; simp
 · intro x y _ _ u w; rw [show Jj b*(x*y)*Jj b=(Jj b*x*Jj b)*(Jj b*y*Jj b) from by simp only [mul_assoc]; rw[←mul_assoc (Jj b) (Jj b),sigma2L,one_mul]]; exact bandL.mul_mem u w
 intro x _ p; rw[show Jj b*x⁻¹ * Jj b=(Jj b*x*Jj b)⁻¹ from by simp only [_root_.mul_inv_rev,←v]; group]; exact bandL.inv_mem p
private def WingL (s:Ortho) := s∈ bandL ∨ s*Jp∈bandL
private lemma fly {s t} (p:WingL s) (q:WingL t): WingL (s*t) := by
  have h:= sigma2L timeAxis
  rcases p with p|p <;> rcases q with q|q
  · exact Or.inl (bandL.mul_mem p q)
  · apply Or.inr; rw [mul_assoc]; exact bandL.mul_mem p q
  · apply Or.inr
    have ht:= bandL.mul_mem p ((show Jp*t*Jp⁻¹∈bandL by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; exact keyBandL q _))
    rw [show s * Jp * (Jp*t*Jp⁻¹)=(s*t)*Jp by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; simp only [mul_assoc]; rw [← mul_assoc Jp Jp,h]; simp [mul_assoc]] at ht; exact ht
  apply Or.inl
  have ht:= bandL.mul_mem p ((show Jp*(t*Jp)*Jp⁻¹∈bandL by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; exact keyBandL q _))
  rw [show s*Jp * (Jp*(t*Jp)*Jp⁻¹)=s*t by rw [show Jp⁻¹=Jp from inv_eq_of_mul_eq_one_right h]; simp only [mul_assoc]; rw [h,← mul_assoc Jp Jp,h]; simp] at ht; exact ht
private def airL : Subgroup Ortho where
 carrier:= {s|WingL s}
 mul_mem':=fly
 one_mem':= Or.inl bandL.one_mem
 inv_mem':=fun {s} h=>by
    obtain h|h:=h
    · exact Or.inl (bandL.inv_mem h)
    apply Or.inr
    have hp:= keyBandL (bandL.inv_mem h) timeAxis
    change Jp*(s*Jp)⁻¹*Jp∈bandL at hp
    rwa [_root_.mul_inv_rev,←mul_assoc Jp Jp⁻¹, mul_inv_cancel,one_mul] at hp
private lemma reflection_mem (v : E4) :
    (ℝ ∙ v)ᗮ.reflection ∈ airL.map motionHom := by
  by_cases hv : v = 0
  · subst v
    have he : (ℝ ∙ (0 : E4))ᗮ.reflection = 1 := by
      apply LinearIsometryEquiv.ext; intro x
      apply Submodule.reflection_mem_subspace_eq_self
      simp
    rw [he]; exact Subgroup.one_mem _
  obtain ⟨g, hg, he⟩ := reflection_conjugate timeAxis hv
  have hr : Signed.reflect timeAxis ∈ airL := Or.inr (by change Jp*Jp∈bandL; rw [sigma2L]; simp)
  have hm:g∈ airL:= Or.inl hg
  exact Subgroup.mem_map.mpr ⟨_, airL.mul_mem (airL.mul_mem (airL.inv_mem hm) hr) hm, he⟩
private lemma coveredL (x:SO): x.val∈ bandL:=by
 have he: x.val ∈ airL:=by
    have h : ⊤ ≤ airL.map motionHom := by
       rw [← LinearIsometryEquiv.reflections_generate]
       apply (Subgroup.closure_le _).mpr
       rintro r ⟨v, rfl⟩; exact reflection_mem v
    obtain ⟨b,hb,he⟩:=Subgroup.mem_map.mp (h (Subgroup.mem_top (motionHom x.val)))
    rwa[← motionHom_injective he]
 rcases he with he|he
 · exact he
 have H:=detained (bandL_le he); change (x.val.val*Jp.val).det=_ at H
 rw [det_mul,detained x.property,one_mul, show Jp.val.det= -1 by dsimp only [Jp,Jj,Signed.reflect]; rw [parity (Signed.mirror timeAxis)]; simp] at H; norm_num at H
abbrev Ψ (i j:Axis)(t:ℝ):SO:= Angles.rise (Ortho.plane i j) t
theorem solarL (x:SO){p:SO→ Prop}(H:∀ i j t,i≠j→ p (Ψ i j t))(h:p 1)(m:∀ s t,p s→p t→p (s*t))(v:∀ s,p s → p s⁻¹): p x:=by
 apply Subgroup.closure_induction (p:=fun x h=> p ⟨x,bandL_le h⟩) _ _ _ _ (coveredL x)
 · rintro _ ⟨i,j,h,t,rfl⟩; exact H _ _ _ h
 · exact h
 · intro x y hx hy w u; exact m ⟨x,_⟩ ⟨y,_⟩ w u
 intro x hx e; exact v ⟨x,_⟩ e
/-- square via two distinct coordinate reflections neither l. --/
abbrev QκL (i k:Axis):SO:= signMot (Signed.mirror i * Signed.mirror k) (by simp [signBit_mul])
lemma hemiKeyL(i k:Axis): (QκL i k).val= Jj i*Jj k := Signed.inclusionO.map_mul ..
lemma doorSphereL {i j k:Axis}(q:i≠j)(v:k≠i)(w:k≠j)(t:ℝ): QκL i k * (Ψ i j t * QκL i k) = Ψ i j (-t) :=by
 let r:=oneParameter (Ortho.plane i j) t
 apply Subtype.ext; change (QκL i k).val * ((Ψ i j t).val * (QκL i k).val)=_
 rw [hemiKeyL]
 have pe:Jj i * Jj k = Jj k * Jj i:=by apply Ortho.ext; intro x; rw[Ortho.move_mul,Ortho.move_mul]; ext y; rw [Signed.mirrored,Signed.mirrored]; by_cases z:y=k<;> by_cases d:y=i<;> simp_all [Jj] -- tune
 nth_rw 2 [pe]; change Jj i*Jj k* (r*(Jj k*Jj i))=_
 rw [show Jj i*Jj k*(r*(Jj k*Jj i))= Jj i*(Jj k*r*Jj k)*Jj i from by group,show Jj k*r*Jj k=r from (keyPlaneL q t k).trans (if_neg (not_or.mpr ⟨v,w⟩))]; exact (keyPlaneL q t i).trans (if_pos (Or.inl rfl)) -- tune
lemma dreamSphereL (i j:Axis)(t u:ℝ): Ψ i j t * Ψ i j u= Ψ i j (t+u):= Subtype.ext ((parameter_add _ _ _).symm)
lemma basicSphereL(i j:Axis): Ψ i j 0=1:= Subtype.ext (YM.Work.A13.oneParameter_zero _)
#print axioms solarL
#print axioms doorSphereL
end YM.GaugeFieldConstruction.Stage.PlaneL
