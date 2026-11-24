import YM.CF.BPress.Smooth.Hole
/-! Lipschitz sphere fillings. Uniform clearance -> controlled/still clears that pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Smooth
open Function Metric Filter Set Module MeasureTheory
open scoped Topology NNReal ENNReal ContDiff InnerProductSpace
variable {M : Type} [MetricSpace M]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (v:E)(p:‖v‖=1)
include p in
lemma clear_extend (X : Set M) (x : IsCompact X) (L : ℝ≥0) (ε : ℝ) (e:0<ε):
    ∃ C : ℝ≥0, ∃ δ:ℝ, 0<δ ∧ ∀ S⊆X, S.Nonempty → ∀ f : M→ E, LipschitzOnWith L f S →
      (∀ x∈S, ‖f x‖=1 ∧ ε ≤ dist (f x) v) → ∃ F : M→ E, LipschitzOnWith C F X ∧ EqOn f F S ∧ ∀ x∈X, ‖F x‖=1 ∧ δ ≤ dist (F x) v := by
  letI : ProperSpace E:=FiniteDimensional.proper ℝ _; let A:=sphere (0:E) 1 \ ball v ε
  let k:=stereoToFun v; let T:=(ℝ ∙ v)ᗮ; let l(u:T):= stereoInvFunAux v u.val
  have ha:IsCompact A:= (isCompact_sphere ..).diff isOpen_ball
  obtain ⟨K,h⟩:= lip_near ha (f:=k) (fun x h=> stereo_domain p (by simpa using (show x∈sphere (0:E) 1 from h.1)) (fun t=> h.2 (t.symm ▸ mem_ball_self e)))
  obtain ⟨r,H⟩:= (ha.bddAbove_image h.continuousOn.norm)
  obtain ⟨d,D⟩:= ambient_ext (E:=↥T) x r (K*L)
  letI : ProperSpace (↥T):=FiniteDimensional.proper ℝ _
  let B:= closedBall (0 : ↥T) d
  have he : ContDiff ℝ 1 l:= contDiff_stereoInvFunAux.comp T.subtypeL.contDiff
  obtain ⟨C,t⟩:= lip_near (s:=B) (isCompact_closedBall ..) (fun y _=> he.contDiffAt (x:=y))
  obtain ⟨δ,u,hδ⟩:= compact_positive (s:=B) (isCompact_closedBall ..) (fun x=>dist (l x) v) ((he.continuous.dist continuous_const).continuousOn) (fun x _=> dist_pos.mpr (fun f=> stereoInvFun_ne_north_pole p x (Subtype.ext f)))
  refine ⟨C * (lipschitzExtensionConstant (↥T)*(K*L)),δ,u,?_⟩; intro S hp ne f g R
  have hA: MapsTo f S A:= fun i hi=> ⟨by simpa using (R i hi).1,fun g=> not_lt.mpr (R i hi).2 (mem_ball.mp g)⟩
  obtain ⟨F,hF,W,U⟩:= D S hp ne (k∘f) (h.comp g hA) (fun y t=> H (mem_image_of_mem _ (hA t)))
  have b : MapsTo F X B:= fun y t=> by simpa [B] using U y t
  refine ⟨l∘F,t.comp hF.lipschitzOnWith b,fun y t=>?_, fun i y=>⟨?_, hδ _ (b y)⟩⟩
  · rw [comp_apply, ← W t]; exact congrArg Subtype.val (stereo_left_inv p (x:=⟨f y,(hA t).1⟩) (fun t'=> (hA t).2 ((t'.symm : v=f y) ▸ mem_ball_self e))).symm
  · simpa [comp_apply] using (show l (F i)∈sphere (0:E) 1 from stereoInvFunAux_mem p (F i).property)

include p
lemma sphere_extension {X S : Set M} (x : IsCompact X) (s : IsCompact S) (t:S⊆X) {n : ℕ}
    (e : finrank ℝ E=n+1) (h : dimH S < n) (L:ℝ≥0):
    ∃ C:ℝ≥0, ∀ Z ⊆ S, ∀ f : M → E, LipschitzOnWith L f Z → (∀ i∈Z, ‖f i‖=1) →
       ∃ g : M → E, EqOn f g Z ∧ LipschitzOnWith C g X ∧ ∀ x∈X, ‖g x‖=1 := by
  classical
  obtain ⟨ε,u,p,h⟩:= avoidance v p S s L e h
  choose C δ hc using fun v : sphere (0:E) 1=> clear_extend v.val (by simpa using v.property) X x L ε p
  refine ⟨ u.sup C, fun Z P f g a=>?_⟩
  rcases Z.eq_empty_or_nonempty with i|i; · subst Z; exact ⟨fun _=>v,Set.eqOn_empty ..,(LipschitzWith.const' _).lipschitzOnWith,fun _ _=> ‹‖v‖=1›⟩
  obtain ⟨i,h,t'⟩:= h Z P i f g a; obtain ⟨G,H,U,L⟩:= (hc i).2 Z (P.trans t) ‹Z.Nonempty› f g (fun u t=> ⟨a u t,t' u t⟩)
  exact ⟨G,U,H.weaken (Finset.le_sup (f:=C) h),fun x t=>(L x t).1⟩
end YM.CF.BPress.Smooth
