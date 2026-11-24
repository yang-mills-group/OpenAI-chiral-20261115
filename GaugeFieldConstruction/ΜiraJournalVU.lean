import GaugeFieldConstruction.StyriaRel.YM.Next.ROTATIONS.Mass
/-!
 Extra arbitrary-parity and non-even receipts for the M estimate. Here as through
 WardPikesMars we are on widths R=exp(n) fixed profile, all constants may be nonuniform
 on the profiles and on the width powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Word OS Ward
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace Matrix.Norms.Frobenius
noncomputable abbrev ReflVU (f : Profile) := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (LinearIsometryEquiv.neg ℝ (E:=ℝ)).toContinuousLinearEquiv f -- tune
lemma reflAtVU (f : Profile)(t): ReflVU f t=f (-t):= rfl
lemma reflEndsVU (f : Profile)(h: Ends f): Ends (ReflVU f):= (show HasCompactSupport ⇑f from h).comp_homeomorph (LinearIsometryEquiv.neg ℝ (E:=ℝ)).toHomeomorph
lemma reflFarVU (f: Profile)(h: Far f): Far (ReflVU f):=by
 refine ⟨reflEndsVU f h.1,?_⟩
 exact h.2.comp_tendsto (show Tendsto (fun t:ℝ=>-t) (𝓝 0) (𝓝 0) from by simpa using continuous_neg.tendsto (0:ℝ)) -- tune
abbrev modeSignVU (b: Bool):ℝ:=if b then -1 else 1
noncomputable abbrev modeSelVU (b:Bool)(f: Profile):Profile:= (2:ℝ)⁻¹ • (f + modeSignVU b • ReflVU f)
lemma modeEndsVU {f: Profile} (h: Ends f) (b): Ends (modeSelVU b f):=(h.add ((reflEndsVU f h).scale _)).scale _
lemma modeFarVU {f:Profile}(h:Far f)(b): Far (modeSelVU b f):=(h.add ((reflFarVU f h).scale _)).scale _
lemma modeRefVU (f:Profile)(b):Reflects b (modeSelVU b f):=by
 intro t; cases b <;> simp [modeSelVU,modeSignVU,reflAtVU] <;> ring
lemma modeWidthVU (w:ℝ)(f: Profile)(b):modeSelVU b (width w f)=width w (modeSelVU b f):=by
 ext1 t; simp only [width_at,modeSelVU,_root_.smul_apply,_root_.add_apply, smul_eq_mul, reflAtVU,width_at,neg_div']; ring -- tune
lemma signCstVU (b): (modeSignVU b:ℂ)= signValue b:=by cases b <;> simp [signValue,modeSignVU]
lemma reflectCostVU (f:Profile): hat (stamp (ReflVU f))= glare (hat (stamp f)):=by
 ext1 p; rw [glare_at,hat_eq,hat_eq]
 conv_lhs=> rw [←integral_neg_eq_self (fun b:ℝ=>_)]
 simp only [stamp_at,reflAtVU, neg_neg]; apply integral_congr_ae; refine ae_of_all _ fun b=>?_ ; dsimp only; rw[plane]; simp [plane]
lemma movedVU (f:Panels)(i): moves (Signed.mirror i) f= update f i (glare (f i)):=by
 ext1 j; unfold moves reflectPanel; by_cases H:j=i; · subst j; simp [Signed.mirror]
 simp [Signed.mirror,H,Ne.symm H]
lemma polarVU (f:Grouping)(i):polar (update f i (ReflVU (f i)))=moves (Signed.mirror i) (polar f):=by rw [replaces, reflectCostVU,movedVU]; rfl
lemma mapModeVU (R: TestMap) (f:Grouping) (i: Axis) (b:Bool) (h:R (update f i (ReflVU (f i)))=signValue b*R f): R f=R (update f i (modeSelVU b (f i))):=by
 rw [modeSelVU,R.map_update_smul,R.map_update_add,R.map_update_smul,h,update_eq_self]; cases b <;> simp [modeSignVU, signValue,Complex.real_smul] <;> ring
lemma mapAllModeVU (R:TestMap)(f: Grouping)(e : Axis→Bool)(h:∀ f:Grouping,∀ i:Axis,R (update f i (ReflVU (f i)))= signValue (e i)*R f): R f=R fun i=> modeSelVU (e i) (f i):=by
 let L (s:Finset Axis):Grouping:=fun i=>if i∈s then modeSelVU (e i) (f i) else f i
 have he(s:Finset Axis):R f=R (L s):=by
    induction s using Finset.induction_on with
    | empty=>simp [L]
    | insert i s hi ih=>
       rw [ih,mapModeVU R (L s) i (e i) (h _ _)]; congr 1; ext1 j; by_cases h:j=i <;> simp [L,h,hi]
 exact (he Finset.univ).trans (by simp [L])
lemma expenseSelectVU (R:Paper)(e : Axis→Bool)(h:∀ f:Panels,∀ i:Axis,R (moves (Signed.mirror i) f)= signValue (e i)*R f) (f:Grouping)(w:Axis→ℝ)(n): sent R (mails w f n)= sent R (mails w (fun i=> modeSelVU (e i) (f i)) n):=by
 refine (mapAllModeVU _ _ e ?_).trans ?_
 · intro f i; rw [sent_at,polarVU]; exact h ..
 congr 1; ext1 i; exact modeWidthVU (fuel (w i) n) (f i) (e i)
variable {G : Gauge} {L : Register G} {S : Table L}
lemma portraitFixedVU (V : ∀ i,Chamber S i) (H : S.Hierarchy) (P : DiffPlan S) (hp : P.Derivatives S) (ho : P.Orientation H.spin)
    (J : Stress S) (C : Conserved P H.spin J) (Y : RawTensor H.spin J) {D : ℕ} {R : Series} (hR : Portrait J D R)
    (a b c d i: Axis) (f : Grouping) (hf : Far (f i)) (hF : ∀ j, Ends (f j))
    (w : Axis → ℝ) (he : w i=0) (hw : ∀ i,w i ≤ 0) (δ : ℝ) (hδ : 0<δ) :
    Budget δ (fun n => sent (R a b c d) (mails w f n)) := by
 let e:= axes a b c d
 let g: Grouping:=fun i=> modeSelVU (e i) (f i)
 refine (fixed V H P hp ho J C Y hR a b c d i g (modeFarVU hf _) (fun j=>modeEndsVU (hF j) _) (fun j _=>modeRefVU _ _) w he hw δ hδ).same (Eventually.of_forall fun n=> Eq.symm (expenseSelectVU (R a b c d) e ?_ f w n))
 intro f i
 let s:= Signed.mirror i
 have ht:=hR.Hs s a b c d f; change _ * R a b c d (moves s f)=R a b c d f at ht
 have hl: colorSign s a*colorSign s b*(colorSign s c*colorSign s d) = signValue (e i) := by
    rw [← spar_at,← spar_at]; cases hh:spar a b i <;> cases hu:spar c d i <;> simp [signValue,e,axes,hh,hu]
 rw [hl] at ht; rw [←ht,←mul_assoc,sign_sq,one_mul]
#print axioms portraitFixedVU
end YM.NSF.Outer
end
