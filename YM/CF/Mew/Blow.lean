import YM.CF.Mew.Lace
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mew
open Function Set Metric Filter MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I E A :Type*} [Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E][MeasurableSpace A]
lemma rivA (F: Key I → A → E)(μ:Measure A)[IsFiniteMeasure μ](p:∀ x,River (fun i=>F i x))(h:∀ x∈hill I,AEStronglyMeasurable (F x) μ) {C:ℝ}(ht:0 ≤ C)(hr:∀ x∈hill I,∀ᵐ y∂μ,‖F x y‖ ≤ C) (i:List I): River (fun z=> ∫ j,F z j∂μ) ∧ Integrable (fun a=>tipI (fun z=> F z a) i) μ ∧tipI (fun z=> ∫ j,F z j∂μ) i=∫ a,tipI (fun z=>F z a) i∂μ:=by
 letI : Nonempty ↥(hill I):= ⟨⟨0,roots⟩⟩; obtain ⟨Z,W,H⟩:=TopologicalSpace.exists_countable_dense (↥(hill I)); let Γ(y:A):Prop:=∀ x∈hill I,‖F x y‖≤C; have hQ:∀ᵐ y∂μ,Γ y:=by
    filter_upwards [ (ae_ball_iff (μ:=μ) (p:=fun y j _=> ‖F j.val y‖≤C) W).mpr (fun j _=> hr _ j.property)] with y q; intro i p'; exact H.induction (P:=fun j=>‖F j.val y‖≤C) q (isClosed_le (continuousOn_iff_continuous_restrict.mp (p y).shore|>.norm) continuous_const) ⟨i,p'⟩
 let G(z:Key I)(y:A):=if Γ y then F z y else 0; have hg(x):G x=ᵐ[μ] F x:= hQ.mono fun i p=>if_pos p
 have hp(y): River (fun v=> G v y):=by unfold G; split; exact p y; exact zeroR _
 let c:A→ℝ:=fun _=>C; have he(x)(hx : x∈hill I): AEStronglyMeasurable (G x) μ:=(h x hx).congr (hg x).symm
 have hu(i)(hi : i∈hill I)(y): ‖G i y‖≤c y:=by unfold G; split; exact ‹Γ y› i hi; rw [norm_zero]; exact ht
 have hx : (fun z=>∫ j,F z j∂μ)= fun z=> ∫ j,G z j∂μ:= funext fun i=>integral_congr_ae (hg i).symm; rw [hx]; refine ⟨riverSum μ G hp (integrable_const _) he hu,?_⟩
 have hv : (fun x=>tipI (fun z=>F z x) i)=ᵐ[μ] fun y=>tipI (fun z=>G z y) i:= hQ.mono fun x p=>congrArg (fun F:Key I→E=>tipI F i) (funext fun z=> (if_pos (t:=F z x) p).symm) -- tune ite.h
 obtain ⟨p,h⟩:=lanceInt μ G hp (integrable_const _) he hu i 0 roots; rw [integral_congr_ae hv]; exact ⟨p.congr hv.symm,h⟩
end YM.CF.Mew
