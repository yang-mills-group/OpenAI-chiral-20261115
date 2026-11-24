import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Slog
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
variable(q:Chi)(d:ℝ)(l:ℕ)(R:ChartRatio G)(t:ℝ)
open AnalyticBridge.GaussianFieldAlignment Orthogonal Gauges Locations PhysicalNext.OrderedAffine2B.SymRows Tensor Channels Primitives.HaarLogJets.Guard
open Souk
variable {M N: Monk G S}{H: Support c}{P P':Tab S}
abbrev gown (P:Tab S)(j:P.1.Free)(v:Mast G c):= Eman P.1 j (flute P.1 (sol S T P.2 x P.1 l) 1 v)
lemma flex(P:Tab S)(j:P.1.Free)(v: Mast G c):gown T x l P j v=tint G _ (sol S T P.2 x P.1 l v) j:=by unfold gown flute Push.Uniform.curve; change (Push.Uniform.paint _ _ _).2 _=_; rw [Push.Uniform.paint_meet,one_smul]  -- tune
lemma capP(P:Tab S)(j:P.1.Free)(v:Mast G c)(h:Allows n (sol S T P.2 x P.1 l) v C): Allows n (gown T x l P j) v (Push.Uniform.shade G*C):=by
 let L:=tint G P.1.Free; let X:Fish (Key P.1 G) →L[ℝ] SU.group.Color:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:P.1.Free=> SU.group.Color) j).comp L.toContinuousLinearMap
 have ht:‖X‖ ≤ Push.Uniform.shade G:=ContinuousLinearMap.opNorm_le_bound _ (Push.Uniform.shade_pos _).le fun i=> (norm_le_pi_norm (L i) j).trans (Push.Uniform.tint_le i)
 exact (h.linear _ ht).germ (Eventually.of_forall fun i=>(flex _ _ _ P j i).symm)
lemma truss (P:Tab S)(u:ℝ)(v:Mast G c)(he:Fire T x P.1 P.2 l u n C v)(hv:∀ i, ‖gown T x l P i (u • v)‖ ≤ 2*t)(ht:0<t)(hp:4*t< R.radius)(hx:LocalRatio R): let y:= u • v; let V:= satU G u v; ∑ i:Site c,HWork T x q d l R t (bunk S P V) i= (addH P.1 R (flute P.1 (sol S T P.2 x P.1 l) 1 y):ℂ):=by
 intro y V; let m(i):= gown T x l P i y
 simp_rw [orchard T x q d l R t _ P, show ∀ i,(bunk S P V).rich x T q d l 0 ((evoke x P).symm i)=m i from fun i=> izan T x q d l P v he i]
 rw [← Complex.ofReal_sum]; apply congrArg Complex.ofReal; rw [Finset.sum_comm]; simp_rw [← sum_mul]; unfold addH; rw [Real.log_prod]; swap -- order check
 · exact fun i _=> (hx.pos _ (mem_ball_zero_iff.mpr ((hv i).trans_lt (by linarith)))).ne'
 refine sum_congr rfl fun i _=>?_ ; rw [show (∑ y:Site c,ansC (S:=S) y i.val)=1 from plant_s S (fun _:Fin (0+2)=>i.val),one_mul,logGuard,broad_one q (d:=2*t) (by positivity) (hv i),one_mul]
-- fur sized
lemma bed_count (i:Site c)(A:Monk G S): let p:= Fintype.card Axis*S.patch.L.val^4*plot 1; (gate x A i).card≤ p:=by
 intro p; let F:= gate x A i; let U:Bond f→ Prop:= fun j=> separation i (S.ratio.parent j.1) ≤1; let Q:=univ.filter U
 have hh: F.card ≤ Q.card:=card_le_card_of_injOn (fun j=>j.val.val) (fun j h=>mem_filter.mpr ⟨mem_univ _,innZ _ _ ((mem_filter.mp h).2)⟩) (fun _ _ _ _ hz=> Subtype.ext (Subtype.ext hz))
 let P:=pavilion 1 i; refine hh.trans ((fine_count Q P fun j v=> (theatre ..).mpr ((mem_filter.mp v).2)).trans ?_); have ht:= pay_v (r:=1) i
 exact (Nat.mul_le_mul_left _ ht) 
lemma cedar(P:Tab S)(s ρ M W:ℝ)(p:0<ρ)(h:s≤ρ)(hp:ρ ≤1)(hv:0<t)(he:0<s)(hu:∀ (j:P.1.Free)(v:Mast G c),‖v‖<ρ→ Allows n (gown T x l P j) v M ∧ ‖gown T x l P j v‖ ≤2*t ∧Allows n (Real.log ∘ R.J) (gown T x l P j v) W)(hq:∀ v:Mast G c,‖v‖<1→ Fire T x P.1 P.2 l ρ n C v)(hM:0 ≤ M)(hW:0 ≤ W)(i:Site c): let A:= composeCost n (composeCost n W M) 1; let E:ℝ:= ↑(Fintype.card Axis*S.patch.L.val^4*plot 1)*A
 ∀ y:InputZ G c,‖y‖<s → Allows n (satX (MossZ T x q d l R t P i)) y (E+E):=by
 intro A E; have hA:0 ≤ A:=by unfold A Jet.composeCost; positivity
 let F:=bunk S P; let Z:= (F 1).park; let Q:=gate x (F 1) i; let X(y):=F (represent y); let L:=chair T P.1
 let V(y):=HWork T x q d l R t (X y) i
 have hx(y:InputZ G c)(hy:‖y‖<s): Allows n V y E:=by
    let N(z:(F 1).zoo x)(y:InputZ G c):=seat T x q d l R t (X y) z i; let p:= Complex.ofRealCLM
    have hh' : V= p∘ fun y=>∑ v∈ Q,N v y:= funext fun v=> city_x ..
    have hh(z:(F 1).zoo x): Allows n (N z) y A:=by
       let B:=gown T x l P (evoke x P z)
       have he'(y: InputZ G c):‖L y‖ ≤ ‖y‖:=Push.Uniform.tint_inv_le y
       have he(y:InputZ G c)(hy: ‖y‖<s): ∀ z:(F 1).zoo x,(X y).rich x T q d l 0 z=gown T x l P (evoke x P z) (L y):=by
          intro z; let v:= ρ⁻¹ • L y; have hv:ρ • v=L y:= smul_inv_smul₀ (by assumption : 0<ρ).ne' _; have hy':‖v‖<1:=by
             have he'': ‖L y‖<ρ:=(he' y).trans_lt (hy.trans_le h); rw [←hv,norm_smul_of_nonneg (by assumption:0<ρ).le] at he''; exact lt_of_mul_lt_mul_left (he''.trans_eq (mul_one _).symm) (by assumption:0<ρ).le
          have hp' := izan T x q d l P v (hq v hy') (evoke x P z); dsimp only at hp'; change (bunk S P (represent y)).rich _ _ _ _ _ _ _= _; rw [show satU G ρ v= _ from (by unfold satU; rw [hv]; exact chap T P.1 y : satU G ρ v=represent y), Equiv.symm_apply_apply,hv] at hp'; exact hp'
       obtain ⟨hc,h,hX⟩:= hu (evoke x P z) (L y) ((he' y).trans_lt (hy.trans_le h)); let X:= ansC (S:=S) i z.val.val
       have hy': Allows n L y 1:= allows_linear (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j=>(he' j).trans_eq (one_mul _).symm) ((he' y).trans ((hy.trans_le ((by assumption:s≤ρ).trans hp)).le))
       refine (((((hX.comp hc).comp hy').smul X).mono (mul_le_of_le_one_left hA (plant_v (w:=fun _:Fin (0+2)=>z.val.val)))).germ ?_)
       filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with j hj; unfold N seat logGuard; rw [he _ (mem_ball_zero_iff.mp hj), broad_one q (by positivity) (hu _ _ ((he' j).trans_lt ((mem_ball_zero_iff.mp hj).trans_le (by assumption)))).2.1,one_mul]; rfl -- tune
    rw [hh']; exact ((((summed Q N fun i _=>hh i).mono (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (bed_count x i (F 1))) hA)).linear p (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>by rw [one_mul]; exact (Complex.norm_real i).le)).mono (one_mul _).le)
 intro y hy; refine subtract_p (hx y hy) (allows_const y (show ‖HWork T x q d l R t (F 1) i‖ ≤ E from ?_))
 exact (show V 0= HWork T x q d l R t (F 1) i from by unfold V X; rw [show represent (0:InputZ G c)=1 from by simp]) ▸ (hx 0 (show ‖(0:InputZ G c)‖<s by simpa)).value -- tune
end
end YM.CF.Tarn
