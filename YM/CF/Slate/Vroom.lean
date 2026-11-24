import YM.CF.Slate.Shah
import YM.CF.Slate.Ride
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Slate
open Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
namespace Far
section pieces
variable {D C s L e r':ℝ} {j:ℕ} {p:Site c}{R:Directions G c→ Mast G c} {g:Site c→ SU.group.El} {M:Monk SU.group S}
structure Lamp (T:Tube G S)(s x:ℝ)(M:Monk G S)(p:Site c)(g:Site c→SU.group.El)(R: Directions G c→ Mast G c)(j n:ℕ):Prop where
 stage: Allows n R 0 (1/2)
 reads: ∀ᶠ i in 𝓝 (0:Directions G c),AgreeNear id p (j*radiusB x) (Lattice.gauge g (Vmove x M.V i)) (satU G s (R i))
 sanda:p ∉ M.key.dome ((j+1)*radiusB x)
open AnalyticBridge.RelativeLogdet
lemma wick (h:K.Funds S T)(ht:ShardIncome n x L e r' T M.key M.park M.V M.k)(hg:0<r')(hp:Lamp T s x M p g R j n)(hx:Ready T x)(hv:1000 ≤ radiusB x)(H:∀ y:Mast SU.group c,‖y‖<1→ Fire T x M.park M.k l s n C y)(u:Dill S)(v:Signed)(φ:separation p (orientZ S v u)+(l+74)*radiusB x ≤ j*radiusB x) : (fun i=> Slate.payer T x (M.atop i x) q d l β v u)=ᶠ[𝓝 0] (fun i=> Slate.taste T M.park x M.k l v u (s • R i,coupling β • glow T x M.park M.k s q d l (shiftZ g M).z (R i))):=by
 have he : FreeResolvent.Gap ((baseX T x M.key M.park M.k ∘ Vmove x M.V) 0) r':=by simp only [Function.comp_apply,Vmove,smul_zero,Work.G07.at_zero_increment]; exact ht.soil
 have hV:‖R 0‖<1:=hp.stage.value.trans_lt (by norm_num)
 filter_upwards [Differential.holds (Neige.transX ht.kernel|>.continuousAt) he (r'/2) (half_lt_self hg) (FreeResolvent.native c) (Wisps.front M.key M.park), hp.stage.smooth.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hV)), hp.reads] with i hi v' l'
 let P:=M.atop i x; let A:=shiftZ g P; let N:Monk G S:={A with key:=bareStores S,V:=satU G s (R i)}; let X:= halo (j*radiusB x) {p}; have hh :Beat A N X:=by
    have he(y:Site c)(u:y∈X):separation p y ≤ j*radiusB x:=by obtain ⟨z,p,v⟩:=halo_spec.mp u; rwa [mem_singleton.mp p] at v
    refine ⟨fun y p=>?_ ,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>Iff.rfl,fun i p _=> l' i (he i.1 p),fun _ _=>rfl,fun _ _=>rfl⟩
    have hA:y∉M.key.place:=fun s=> hp.sanda (halo_spec.mpr ⟨y,s,(separation_comm ..).trans_le ((he y p).trans (Nat.mul_le_mul_right _ (Nat.le_succ _)))⟩); change (y∈ M.key.place↔ y∈(bareStores _).place); simp only [iff_false_intro hA]; simp [bareStores,Stores.place]
 have hA:=painter_s (l:=l) (q:=q) (x:=x) (β:=β) (d:=d) h g P hi (half_pos hg) (by omega) v; change Slate.payer T x P q d l β v u=_; rw [←hA,Slate.vary (U:=A) (V:=N) (T:=T) (l:=l) (q:=q) (d:=d) (β:=β) hh hx hv v u (aroundBk X (show Beat.shadows (o:=p) X _ from Subset.refl _) φ)]
 exact shineC (g:=N) rfl h (R i) (s:=s) rfl u v (H _ (mem_ball_zero_iff.mp v'))
lemma speed(g:Site c→SU.group.El)(M:Monk G S): ‖(shiftZ g M).z‖ ≤ ‖M.z‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg M.z)).mpr fun i=> (SU.group.norm_adjoint ..).trans_le (norm_le_pi_norm M.z i) -- metavars
lemma ink_e(hd:3 ≤ n)(hs:0<s)(hs':s ≤ 1) -- remove
 (h:0≤ D)(H: Fire T x M.park M.k l s n C (R 0))(hp:Allows n R 0 (1/2))(hl:‖M.z‖ ≤ e)(hv:|coupling β| * Jet.composeCost n (e*C) (1/2) ≤ s / 2) -- tune
 (v:Signed)(u:Dill S) (hK:KnotP (taste T M.park x M.k l v u) n (D*s) D s):
 Allows n (fun i=>Slate.taste T M.park x M.k l v u (s • R i, coupling β • glow T x M.park M.k s q d l (shiftZ g M).z (R i))) 0 (composeCost n ((D+D)*s^3) (1/2)):=by
 let f:= glow T x M.park M.k s q d l (shiftZ g M).z; let t:= coupling β; let W(i):= s⁻¹ • (t • f (R i)); have hu:=glow_p (q:=q) (d:=d) H _ ((speed g M).trans hl)
 have hQ:Allows n W 0 (1/2):=by refine (((hu.comp hp).smul (coupling β)).smul s⁻¹).mono ?_; rw [abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs]; linarith only [hv]
 let P(i): Ark T M.park:= (R i,W i); have ht: Allows n P 0 (1/2):=hp.pair hQ
 refine ((tip_a hK hs hs' hd (x:=P 0) (ht.value.trans_lt (by norm_num)) le_rfl).comp (f:=P) ht).germ (Eventually.of_forall fun i=>?_)
 simp only; rw [ show s • P i=(s • R i,t • f (R i)) from Prod.ext rfl (smul_inv_smul₀ hs.ne' _)]
end pieces
end Far
end YM.CF.Slate
