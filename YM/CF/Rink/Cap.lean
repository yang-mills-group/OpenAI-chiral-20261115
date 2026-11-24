/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Rink.Hello
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Governor
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rink
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
variable {K:Teller G}
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
open Affine Reine
lemma rein{ι P:Type*}[Fintype ι]{F : ι → Ox≃ₗᵢ[ℝ] Ox}{S:P→Ox≃ₗᵢ[ℝ] Ox}{T T':ι→ P →Pressure.Pay G}{a a':ι→Ox}(h:∀ i j z,T' i j (S j z)=F i (T i j z))(p:∀ i,a' i=F i (a i))(j:P): Pressure.unzip T' a' j=S j (Pressure.unzip T a j):=by
 unfold Pressure.unzip; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; apply ext_inner_left ℝ; intro z; obtain ⟨v,rfl⟩:=(S j).surjective z; rw [(S j).inner_map_map,p,ContinuousLinearMap.adjoint_inner_right,h,(F i).inner_map_map,ContinuousLinearMap.adjoint_inner_right] -- tune inner lemma
lemma cog{ι P:Type*}[Fintype P]{F : ι → Ox≃ₗᵢ[ℝ] Ox}{S:P→Ox≃ₗᵢ[ℝ] Ox}{T T':ι→ P →Pressure.Pay G}{a a':P→Ox}(h:∀ i j z,T' i j (S j z)=F i (T i j z))(p:∀ i,a' i=S i (a i))(i): Pressure.zip T' a' i=F i (Pressure.zip T a i):=by unfold Pressure.zip; rw [map_sum]; exact Finset.sum_congr rfl fun j _=>by rw [p,h]
lemma slate_x (r:ℕ)(t u:ℝ)(U Z:Config G f)(V Q W R:Config G c)(L:Twin f→ Ox ≃ₗᵢ[ℝ] Ox)(P:Twin c→ Ox≃ₗᵢ[ℝ] Ox)(Y:Bond c→Ox ≃ₗᵢ[ℝ] Ox)(N:Co c Gain→ Ox≃ₗᵢ[ℝ] Ox)
 (HL:∀ i j z,T.Φ r W i j (P j z)=L i (T.Φ r V i j z))(HP:∀ i j z,T.Φ' r W i j (P j z)=Y i (T.Φ' r V i j z))(HV:∀ i j z,T.N r W i j (P j z)=N i (T.N r V i j z))
 (hs:∀ i,T.Xf r Z i=L i (T.Xf r U i))(hX:∀ i,T.Xn r W i=P i (T.Xn r V i))(hQ:∀ i,T.vision r u W i=P i (T.vision r u V i))(hz:∀ i,Tube.Z S R W i=Y i (Tube.Z S Q V i))(hw: ∀ i,Pressure.wire R W i= Pressure.wire Q V i)
 (hF:∀ i,crown T.up T.high r 1 t Z i=crown T.up T.high r 1 t U i)(hC:∀ i,crown T.down T.low r S.patch.L.val u W i=crown T.down T.low r S.patch.L.val u V i):
 T.workF r Z W t u=T.workF r U V t u ∧ T.workI r R W u=T.workI r Q V u∧ T.workL r Z R W u=T.workL r U Q V u ∧ T.workC r W u=T.workC r V u ∧T.workD r W u=T.workD r V u ∧ T.workN r W u=T.workN r V u:=by
 have h₁(i): T.Mv r u W i=L i (T.Mv r u V i):= cog HL hQ i; have h₂(i): T.Mw r u W i=Y i (T.Mw r u V i):= cog HP hQ i; have h₃:=cog HV hQ
 refine ⟨funext fun i=> ?_,funext fun i=> ?_,funext fun i=> ?_,funext fun i=> ?_,funext fun i=>?_,funext fun i=>?_⟩
 · simp_rw [Tube.workF,hF,h₁,hs,LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.norm_map]
 · simp_rw [Tube.workI,Tube.monetary,hw,h₂,hz,LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.norm_map]
 · unfold Tube.workL; refine sum_congr rfl fun j _=> ?_; rw [rein HL hs,rein HP hz,hX,hQ,← map_add,←map_sub,(P _).inner_map_map]
 · simp_rw [Tube.workC,hC,hX,hQ,LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.norm_map]
 · unfold Tube.workD; refine sum_congr rfl fun j _=> ?_; rw [rein HL h₁,rein HP h₂, rein HV h₃,hQ,←map_add,←map_add,←map_sub,(P _).inner_map_map]
 unfold Tube.workN; rw [h₃,(N i).norm_map] -- tune
section
open Pressure.Tube PhysicalNext.Repeat.Turn
abbrev badge : Ox≃ₗᵢ[ℝ] Ox:=LinearIsometryEquiv.ofSurjective frolic (fun q=> ⟨frolic q,fiz2 q⟩)
lemma lane_b(T:Tube G S)(r:ℕ)(V:Config G c)(i:Co c Gain)(j:Twin c)(z:Ox): T.N r (Reef.echo V) i j (frolic z) =frolic (T.N r V i j z):=by
 have hx {α:Type} (f g:α→Pay G)(h:∀ i x, g i (frolic x)=frolic (f i x))(x): (∑' i,g i) (frolic x)= frolic ((∑' i,f i) x):=by
    let F:=badge.toContinuousLinearEquiv; let L:= F.arrowCongr F; have he(v:Pay G)(x: Ox): L v (frolic x)=frolic (v x):=by change F (v (F.symm (F x)))=_; rw [ContinuousLinearEquiv.symm_apply_apply]; rfl
    rw [show g=L ∘ f from ?_]; unfold Function.comp; rw [←L.map_tsum]; exact he ..
    funext i; apply ContinuousLinearMap.ext; intro x; obtain ⟨j,rfl⟩:=F.surjective x; exact (h i j).trans (he (f i) j).symm
 apply hx; intro x z; unfold Pressure.priced; split; exact rateY ..; exact (map_zero frolic).symm
lemma curseC(K:PathData G)(p:Clip)(V:Config G c)(r a:ℕ)(t:ℝ)(i:Cell c): crown K p r a t (Reef.echo V) i=crown K p r a t V i:=by
 have he:PathData.kept p t i.1 (Reef.echo V) ↔ PathData.kept p t i.1 V:=by simp only [PathData.kept,faceValue,Reef.echo_t,cool]
 unfold crown trunk; rw [snipE, he, faceValue,Reef.echo_t,cool] -- tune
 simp [faceValue]
lemma cost_g(K:PathData G)(p:Clip)(V:Config G c)(z:Site c→ SU.group.El)(r a:ℕ)(t:ℝ)(i:Cell c): crown K p r a t (Lattice.gauge z V) i=crown K p r a t V i:=by
 have he:PathData.kept p t i.1 (Lattice.gauge z V)↔PathData.kept p t i.1 V:=by simp [PathData.kept]
 unfold crown trunk; rw [Gauges.shorten_turn,he,face_gauge]; simp -- tune
lemma score_f(T:Tube G S)(x:ℝ)(i:Dill S)(U:Config G f)(V Q:Config G c):payX T x i (Reef.echo U) (Reef.echo Q) (Reef.echo V)=payX T x i U Q V:=by
 let r:=Stores.till x; let v:= temp x; let s:= fiery G x S.patch.L; have hw(i):wire (Reef.echo Q) (Reef.echo V) i= wire Q V i:=by unfold wire Reef.echo; rw [← map_inv,← map_mul, Reef.cool]; -- tune line ending
 obtain ⟨hF,hI,hL,hC,hD,hN⟩:= slate_x (T:=T) r s v U (Reef.echo U) V Q (Reef.echo V) (Reef.echo Q) (fun _=> badge) (fun _=> badge) (fun _=> badge) (fun _=> badge) (fun i j z=> leapsE ..) (fun i j z=> kickedE ..) (fun i j z=>lane_b T r V i j z) (fun i=> plotE ..) (fun i=> plotE ..) (fun i=> thinE ..) (fun i=>zvE ..) hw (fun i=>curseC ..) (fun i=>curseC ..)
 rcases i with i|i|i|i; exact congr_fun hF _; exact congr_fun hI _; exact congrArg₂ (·+·) (congrFun hC _) (congrArg₂ (·+·) (congrFun hL _) (congrFun hD _)); exact congrFun hN _
open Gauges
lemma score_g(T:Tube G S)(x:ℝ)(i:Dill S)(U:Config G f)(V Q:Config G c)(z:Site c→ SU.group.El):payX T x i (Lattice.gauge (constantGauge z S.ratio) U) (Lattice.gauge z Q) (Lattice.gauge z V)=payX T x i U Q V:=by
 let F:=constantGauge z S.ratio; let r:= Stores.till x; let s:= fiery G x S.patch.L; let v:=temp x
 obtain ⟨hF,hI,hL,hC,hD,hN⟩:= slate_x (T:=T) r s v U (Lattice.gauge F U) V Q (Lattice.gauge z V) (Lattice.gauge z Q) (fun i=>(Gauges.turn (F i.1.1)).toLinearIsometryEquiv rfl) (fun i=>(Gauges.turn (z i.1.1)).toLinearIsometryEquiv rfl) (fun i=>(Gauges.turn (z i.1)).toLinearIsometryEquiv rfl) (fun i=>(Gauges.turn (z i.1)).toLinearIsometryEquiv rfl) (fun i j v=> leap_turn ..) (fun i j v=>lane_turn ..) (fun i j v=>lane_turn ..) (fun i=>plotted_turn ..) (fun i=> plotted_turn ..) (fun i=>thin_turn ..) (fun i=>Z_turn ..) (fun i=>wire_gauge ..) (fun i=>cost_g ..) (fun i=>cost_g ..)
 rcases i with i|i|i|i; exact congr_fun hF _; exact congr_fun hI _; exact congrArg₂ (·+·) (congrFun hC _) (congrArg₂ (·+·) (congrFun hL _) (congrFun hD _)); exact congrFun hN _
lemma score_s(T:Tube G S)(x:ℝ)(i:Dill S)(U:Config G f)(V Q:Config G c)(b:Site c): payX T x i (Lattice.translate (S.ratio.embed b) U) (Lattice.translate b Q) (Lattice.translate b V)=payX T x (stepZ S b i) U Q V:=by
 rcases i with i|i|i|i; exact translated_F ..; exact translated_I ..; exact congrArg₂ (·+·) (translated_C ..) (congrArg₂ (·+·) (translated_L ..) (translated_D ..)); exact translated_N ..
end
end YM.CF.Rink
