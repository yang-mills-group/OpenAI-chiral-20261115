import YM.CF.Char.Giro
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
open Locations Gauges Channels AnalyticNext.QuarticMatch
section
open Reef Offset
local notation "D"=> SU.group
variable {n:Side}(T:Tube SU.group S)(A:Stores S)(F:Forest S.ratio)(x:ℝ)(V:Config SU.group c)(k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray SU.group (Frozen A x F))
private abbrev fCL:Ox≃L[ℝ]Ox:=Tensor.ortho (shiftF Unit) ()
lemma snipE (K:PathData D)(r l:ℕ)(U:Config D n)(i:Cell n) : shorten K r l (Reef.echo U) i=frolic (shorten K r l U i):=by
 unfold shorten; change _= fCL _; rw [fCL.map_tsum]; apply tsum_congr; intro j; unfold shortenTerm; split
 · rw [PathData.ellTerms,PathData.ellTerms,tollSlot,map_smul]; rfl
 rw [map_zero]
lemma shootE(K:Clip)(U:Config D n)(i:Cell n): shoot K (Reef.echo U) i=frolic (shoot K U i):=by rw [shoot,shoot,faceValue,Reef.echo_t,swing,map_smul]; rfl
lemma plotE(K:Clip)(P:PathData D)(r l:ℕ)(U:Config D n)(i:Twin n): plotted P K r l (Reef.echo U) i=frolic (plotted P K r l U i):=by unfold plotted; split; apply snipE; exact shootE ..
lemma thinE(K:Clip)(P:PathData D)(r l:ℕ)(t:ℝ)(U:Config D n)(i:Twin n): thinned P K t r l (Reef.echo U) i= frolic (thinned P K t r l U i):=by
 have he:PathData.kept K t i.1.1 (Reef.echo U)↔PathData.kept K t i.1.1 U:=by simp only [PathData.kept,faceValue,echo_t,cool]
 unfold thinned; split
 · simp_rw [he]; split; exact snipE ..; rw [map_zero]
 unfold toll; rw [faceValue,echo_t,cool,shootE, map_smul]; rfl
private lemma turns {α:Type*} (f g:α→Pay D)(h:∀ i x, g i (frolic x)=frolic (f i x))(x): (∑' i,g i) (frolic x)= frolic ((∑' i,f i) x):=by
 let L:= fCL.arrowCongr fCL; have he(v:Pay D)(x: Ox): L v (frolic x)=frolic (v x):=by change fCL (v (fCL.symm (fCL x)))=_; rw [ContinuousLinearEquiv.symm_apply_apply]; rfl
 rw [show g=L ∘ f from ?_]; unfold Function.comp; rw [←L.map_tsum]; exact he ..
 funext i; apply ContinuousLinearMap.ext; intro x; obtain ⟨j,rfl⟩:=fCL.surjective x; exact (h i j).trans (he (f i) j).symm
lemma rateY(U:Config D n)(x:Site n)(w:Walk)(b:ℝ)(v): rated (Reef.echo U) x w b (frolic v)=frolic (rated U x w b v):=by change b • SU.group.adjoint _ _=_; rw [echo_t,← dip]; exact (map_smul frolic _ _).symm
lemma leapsE(r:ℕ)(i:Twin f)(j:Twin c)(v): T.Φ r (Reef.echo V) i j (frolic v)=frolic (T.Φ r V i j v):=by
 apply turns; intro x z; dsimp only [casted]; split
 · rw [repE]; exact rateY ..
 change 0=_; exact (map_zero frolic).symm
lemma kickedE(r:ℕ)(i:Bond c)(j:Twin c)(v): T.Φ' r (Reef.echo V) i j (frolic v)=frolic (T.Φ' r V i j v):=by
 apply turns; intro x z; unfold Pressure.priced; split; exact rateY ..; exact (map_zero frolic).symm
lemma zvE(R:Config D c)(j:Bond c): Tube.Z S (Reef.echo R) (Reef.echo V) j=frolic (Tube.Z S R V j):=by unfold Tube.Z Reef.echo; rw [←map_inv,← map_mul,swing,map_smul] -- tune
lemma frame_b(h:S.patch.Branches S.kernel SU.group)(i:Slots S) : fixedBase T x (Reef.echo V) k i= frolic (fixedBase T x V k i):=by
 obtain ⟨s,i|i⟩:=i
 · change fixedF T x _ _ _=frolic (fixedF ..); simp only [fixedF,echo_p,roll0,Tube.Xf,Tube.Xn,plotE,Pressure.zip,map_sub,map_sum]
   simp_rw [leapsE] -- tune
 change fixedI T x _ _ _ _=frolic (fixedI ..); simp only [fixedI,zNoise,echo_p,roll0,(proceeds h _ _).1,zvE, Tube.Xn,plotE,Pressure.zip,map_sub,map_sum]; simp_rw [ kickedE]
lemma rated_b (h:S.patch.Branches S.kernel SU.group)(i:Slots S): Rows.base T x (Reef.echo V) k i= frolic (Rows.base T x V k i):=by
 obtain ⟨s,i|i⟩:=i
 · change Rows.faceFixed T x _ _ _= frolic (Rows.faceFixed ..); simp only [Rows.faceFixed,echo_p,roll0,Tube.Xf,Tube.Mv,Tube.vision,Pressure.zip,plotE,thinE,leapsE, map_sub,map_sum]
 change Rows.noiseFixed ..= frolic (Rows.noiseFixed ..); simp only [Rows.noiseFixed,echo_p,roll0,(proceeds h _ _).1,zvE, Tube.Mw,Tube.vision,Pressure.zip, thinE,kickedE,map_sub,map_sum]
lemma storyE {σ E Λ:ℝ}(ht:S.patch.Branches S.kernel SU.group)(h:T.up.Bounds T.high σ E Λ)(hx:Rare T.up): Flow (PhysicalNext.OrderedAffine2B.SymRows.room x A F) (shiftF _) (shiftF _) k k T V (Reef.echo V) q d Y (Reef.echo Y):=by
 refine ⟨⟨gram_motion (Equiv.refl _) _ _ (Equiv.refl _) (shiftF _) ht h (fun _=> rfl) (brandE T x V k ht) ⟨fun _=>rfl,fun _=>rfl⟩,brandE T x V k ht,rated_b T x V k ht,frame_b T x V k ht,fun i=>?_⟩,fun a=>?_⟩
 · unfold autoShell; rw [repE]; unfold Reef.echo; rw [←map_inv,←map_mul]; exact patchE ..
 dsimp only [PhysicalNext.OrderedAffine2B.SymRows.room]; rw [rack_actual,rack_actual,repE,inc_re,clip_reel T hx]
 simp only [noiseTaylor,(proceeds ht _ _).1,Reef.echo,←map_inv,←map_mul,cold]
end
end YM.CF.Char
