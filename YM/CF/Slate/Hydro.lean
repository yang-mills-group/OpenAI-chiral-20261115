import YM.CF.Slate.Dill
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
open Work.E03 AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows
local notation "G"=>SU.group
variable {T:Tube SU.group S}{K:Teller SU.group}
lemma gust_p (h:S.patch.Branches S.kernel G) (U:Config G f)(k:S.Choices)(g:Site c→SU.group.El): S.prediction (Lattice.gauge (constantGauge g S.ratio) U) k=Lattice.gauge g (S.prediction U k):=by
 funext i; unfold StepData.prediction; rw [S.updateGauged h,(S.patch.bond_gauge (h:=h) ..).2]; simp only [Function.comp_apply,constantGauge,Ratio.embed_parent]; rfl
lemma rgba(V:Config G c)(U:Config G f)(k:S.Choices)(g:Site c→SU.group.El)(p:K.Funds S T)(d:ℕ)(w:ℝ): Yaught T d (fiery G w S.patch.L) (temp w) (Lattice.gauge g V) (Lattice.gauge (constantGauge g S.ratio) U) k = Yaught T d (fiery G w S.patch.L) (temp w) V U k:=by
 let z:=constantGauge g S.ratio; let Z:=Lattice.gauge z U; let W:=Lattice.gauge g V; have hh:=gust_p (funds_branch p) U k g
 have hk{n:Side}(V:Config SU.group n)(g:Site n→SU.group.El)(i:Cell n): sore G (faceValue (Lattice.gauge g V) i) = sore G (faceValue V i):=by rw [face_gauge]; unfold sore; rw [SU.group.price_conj,SU.group.curvature_conjugate, SU.group.norm_adjoint]
 funext b; unfold Yaught; rcases b with b|b|b|b <;> simp only [Sum.elim_inl, Sum.elim_inr]
 · rw [hiatus,hiatus]; unfold KissP; rw [hk]; apply congrArg (T.high.direct*sore SU.group (faceValue U b)+ ·); refine sum_congr rfl fun i _=> ?_
   have ht:RiftF d Z W T (b,i)= SU.group.adjoint (z b.1) (RiftF d U V T (b,i)):=by unfold RiftF; unfold Z W; rw [Tube.Xf,plotted_turn, rolledF]; exact (map_sub (SU.group.adjoint _) _ _).symm
   rw [show RiftF _ _ _ T _ = _ from ht, SU.group.norm_adjoint]
 · rw [iham,iham]; unfold KissI; have hp :tideX S k W Z b=g b.1*tideX S k V U b*(g b.1)⁻¹:=by unfold tideX Z W z; rw [hh]; unfold Lattice.gauge; group
   have he: RiftI d Z W T k b = SU.group.adjoint (g b.1) (RiftI d U V T k b):=by unfold RiftI W Z z; rw [hh,Z_turn,rolledI]; exact (map_sub _ _ _).symm
   change S.kernel.penalty*sore G (tideX S k W Z b)+_=_; rw [hp, show sore _ _=sore G (tideX S k V U b) from ?_, show RiftI _ _ _ T _ _ = _ from he, SU.group.norm_adjoint]
   unfold sore; rw [SU.group.curvature_conjugate, SU.group.price_conj, SU.group.norm_adjoint]
 · rw [inka,inka,zpia,zpia]; unfold KissQ; rw [hk]; apply congrArg (-(T.low.direct*sore SU.group (faceValue V b)) + ·); refine sum_congr rfl fun i _=>?_ ; let f:=g b.1; let a:= SU.group.adjoint f; have hv:=gauge_gaps K T p d U V k g (b,i); have h₁: RiftL d Z W T k (b,i) = a (RiftL d U V T k (b,i)):=hv.1; have h₂ : RiftD d W T (b,i) = a (RiftD d V T (b,i)):=by
       have hp:T.Xn d W=turnData g (fun i: Twin c=>i.1.1) (T.Xn d V):=funext fun v=> plotted_turn T.down T.low d _ _ _ _
       unfold RiftD; rw [hp]; exact hv.2 _
   rw [show RiftD _ _ T _ = _ from h₂, show RiftL _ _ _ T _ _= _ from h₁,show T.Xn d _ (b,i)=a (T.Xn d V _) from plotted_turn ..]; rw [show ∀ x y,inner ℝ (a x) (a y)=inner ℝ x y from fun x y=> (Gauges.turn f).inner_map_map x y, show ∀ x y,inner ℝ (a x) (a y)=inner ℝ x y from fun x y=> (Gauges.turn f).inner_map_map x y]
 rw [nk,nk]; have he:RiftN d W T b = SU.group.adjoint (g b.1) (RiftN d V T b):=by
    unfold W RiftN Tube.Xn zip; rw [map_sum]; exact sum_congr rfl fun i _=>by rw [plotted_turn]; exact lane_turn ..
 rw [show RiftN _ _ T _=_ from he, SU.group.norm_adjoint]
end YM.CF.Slate
