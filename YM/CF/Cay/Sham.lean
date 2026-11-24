import YM.CF.Cay.Stall
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal Gauges PhysicalNext.OrderedAffine2B.SymRows
open Matrix
variable {M:Monk SU.group S}
lemma turP{A:PathData G}{a p b:ℝ}{P:Clip}(X:A.Bounds P a p b)(y:Site c)(t:ℕ)(V:Config G c)(g:Site c→SU.group.El): turF A t (Lattice.gauge g V) y=turF A t V y:=by
 have hp{k:ℕ}(Q:ℕ→ Atom G k)(H:∀ i,(Q i).Invariant): gplot (batch Q t) (Lattice.gauge g V) y=gplot (batch Q t) V y:=by
    refine tsum_congr fun i=>?_ ; unfold batch; split
    · unfold Atom.unmasked; simp only [Work.F05.slot_gauge]; exact H i ..
    simp only [dimU]
 unfold turF; rw [hp A.cubic (fun i=>(X.invariant i).2.1),hp A.quartic (fun i=>(X.invariant i).2.2)]
lemma wage (g:Site c→SU.group.El)(p:K.Funds S T)(ht:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) w)(hv:0<w)(hz:120 ≤ radiusB x)(s:Signed): let H:=shiftZ g M; let f(A:ζ):=ballot T x (pull s 0 A.V) (pull s 0 (A.sent x T q d l β)) (choice s A.k);
 stars T x H q d l β s=stars T x M q d l β s ∧ f H=f M:=by
 intro H Ω; obtain ⟨v,z,U,V⟩:=p.feeds; have ht' :=painter_s (l:=l) (d:=d) (q:=q) (β:=β) p g M ht hv hz s; let Y(v:ζ):=turF T.up (Stores.till x) (pull s 0 (v.sent x T q d l β)); let X(v:ζ):= turF T.down (Hors.cart x S.patch.L) (pull s 0 v.V)
 have ha:H.sent x T q d l β=Lattice.gauge (constantGauge g S.ratio) (M.sent x T q d l β):= Eq.trans (show H.sent x T q d l β=landed x M.key M.park (Lattice.gauge g M.V) (gaugeY g x M.key M.park (M.bush x)) (Pogo g M x (M.fuel x T q d l β)) from congrArg (landed x M.key M.park (Lattice.gauge g M.V) (gaugeY g x M.key M.park (M.bush x))) (buzz g M q x β d p l w ht hv hz)) (audU g M x _ _)
 have he:Y H=Y M:=by unfold Y; rw [ha,Work.F05.pull_gauge_zero]; exact funext fun i=>turP U i _ _ _
 have hd:X H=X M:=by unfold X; rw [show H.V=Lattice.gauge g M.V from rfl,Work.F05.pull_gauge_zero]; exact funext fun i=>turP V i _ _ _
 let Z(v:ζ): Site f ⊕ Site c→ℝ:=Sum.elim (Y v) (- X v); have hZ: Z H= Z M:=by unfold Z; rw [he,hd]
 constructor
 · exact congrArg₂ (fun (v:Dill S →ℝ)(w: Site _⊕ Site _→ℝ)=> Sum.elim v w) ht' hZ
 unfold Ω; unfold ballot; rw [ha,show H.V=Lattice.gauge g M.V from rfl,Work.F05.pull_gauge_zero,vega (T:=T) g p]; exact congrArg₂ (fun (v:Dill S →ℝ)(w: Site _⊕ Site _→ℝ)=>Sum.elim v w) (rgba _ _ (choice s M.k) (Gauges.turned g s) p _ _) (by unfold Z X Y at hZ; rw [ha,show H.V=Lattice.gauge g M.V from rfl, Work.F05.pull_gauge_zero M.V g,vega (T:=T) g p] at hZ; exact hZ)
lemma rota_g(g:Site c→SU.group.El)(p:K.Funds S T)(ht:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) w)(hv:0<w)(hz:120 ≤ radiusB x)(hp:0<β): adjust T x q d l β (shiftZ g M)=adjust T x q d l β M:=by
 let H:=shiftZ g M; have he(s:Signed):= wage (M:=M) (l:=l) (q:=q) (β:=β) (d:=d) g p ht hv hz s
 have hg: potH T x H q d l β= potH T x M q d l β:=by unfold potH; unfold H; simp_rw [fun s=>(he s).1] -- tune
 let f (A:Monk SU.group S)(s: Signed):= (∑ i: Along S,ballot T x (pull s 0 A.V) (pull s 0 (A.sent x T q d l β)) (choice s A.k) i)
 have hh:f H=f M:=funext fun i=>congrArg (fun b:Along S→ℝ=>∑ j,b j) (he i).2; have hh'(A:Monk SU.group S):aster T x A q d l β= -β*averaged (f A)+costU (A.bell x)/2:= (deck_x _ _ _ _ _ _ _ hp p).trans (congrArg (fun y=> -β*y+costU (A.bell x)/2) ((wise (x:=x) _ p _ _ A.k).symm))
 have hF:costU (M.bell x)=costU (H.bell x):=by unfold costU; simp_rw [SectorChange.price_square,tape.apply_symm_apply]; refine sum_congr rfl fun i _=>?_; rw [show ‖H.bell x i‖ = _ from (SU.group.norm_adjoint (constantGauge g S.ratio i.val.val.1) (M.bell x i))]
 have heA:=hh' H; rw [hh,←hF,←hh' M] at heA; unfold aster at heA; change _= _; unfold adjust; change sepB T x H q d l β+_= _; linarith only [hg,heA]
lemma swing_g(g:Site c→SU.group.El)(M:Monk SU.group S)(e:Bond f)(Y:Monk SU.group S→ℝ)(p:ContDiffAt ℝ (2:ℕ) (Y ∘ rough (shiftZ g M)) 0)(h:∀ i,Y (shiftZ g (rough M i))= Y (rough M i)): spring Y e M=spring Y e (shiftZ g M):=by
 let H:=shiftZ g M; let L:= Motion.swing (constantGauge g S.ratio); let Z:=Y ∘ rough H; let Q:= Y ∘ rough M; let U:=Z ∘ L; have he:Q=U:=funext fun i=>(h i).symm
 have hp:L (arrow e M.z)=arrow e (H.z):=by
    ext1 j; change _= _; change SU.group.adjoint _ (arrow e M.z j)= _
    by_cases h:j=e; · subst j; rw [arrow,Pi.single_eq_same,arrow,Pi.single_eq_same]; rfl
    unfold arrow; rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h,map_zero]
 have ht: ContDiffAt ℝ (2:ℕ) Z (L 0):=(map_zero L).symm ▸ p
 have hh(j:ℕ)(hj:j ≤ 2): iteratedFDeriv ℝ j U 0=(iteratedFDeriv ℝ j Z 0).compContinuousLinearMap (fun _=>L):=by unfold U; rw [Push.Uniform.iter_lin_at (ht.of_le (by exact_mod_cast hj)),map_zero]
 let z:=arrow e M.z; change fderiv ℝ Q 0 z+ hdot Q 0 M.z z/2=fderiv ℝ Z 0 _+ _; rw [he]; suffices h : hdot U 0 M.z z= hdot Z 0 H.z (arrow e H.z) from (congrArg₂ (·+·) ?_ (congrArg (· / (2:ℝ)) h))
 · unfold U; rw [fderiv_comp _ (ht.differentiableAt (by norm_num)) L.differentiableAt,L.fderiv, map_zero,ContinuousLinearMap.comp_apply,show L z= _ from hp]
 rw [show hdot U 0 M.z z=iteratedFDeriv ℝ 2 U 0 ![M.z,z] from by rw [iteratedFDeriv_two_apply]; rfl, hh 2 le_rfl,ContinuousMultilinearMap.compContinuousLinearMap_apply,iteratedFDeriv_two_apply]; change hdot Z 0 H.z (L z)= _; rw [show L z= _ from hp]
end YM.CF.Cay
