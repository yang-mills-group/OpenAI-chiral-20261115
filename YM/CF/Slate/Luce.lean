import YM.CF.Vol.Slush
import YM.CF.Vol.Pallas
import YM.CF.Forge.Out
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
abbrev skyB(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(b:Slots S)(u:Ark T F):= match b.2 with| .inl v=> OrnG T F k b.1 (Stores.till x) u v | .inr v=> OriG T F k b.1 (Stores.till x) u v
abbrev arcX(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(i:Slots S)(u:Mast G c):= let V:= facadeX G u; Offset.fixedBase T x V k i + gloss T x F k i (u,sol S T k x F l u)
lemma drop_x(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(i:Slots S)(v:Mast G c): Offset.fixedBase T x (facadeX G v) k i=skyB T x F k i (v,0):=by
 let t:= Stores.till x; let z:=choice i.1 k; have hx: Jazz T z i.1 (F:=F) (v,0) = facade S i.1 (facadeX G v) 0:=by rw [Jazz,←tray_x F x]; exact congrArg (pull i.1 0) (congrArg (increment (replica S.ratio (facadeX G v))) ((meal F x (G:=G)).map_zero)) -- tune facade
 unfold z at hx; rcases i with ⟨s,i|i⟩
 · unfold skyB OrnG Offset.fixedBase Offset.fixedF; dsimp only [Sum.elim_inl,RiftF]; change T.Xf t _ _ - _ = T.Xf t _ _-_; rw [show Jazz T (choice s k) s (F:=F) (v,0)=_ from hx]; rfl
 unfold skyB OriG Offset.fixedBase Offset.fixedI; dsimp only [Sum.elim_inr,RiftI]; rw [show Jazz T (choice s k) s (F:=F) (v,0)=_ from hx]; rfl
lemma arc_move(y:E→ A)(f g:E×A→G.Color)(h : DifferentiableAt ℝ f 0)(p:DifferentiableAt ℝ g 0)(ht:DifferentiableAt ℝ y 0)(v:y 0=0)(hp:∀ x,g (x,0)=0)(hq:∀ x:A,fderiv ℝ f 0 (0,x)= fderiv ℝ g 0 (0,x)) {D:ℝ}(he: stance (f ∘ (Vol.pulse y)- g) D)(hD:0≤D): stance (fun i:E=> f (i,0) + g (i, y i)) D:=by
 let x:E →L[ℝ] E×A:= ContinuousLinearMap.inl ℝ _ _; let Q:E→E×A:=fun t=> (t,y t); have ha: x 0=(0:E×A):=map_zero ..; have hh:Q 0=0:=Prod.ext rfl v
 let P(v:E×A):=Vol.pulse y v; have hv:(f ∘ P-g) ∘ x=(fun i:E=> f (i,y i)):=by ext1 i; change f (i,0+ _) - g (i,0)= _; rw [hp,sub_zero,zero_add]; rfl
 have hy:‖fderiv ℝ (f∘P-g) 0‖ ≤ D:=he.rud; have he': DifferentiableAt ℝ P 0:=differentiableAt_fst.prodMk (differentiableAt_snd.add (ht.comp (f:=Prod.fst) (0:E×A) differentiableAt_fst)); have hm:P 0=0:=by unfold P Vol.pulse; simp [v]
 have ho: DifferentiableAt ℝ (f∘P-g) (x 0):=by rw [ha]; exact ((hm.symm ▸ h).comp (f:=P) 0 he').sub p
 have hz: ‖fderiv ℝ (f∘ Q) 0‖ ≤ D:=by rw [show f ∘ Q= (f ∘ P-g) ∘ x from hv.symm, fderiv_comp _ ho x.differentiableAt,ha,x.fderiv]; exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul_of_nonneg_right hy (norm_nonneg _)).trans (mul_le_of_le_one_right hD (x.opNorm_le_bound zero_le_one fun y=> by rw [one_mul]; exact max_le le_rfl (by change ‖(0:A)‖≤ _; simp))))
 let W :=(fun i:E=> f (i,0) + g (i,y i)); have hi :g (0:E×A)=0:=hp 0; have hΓ:= he.origin; change f (P 0)-g 0=0 at hΓ; rw [hm,hi,sub_zero] at hΓ
 refine ⟨by rw [v,hp,(show f (0,0)=0 from hΓ),add_zero], ?_⟩
 have hA : HasFDerivAt Q ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ y 0)) 0:= ((ContinuousLinearMap.id ℝ E).hasFDerivAt).prodMk ht.hasFDerivAt
 refine (show fderiv ℝ W 0 = fderiv ℝ (f∘Q) 0 from ?_) ▸ hz
 have hr:= ( ( ( (show DifferentiableAt ℝ f (x 0) from ha.symm ▸ h).hasFDerivAt).comp (f:=x) (0:E) x.hasFDerivAt)).add (( (show DifferentiableAt ℝ g (Q 0) from hh.symm ▸ p).hasFDerivAt).comp (f:=Q) (0:E) hA); rw [ha,hh] at hr; have hp' := ( (show DifferentiableAt ℝ f (Q 0) from hh.symm ▸ h).hasFDerivAt).comp _ hA; rw [hh] at hp'; rw [show W=(f ∘ x)+(g ∘ Q) from rfl,hr.fderiv,hp'.fderiv];
 ext1 t; let d:=fderiv ℝ y 0 t; let L:=fderiv ℝ g 0; have hi: L (t,0)=0:=by
    have he(y:E):g (x y)=0:=hp y; have hh:g∘x=fun _=>0:= funext he; let hq:= (ha.symm ▸ p).hasFDerivAt.comp (f:=x) 0 x.hasFDerivAt; rw [ha,hh] at hq; exact DFunLike.congr_fun (hq.unique (hasFDerivAt_const ..)) t
 change fderiv ℝ f _ (t,0)+ L (t,d)= fderiv ℝ f _ (t,d); rw [show (t,d)= (t,(0:A))+(0,d) from Prod.ext (add_zero _).symm (zero_add _).symm,map_add,map_add,hi,zero_add,hq]
end YM.CF.Slate
