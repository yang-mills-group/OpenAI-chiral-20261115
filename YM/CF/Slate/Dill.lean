import YM.CF.Slate.Coin
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
open Work.E03
local notation "G"=>SU.group
variable {K:Teller SU.group}{U V:Monk G S} {T:Tube G S}{X:Support c}
abbrev leadD(S:StepData c f): Dill S → Site c:= Sum.elim (fun v=> S.ratio.parent v.1) (Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst))
lemma ringT (i:Dill S){t:ℝ}{R:ℕ}(M N:Config G f)(k k': S.Choices)(A B:Config G c)(g:AgreeNear id (leadD S i) (4*R+8) A B)(h:AgreeNear S.ratio.parent (leadD S i) (4*R+8) M N)(v:AgreeNear id (leadD S i) (4*R+8) (S.prediction M k) (S.prediction N k')) : Yaught T R (fiery G t S.patch.L) (temp t) A M k i= Yaught T R (fiery G t S.patch.L) (temp t) B N k' i :=by
 let o:= leadD S i; let p(y:Site c):Prop:=separation o y ≤ R; let C:=4*R+8; have hc(x:Site c)(hx:p x):AgreeNear id x (3*R+8) A B:=g.shrink (by unfold p o at hx; omega)
 have hf(i:Twin c)(hx:separation o i.1.1 ≤ 2*R):T.Xn R A i=T.Xn R B i:=plotted_near id sep_step A B _ _ _ _ i S.patch.L.property (g.shrink (by simp only [id_eq]; unfold o at hx; omega)); have hF(i:Twin f)(hx:p (S.ratio.parent i.1.1)):T.Xf R M i=T.Xf R N i:=plotted_near S.ratio.parent (parent_step S) M N _ _ _ _ i le_rfl (h.shrink (by unfold p o at hx; omega)) -- p shadow
 have hr(ι:Type)(P:Config G c→ι→Twin c→Pay G)(m:ι→ Site c)(y:ι)(u:p (m y))(Z:∀ j,(R < separation (m y) j.1.1 → P A y j=0) ∧ (AgreeNear id (m y) R A B→ P A y j=P B y j)): zip (P A) (T.Xn R A) y=zip (P B) (T.Xn R B) y:=Lift.zipAt R A B _ y P (T.Xn R A) (T.Xn R B) Z (g.shrink (by unfold p o at u; omega)) fun j w=> hf j ((separation_triangle o (m y) _).trans (by unfold p at u; omega))
 have he(j:Bond c)(hx:p j.1): tideX S k A M j=tideX S k' B N j:=by
    unfold tideX; have hp:separation (leadD S i) (id j.1) ≤ 4*R+8:=by unfold p o at hx; simp only [id_eq]; omega
    rw [v j hp,g j hp]
 have hp(j:Bond c)(hx:p j.1):Tube.Z S (S.prediction M k) A j=Tube.Z S (S.prediction N k') B j:= congrArg (fun i:SU.group.El=>Real.sqrt S.kernel.penalty • SU.group.curvature i) (he _ hx) -- G notation
 have hX:p (leadD S i):=by simp [p,o]
 unfold Yaught; rcases i with i|i|i|i <;> simp only [Sum.elim_inl, Sum.elim_inr]
 · have hz: faceValue M i=faceValue N i:=travel_near _ (parent_step S) M N i.1 _ 4 le_rfl (h.shrink (by change separation (S.ratio.parent i.1) (S.ratio.parent i.1)+_ ≤_; simp only [separation_self]; omega)); rw [hiatus,hiatus,KissP,KissP,hz]; refine congrArg (fun x=> _*sore _ _+x) (sum_congr rfl fun j _=>?_) -- tune
   unfold RiftF; rw [hF (i,j) hX,hr _ (T.Φ R) (fun j=>S.ratio.parent j.1.1) (i,j) hX (Lift.vBand T R _ _ _)] -- tune
 · rw [iham,iham,RiftI,RiftI,hp i hX]; unfold KissI; rw [he i hX,hr _ (T.Φ' R) Prod.fst i hX (Lift.kickBand T R _ _ _)]
 · have hV: faceValue A i=faceValue B i:=travel_near id sep_step A B i.1 _ 4 le_rfl (g.shrink (by change separation i.1 i.1+_≤_; simp only [separation_self]; omega)); rw [inka,inka,zpia,zpia,KissQ,KissQ,hV]; apply congrArg (-(_*sore _ _)+·); apply sum_congr rfl; intro j _
   let m(y:Twin f):= S.ratio.parent y.1.1; let P:= T.Xn R A; have hJ: AgreeNear id i.1 (2*R) A B:=g.shrink (by change separation i.1 i.1+_≤ _; simp only [separation_self]; omega)
   unfold RiftL RiftD lGap dGap; rw [hf (i,j) (by change separation i.1 i.1≤_; simp), paidZip (T.Φ R) _ (T.Xf R N) m (i,j) R (Lift.vBand T R) hJ hF, paidZip (T.Φ' R) _ (Tube.Z S (S.prediction N k') B) Prod.fst (i,j) R (Lift.kickBand T R) hJ hp, paidZip (T.Φ R) (zip _ (T.Xn R A)) (zip _ (T.Xn R B)) m (i,j) R (Lift.vBand T R) hJ (fun z u=>hr _ (T.Φ R) m z u (Lift.vBand T R _ _ z)),paidZip (T.Φ' R) (zip _ (T.Xn R A)) (zip _ (T.Xn R B)) Prod.fst (i,j) R (Lift.kickBand T R) hJ (fun z u=>hr _ (T.Φ' R) _ z u (Lift.kickBand T R _ _ z)),paidZip (T.N R) (zip _ (T.Xn R A)) (zip _ (T.Xn R B)) Prod.fst (i,j) R (payBand T R) hJ (fun z u=>hr _ (T.N R) _ z u (payBand T R _ _ z))]
 rw [nk,nk]; unfold RiftN; rw [hr _ (T.N R) Prod.fst i hX (payBand T R _ _ _)]
end YM.CF.Slate
