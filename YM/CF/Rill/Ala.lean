import YM.CF.Err.Bell
import YM.CF.Atala.Wills
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
-- chart
variable {F E D:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
open LocalH CF.Err
abbrev FoldK(V W:Config G c):Directions G c:=fun i=> snap G (W i*(V i)⁻¹)
lemma veil (V:Config G c) :
 FoldK V V=0∧ContinuousAt (FoldK V) V ∧ ∀ᶠ W in 𝓝 V,increment V (FoldK V W)=W:=by
 let R:Directions G c:=FoldK V V
 have hh : snap G 1=0:=by have he:=SU.group.plog_left.self_of_nhds; simpa [snap] using he
 refine ⟨funext fun i=>by unfold FoldK; rw [mul_inv_cancel]; exact hh,continuousAt_pi.mpr fun i=>?_ ,?_⟩
 · exact (show ContDiffAt ℝ ω SU.group.plog (SU.group.mat (V i*(V i)⁻¹)) from by rw [mul_inv_cancel,SU.group.mat_one]; exact SU.group.plog_diff).continuousAt.comp (f:=fun W:Config G c=>SU.group.mat (W i*(V i)⁻¹)) ((SU.group.continuous_mat.comp (show Continuous (fun W:Config G c => W i*(V i)⁻¹) by fun_prop)).continuousAt)
 have he(i:Bond c):∀ᶠ W in 𝓝 V,increment V (FoldK V W) i=W i:=by
    let g(W:Config G c):=W i*(V i)⁻¹; have ht:Tendsto g (𝓝 V) (𝓝 1):=by rw [show (1:SU.group.El)=g V from (mul_inv_cancel _).symm]; exact (show Continuous g from by unfold g; fun_prop).continuousAt
    filter_upwards [ht.eventually SU.group.plog_right] with W hw; change SU.group.lieExp (SU.group.plog (SU.group.mat (g W))) * V i=W i; rw [hw]; unfold g; simp [mul_assoc]
 filter_upwards [eventually_all.mpr he] with W hw using funext hw
abbrev Rain(K:Side) (E:Type*):= Directions G K× E
abbrev Tilt(c f:Side)(E:Type*):= Config G c× Config G f × E
abbrev RingP(c f:Side)(E:Type*):= Directions G c × Rain f E
def raiseW (P:Tilt c f E)(x: RingP c f E): Tilt c f E:= (increment P.1 x.1,increment P.2.1 x.2.1,x.2.2+ P.2.2)
def bank (P Q:Tilt c f E): RingP c f E:= (FoldK P.1 Q.1,FoldK P.2.1 Q.2.1,Q.2.2-P.2.2)
lemma scrub (P:Tilt c f E): raiseW P 0=P:=by simp [raiseW]
lemma stepU(P:Tilt c f E):Continuous (raiseW P):=by unfold raiseW increment; fun_prop
lemma willow (P:Tilt c f E): bank P P=0∧ContinuousAt (bank P) P∧ ∀ᶠ Q in 𝓝 P, raiseW P (bank P Q)=Q:=by
 obtain ⟨p,t,h⟩:=veil P.1; obtain ⟨v,k,l⟩:=veil P.2.1; refine ⟨by unfold bank; simp_rw [p,v,sub_self]; rfl,(t.comp continuousAt_fst).prodMk ((k.comp (f:=fun x:Tilt c f E=>x.2.1) (by fun_prop)).prodMk ((Continuous.continuousAt (show Continuous (fun x:Tilt c f E=>x.2.2) from by fun_prop)).sub continuousAt_const)),?_⟩
 filter_upwards [continuousAt_fst (p:=P)|>.eventually h, (continuousAt_fst.comp (continuousAt_snd (p:=P))).eventually l] with Q r q; change increment P.2.1 (FoldK P.2.1 Q.2.1)=Q.2.1 at q; simp only [raiseW,bank,sub_add_cancel,q,r,Prod.mk.eta] -- tune
-- local structure
variable (Z:Tilt c f E→ F){P:Tilt c f E}
def crest (t:Tilt c f E):= iteratedFDeriv ℝ l (Z ∘ raiseW t) 0 -- l implicit
abbrev CurlP (t:Tilt c f E): Prop:= ContDiffAt ℝ (↑l) (Z ∘ raiseW t) 0
lemma wet (h:CurlP (l:=l) Z P): ContinuousAt Z P:=by
 obtain ⟨p,t,v⟩:=willow P; have he:ContinuousAt (Z ∘ raiseW P) (bank P P):=p.symm ▸ h.continuousAt; exact (he.comp (f:=bank P) t).congr_of_eventuallyEq (v.mono fun i p=> congrArg Z p.symm)
lemma woodP(P:Tilt c f E):
 ContDiffAt ℝ (↑l) (fun i: RingP c f E× RingP c f E=> bank P (raiseW (raiseW P i.1) i.2)) 0:=by
 let W(i:RingP c f E × RingP c f E):=raiseW (raiseW P i.1) i.2
 have he:W 0=P:=by unfold W; simp_rw [Prod.fst_zero,Prod.snd_zero,scrub]
 -- helper
 have ht{N:Type}[NormedAddCommGroup N][NormedSpace ℝ N](P:SU.group.El)(U V:N→ SU.group.Color)(h:ContDiffAt ℝ (↑l) U 0)(v:ContDiffAt ℝ (↑l) V 0)(q:U 0=0)(y:V 0=0): ContDiffAt ℝ (↑l) (fun i=> snap G (SU.group.lieExp (V i)*(SU.group.lieExp (U i)*P)*P⁻¹)) 0:=by
    let F(i:N):=SU.group.lieExp (V i)*(SU.group.lieExp (U i)*P)*P⁻¹; have he:F 0=1:=by simp [F,q,y]
    refine ContDiffAt.comp (f:=SU.group.mat ∘ F) (g:=SU.group.plog) 0 ?_ ?_
    · simp only [Function.comp_apply,he,Gauge.mat_one]; exact SU.group.plog_diff.of_le le_top
    let Gx :=SU.group.exp_jet; unfold F; simp_rw [Function.comp_def, Gauge.mat_mul]; exact (((Gx.contDiffAt.of_le (m:=↑l) le_top|>.comp _ v).mul (((Gx.contDiffAt.of_le (m:=↑l) le_top|>.comp _ h).mul contDiffAt_const))).mul contDiffAt_const)
 refine ContDiffAt.prodMk (f:=fun i: RingP c f E × RingP c f E=> FoldK P.1 (W i).1) (g:=fun i=>(FoldK P.2.1 (W i).2.1,(W i).2.2-P.2.2)) ?_ (ContDiffAt.prodMk ?_ ?_)
 · exact contDiffAt_pi.mpr fun j=> ht (P.1 j) (fun x:RingP c f E × RingP c f E=> x.1.1 j) (fun x:RingP c f E × RingP c f E=> x.2.1 j) (by fun_prop) (by fun_prop) rfl rfl
 · exact contDiffAt_pi.mpr fun j=> ht (P.2.1 j) (fun x:RingP c f E × RingP c f E=> x.1.2.1 j) (fun x:RingP c f E × RingP c f E=> x.2.2.1 j) (by fun_prop) (by fun_prop) rfl rfl
 unfold W raiseW; dsimp only; fun_prop
lemma rose (h:CurlP (l:=l) Z P) : ContDiffAt ℝ (↑l) (fun i: RingP c f E × RingP c f E=>Z (raiseW (raiseW P i.1) i.2)) 0:=by
 let Wa(i:RingP c f E × RingP c f E):=raiseW (raiseW P i.1) i.2; have hp:Wa 0=P:=by unfold Wa; simp_rw [Prod.fst_zero,scrub,Prod.snd_zero,scrub]
 obtain ⟨ht,p,H⟩:=willow P; have hz: bank P (Wa 0)=0:=hp ▸ ht; have he:Tendsto Wa (𝓝 0) (𝓝 P):=by rw [←hp]; exact (show Continuous Wa from by unfold Wa raiseW increment; fun_prop).continuousAt
 exact (((show ContDiffAt ℝ (↑l) (Z ∘ raiseW P) (bank P (Wa 0)) from hz.symm ▸ h).comp (f:=bank P ∘ Wa) 0 (woodP P))).congr_of_eventuallyEq ((he.eventually H).mono fun i p=> congrArg Z p.symm)
-- chart field tender
lemma stamp (h:CurlP (l:=l) Z P):∀ᶠ t in 𝓝 P,CurlP (l:=l) Z t:=by
 obtain ⟨p,t,v⟩:=willow P
 let yz(t:Tilt c f E):= (bank P t,(0: RingP c f E))
 have he:Tendsto yz (𝓝 P) (𝓝 0):=by rw [show (0:_)=yz P from ?_]; exact t.prodMk continuousAt_const; unfold yz; simp_rw [p]; rfl
 let a(t:RingP c f E × RingP c f E):= Z (raiseW (raiseW P t.1) t.2)
 filter_upwards [he.eventually ((rose Z h).eventually (by simp)),v] with y hy hw
 change ContDiffAt ℝ (↑l) (Z ∘ raiseW y) 0
 convert (show ContDiffAt ℝ (↑l) (fun i=>a (bank P y,i)) 0 from (show ContDiffAt ℝ (↑l) a (bank P y,0) from hy).comp (f:=fun i=> (_,i)) 0 (by fun_prop)) using 1; funext i; simp [a,hw]
end YM.CF.Rill
