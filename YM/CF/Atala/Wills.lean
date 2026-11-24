import YM.CF.Atala.Match
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Atala
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}
open CF.Forge
lemma fills_l (F:Forest S.ratio)(U:Config G f)(y:Site c) (k:∀ i∈F.trunks, S.ratio.parent i.1=y→U i=1) (u:Site f) (p:S.ratio.parent u=y): F.foldAt U u=1:=by
 induction u using Forest.hike.induct F with
 | case1 i h ih=>
   let V:=(F.up i).used i; have hv:V∈F.trunks:=(F.trunk_mem_iff V).mpr ⟨i,h,rfl⟩; have hs:S.ratio.parent V.1=y:=by
      have he:=sits (F:=F) hv; unfold V at *; cases g:F.up i with| mk j d=>
       cases d
       · exact p
       rw [g] at he; simpa [Step.used] using he.symm.trans (by simpa [Step.used] using p) -- tune
   have ht: (F.up i).read U i=1:=by unfold Step.read; rw [k _ hv hs]; split <;> simp
   have hh:= F.fold_step U h; rw [ht,ih ((F.stays i h).trans p),mul_one] at hh; exact hh
 | case2 i h=> rw [show i=S.ratio.embed (S.ratio.parent i) from Classical.not_not.mp h,F.fold_root]
lemma less_fl{a b:ℝ}(U: Config G f)(h:a≤b):flags b U ⊆ flags a U:=fun i t=>by obtain ⟨i',p,k⟩:= (flags_spec ..).mp t; exact (flags_spec ..).mpr ⟨_,p,h.trans_lt k⟩
open Cube
lemma win_r{k:ℕ}{i:reach c}{j:Seat c}(p:j∈win k i): separation j i.1 ≤ k+1:=by
 obtain ⟨u,p,h⟩:=halo_spec.mp p; rw [separation_comm] at h; apply (separation_triangle _ u i.1).trans; simp at p; rcases p with p|p; subst u; simp; omega; subst u; apply Nat.add_le_add h; rw [separation_comm]; exact Work.E01.sep_step_le .. -- tune
local notation "G"=> SU.group
variable {S:StepData (More c) (More f)}{T:Tube SU.group S}{M:Monk SU.group S}{a b u t:ℝ}{k k':ℕ}{P:Loom c}{V:Loom f}
open Rush
lemma bridgeV (K:Ratio c f)(hK:S.ratio=ratio K) (q':Chi)(hv:Bell S M x T q d l β a b) (hr:Roof c a u k P)(hp: Roof f a t k' V) (hz:k+k' ≤ radiusB x)(h:0<b)(hb:b<firstRadius SU.group)(A:Ids c)(Y:Ids f)(i:reach f) (he:S.ratio.parent i.1 ∉ M.key.dome (20*radiusB x)) :
 let W:= V (M.sent x T q d l β,Y)
 let F:Forest (ratio K):= hK ▸ M.park
 seine K F q' b W (P (M.V,A)) i = W i ∧ W i=M.sent x T q d l β i∧ replica S.ratio (P (M.V,A)) i=replica S.ratio M.V i:=by
 let R:=radiusB x; intro W F; let Q:=M.park; have hx:=hv.years; have ht{e:reach f}(p:S.ratio.parent e.1∉ M.key.dome (19*R)):W e=M.sent x T q d l β e:=by
    refine hp.lamp _ _ e (disjoint_left.mpr fun y g t=> ?_); have hj:= Work.E04.parent_separation S.ratio y e.1; apply p (dome_u (hv.reach _ g) ?_); have he:=win_r t; unfold R; omega
 have hk0:S.ratio.parent i.1∉ M.key.dome (11*R):=fun t=>he (dome_u t (by simp [R]; first|done|omega)) -- tune
 have hk:S.ratio.parent i.1 ∉ M.key.dome (19*R):=fun t=> he (dome_u t (by simp [R]; first|done|omega))
 have hK'(j): Q.foldAt W j=F.foldAt W j :=by -- cast Forest by equality of ratio, foldAt
    have hz(C C':Ratio (More c) (More f))(Y:Forest C)(p:C=C'): let V:Forest C':=p ▸ Y; Y.foldAt W j=V.foldAt W j:=by subst C; rfl
    exact hz _ _ Q hK
 have hy (z:Site (More c))(p:z∉ M.key.dome (19*R)) (y:Site (More f))(g:S.ratio.parent y=z):F.foldAt W y=1:=by
    rw [← hK']; apply fills_l (S:=S) Q W z _ y g; intro i j l; rw [ht (l.symm ▸ p),tipS _ j]
 have hr1: F.foldAt W i.1=1:=hy _ hk _ rfl
 have hr2: F.foldAt W (i.1+step i.2)=1:=by
    have h:S.ratio.parent (i.1+step i.2)∉ M.key.dome (19*R):=fun v=>he (dome_u v (by rw [separation_comm]; have h:=Work.E03.parent_step S i.1 i.2; unfold R; omega))
    exact hy _ h _ rfl
 have hW:replica S.ratio (P (M.V,A)) i=replica S.ratio M.V i:=by
    unfold Precision.replica; split; rfl
    refine hr.lamp _ _ _ (disjoint_left.mpr fun j z p=> hk0 ?_); let Z:=S.ratio.parent i.1; have hh:j∈ M.key.flags := hv.height ((less_fl M.V hv.tax) z); have hg:separation j Z ≤ k+1:= win_r p; exact halo_spec.mpr ⟨j,mem_union_right _ hh,hg.trans (by unfold R; omega)⟩
 have hh:= ht hk
 refine ⟨?_,hh,hW⟩; unfold seine portU Lattice.gauge
 simp only [Pi.inv_apply,hr1,hr2,inv_one,mul_one,one_mul]; rw [show Precision.replica (ratio K) (P (M.V,A)) i= _ from (congrArg (fun R=> Precision.replica R (P (M.V,A)) i) hK.symm).trans hW,hh]; obtain ⟨z,t,g⟩:= highs (by omega) h.le hv.low i hk0; exact knitHere _ _ _ _ h hb ⟨z,t,g⟩
end YM.CF.Atala
