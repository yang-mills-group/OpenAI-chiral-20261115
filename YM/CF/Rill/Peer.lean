import YM.CF.Rill.Bird
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
open Err
variable {M N:Monk G S}{e b w K t:ℝ} {U V:Config G c}{E F:Support c} {T:Tube G S}
open Atala
variable {a b':ℝ}
structure PaneL (M:Monk G S)(E:Support c) (x e b:ℝ) (Z:Config G f): Prop where
 stampK: SeeW M.V e E M.key.flags
 mindF: SeeW Z e (Passage S E) (Passage S (M.key.dome (12*radiusB x)))
 farF(i:Bond f):S.ratio.parent i.1∈E → S.ratio.parent i.1 ∉ M.key.dome (20*radiusB x)→ Z i * (replica S.ratio M.V i)⁻¹ ∈ SU.group.lieExp '' ball 0 b
set_option maxHeartbeats 1700000 in
lemma uplift(p:Beat M N F)(hr:Ready T x)(g:Agrees F M.V V)(u:F∩ RG.flags (temp x) V⊆M.key.flags) (h:Bell S N x T q d l β a b)(t:a<e)(hx:b<b')(hb:0<b)(hg:1000≤radiusB x)(z:halo ((l+70)*radiusB x) E⊆F): PaneL M E x e b' (M.sent x T q d l β):=by
 let X:= M.sent x T q d l β; let Z:= N.sent x T q d l β; let R:=radiusB x; let K:=(l+70)*R
 have hh : halo 13 E ⊆ F:= fun i k=> z ((Corona.halo_mono (by simp_rw [Nat.add_mul]; omega : 13≤(l+70)*radiusB x) (Subset.refl _)) k); have hW:E⊆ F:=(halo_subset 13 _).trans hh
 have he {y:Site f}(k:S.ratio.parent y∈halo 13 E): Beat.shadows (o:=S.ratio.parent y) F ((l+62)*R):=by
    intro i v; obtain ⟨j,p,t⟩:=halo_spec.mp k; obtain ⟨u,g,w⟩:=halo_spec.mp v; rw [mem_singleton.mp g] at w; refine z (halo_spec.mpr ⟨j,p,(separation_triangle j (S.ratio.parent y) i).trans (by unfold R at w; simp_rw [Nat.add_mul] at *; omega)⟩)
 refine ⟨fun i l' j w=>?_ ,fun i l' j w=>?_ ,fun i hq hu=>?_ ⟩
 · rw [show faceValue _ _=faceValue V j from ?_]; swap; · refine travel_local _ _ _ _ fun a u e=> g _ (hh (halo_spec.mpr ⟨i,l',(terrain w (List.mem_toFinset.mpr u)).trans (by omega)⟩)) (hh (halo_spec.mpr ⟨i,l',(terrain w (List.mem_toFinset.mpr e)).trans (by omega)⟩))
   by_cases p:i∈M.key.flags; exact Or.inr p; exact Or.inl (lt_of_le_of_lt ((le_of_not_gt (fun v=> p (u (mem_inter.mpr ⟨hW l',(flags_spec ..).mpr ⟨_,w,v⟩⟩)))) : SU.group.chord (faceValue V j) ≤ temp x) (h.tax.trans_lt t))
 · suffices faceValue X j=faceValue Z j by
      change SU.group.chord (faceValue X j)< e ∨ i∈_; rw [this]; by_cases k:SU.group.chord (faceValue Z j) ≤ a; exact Or.inl (k.trans_lt t)
      apply Or.inr; refine mem_filter.mpr ⟨mem_univ _,p.sym.same (he (y:=i) (halo_subset 13 _ ((mem_filter.mp l').2))) (h.reach i ((flags_spec ..).mpr ⟨j,w,lt_of_not_ge k⟩)) ?_⟩; rw [separation_self]; unfold R; simp_rw [Nat.add_mul]; omega
   exact travel_local _ _ _ _ fun a u e=> p.backF hr hg a (he (mem_filter.mp (parent_hK _ (halo_spec.mpr ⟨i,l',terrain w (List.mem_toFinset.mpr u)⟩)) |>.2))
 let o:= S.ratio.parent i.1; have hp:Beat.shadows (o:=o) F ((l+62)*R):= he (halo_subset 13 _ hq)
 have hg':S.ratio.parent i.1 ∉ N.key.dome (11*radiusB x):=by
    intro v; apply hu (Atala.dome_u (p.sym.same hp v (by unfold o R; rw [separation_self]; simp_rw [Nat.add_mul]; omega)) (by rw [separation_self]; omega))
 obtain ⟨w,t,g⟩:= Atala.highs (by omega) hb.le h.low i hg'
 rw [p.backF hr hg i hp, g]; unfold replica; split; · simp only [mul_one,inv_one]; exact ⟨_,mem_ball_zero_iff.mpr (t.trans_lt hx),rfl⟩
 rw [p.view _ (hW hq) (hh (halo_spec.mpr ⟨o,hq,(Work.E01.sep_step_le o _).trans (by omega)⟩)),mul_assoc,mul_inv_cancel,mul_one]; exact ⟨_,mem_ball_zero_iff.mpr (t.trans_lt hx),rfl⟩
structure MarkP (M:Monk G S)(E:Support c) (x e b:ℝ) (Y:Tilt c f (Foil f))(l n:ℕ)(T:Tube G S)(q:Chi)(d:ℝ):Prop extends PaneL (monkD M Y) E x e b (legL M T x q d l Y) where
 tea(i:Bond f): S.ratio.parent i.1∈halo 13 E → CurlP (l:=n) (fun u=> SU.group.mat (legL M T x q d l u i)) Y
lemma mead {P:HomeL c f}(h:MarkP M E x e b P l r T q d)(hQ:b<firstRadius G):∀ᶠ y in 𝓝 P,MarkP M E x e b y l r T q d:=by
 let W:= legL M T x q d l
 have hh(i:Bond f)(t:S.ratio.parent i.1∈halo 13 E):ContinuousAt (fun y=>W y i) P:=(SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (wet _ (h.tea i t))
 have ht(i:Bond f):∀ᶠ y in 𝓝 P, (S.ratio.parent i.1∈ E → S.ratio.parent i.1 ∉ M.key.dome (20*radiusB x)→ W y i * (replica S.ratio y.1 i)⁻¹ ∈ SU.group.lieExp '' ball 0 b) ∧ (S.ratio.parent i.1∈halo 13 E → CurlP (l:=r) (fun u=> SU.group.mat (W u i)) y):=by
    refine Eventually.and ?_ ?_
    · by_cases p:S.ratio.parent i.1∈E; swap; · exact Eventually.of_forall fun _ u=> (p u).elim
      by_cases k:S.ratio.parent i.1∈M.key.dome (20*radiusB x); · exact Eventually.of_forall fun _ _ p=>(p k).elim
      let g(y:HomeL c f):= W y i* (replica S.ratio y.1 i)⁻¹; have hy:ContinuousAt g P:= (hh _ (halo_subset 13 _ p)).mul ((show ContinuousAt (fun y:HomeL c f=> replica S.ratio y.1 i) P from by unfold replica; split; exact continuousAt_const; fun_prop).inv)
      exact (hy.eventually (((LocalH.geom_patch G).choose_spec.2 b hQ.le).1.mem_nhds (h.farF i p k))).mono fun y hy _ _=>hy
    by_cases k:S.ratio.parent i.1 ∈ halo 13 E
    · exact (stamp _ (h.tea i k)).mono fun y hy _=> hy
    exact Eventually.of_forall fun _ p=> (k p).elim
 have hp:= cotton W (t':=P) (fun i p=>hh i ((mem_filter.mp (parent_hK _ p)).2)) h.mindF; have hv:= cotton Prod.fst (t':=P) (fun i p=> Continuous.continuousAt ((continuous_apply i).comp continuous_fst)) h.stampK
 filter_upwards [eventually_all.mpr ht,hp,hv] with y w hp hv; exact ⟨⟨hv,hp,fun i=>(w i).1⟩,fun i=>(w i).2⟩
end YM.CF.Rill
