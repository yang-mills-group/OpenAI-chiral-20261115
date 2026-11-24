import YM.CF.Souk.Hill
/-! Trace-delta norms for true thermal. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Souk
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt Hors Neige
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt address Primary tint Multiplicity countCost)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
variable {ι τ:Type} [Fintype ι][Fintype τ] [DecidableEq τ]
open Planned.JetPort Finset
-- compressed Haar val for joint chart. actually entropy ℓ¹ not op∞.
abbrev Eman (F:Forest S.ratio)(i:F.Free) : Positions (Uniform.Joint F G)→L[ℝ] G.Color:= LinearMap.toContinuousLinearMap { toFun:=fun x=>((Uniform.paint F G) x).2 i,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
def addH(F:Forest S.ratio)(p:ChartRatio G)(x:Fish (Uniform.Joint F G)):= Real.log (∏ i:F.Free, p.J (Eman F i x))
lemma shrine(j:ℕ)(p:ChartRatio G)(hp:LocalRatio p): ContDiffAt ℝ (j:ℕ) (fun x=> Real.log (p.J x)) (0:G.Color):=by
 have hx:=(mem_ball_self (x:=(0:G.Color)) hp.patch); exact ((hp.germ 0 hx).log (hp.pos _ hx).ne').of_le le_top
lemma e_norm(i:F.Free)(j:Uniform.Joint F G): ‖Eman F i (bolt j)‖ ≤  Uniform.shade G:=by
 let Z:= (tint G F.Free); let K:=((Uniform.partSpace (Primary c G) (Key F G)) (bolt j)).2
 apply le_trans (b:=‖Z K‖) (norm_le_pi_norm ..) ((Uniform.tint_le _).trans (mul_le_of_le_one_right (Uniform.shade_pos _).le ?_)); exact (norm_snd_le _).trans ((Uniform.parts_isometry (bolt j)).trans_le ((Uniform.norm_bolt ..).le))
lemma lonely (F:Forest S.ratio)(k:ℕ)(q:Fin (k+1)→Uniform.Joint F G)(p:ChartRatio G)(hp:LocalRatio p):
 let Z:= (fun x=> Real.log (p.J x)); let A:= ‖iteratedFDeriv ℝ (k+1) Z 0‖*Uniform.shade G^(k+1)
 ContDiffAt ℝ (k+1:ℕ) (addH F p) 0 ∧ |Uniform.entry (addH F p) 0 q| ≤ A:=by
 intro Z A; let L(i:F.Free):= Eman F (G:=G) i; let U(i:F.Free):=Z ∘ L i; have hg(i):ContDiffAt ℝ (k+1:ℕ) Z (L i 0):=by rw [map_zero]; exact shrine _ _ hp
 have hv(i): ContDiffAt ℝ (k+1:ℕ) (U i) 0:=(hg i).comp _ (L i).contDiff.contDiffAt
 have hA:0 ≤ A:= mul_nonneg (norm_nonneg _) (pow_nonneg (Uniform.shade_pos _).le _)
 have he : addH F p =ᶠ[𝓝 0] ∑ i:F.Free,U i:=by
    have hh(i:F.Free):∀ᶠ x in 𝓝 (0: Positions (Uniform.Joint F G)), p.J (L i x) ≠0:=((L i).continuous.continuousAt.eventually (p:=fun y=> y∈ball (0:G.Color) p.radius) (by rw [map_zero]; exact ball_mem_nhds _ hp.patch)).mono fun i hi=> (hp.pos _ hi).ne'
    filter_upwards [eventually_all.mpr hh] with x hx; unfold addH; rw [Real.log_prod (fun i _ => hx i), Finset.sum_apply]; rfl
 have hh(i:F.Free): Uniform.entry (U i) 0 q= iteratedFDeriv ℝ (k+1) Z 0 (fun j=> L i (bolt (q j))):=by unfold Uniform.entry U; rw [Uniform.iter_lin_at (hg i),map_zero]; exact rfl
 have ht: Uniform.entry (addH F p) 0 q= ∑ i:F.Free,Uniform.entry (U i) 0 q:=by unfold Uniform.entry; rw [(he.iteratedFDeriv ℝ (k+1)).eq_of_nhds, iteratedFDeriv_sum_apply (fun i _=> hv i),_root_.sum_apply]
 rw [ht]; refine ⟨ContDiffAt.congr_of_eventuallyEq ?_ he,?_⟩
 · exact (ContDiffAt.sum (s:=Finset.univ) (f:=U) (fun i _=> hv i)).congr_of_eventuallyEq (Eventually.of_forall fun y=>Finset.sum_apply y _ U)
 cases hx:q 0 with
 | inl v=>
    rw [Finset.sum_eq_zero]; exact (abs_zero.le.trans hA); intro i _; rw [hh,ContinuousMultilinearMap.map_coord_zero _ 0]; rw [hx]; ext j; change bolt (Sum.inl v) (Sum.inr (i,j))=(0:ℝ); simp [Uniform.bolt]
 | inr v=>
    rw [sum_eq_single v.1,hh]; swap -- verify order
    · intro b hb hp; rw [hh,ContinuousMultilinearMap.map_coord_zero _ 0]; rw [hx]; ext j; change bolt (Sum.inr v) (Sum.inr (b,j))=(0:ℝ); simp [Uniform.bolt, Pi.single_apply, show (b,j) ≠ v from fun k=>hp (congr_arg Prod.fst k)]
    · exact (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (le_refl ‖iteratedFDeriv ℝ (k+1) Z 0‖) (fun j=> e_norm v.1 (q j))).trans_eq (by change ‖_‖ * (∏ _:Fin (k+1),Uniform.shade G)=A; simp [A])
    simp
lemma wealth(P:ChartRatio G)(hp: LocalRatio P): ∃ A:ℝ,0<A ∧∀ {c f:Side}(S:StepData c f)(F:Forest S.ratio), FloorZ (addH F P) A:=by
 let f(x):=Real.log (P.J x); let D(i):= ‖iteratedFDeriv ℝ i f 0‖ * Uniform.shade G^i; let A:=1+D 1+D 2; have he(i):0 ≤ D i:= mul_nonneg (norm_nonneg _) (pow_nonneg (Uniform.shade_pos _).le _)
 refine ⟨A,by unfold A; linarith only [he 1,he 2],?_⟩
 intro c f S F
 by_cases hv : Nonempty (Uniform.Joint F G)
 · exact ⟨(by simpa using (lonely F 1 (fun i=>Classical.arbitrary _) P hp).1), fun i=>(lonely F _ i P hp).2.trans (show D 1 ≤ A from by unfold A; linarith only [he 2]), fun i=>(lonely F 1 i P hp).2.trans (show D 2 ≤ A from by unfold A; linarith only [he 1])⟩
 have he: Subsingleton (Fish (Uniform.Joint F G)):=⟨fun x y=>funext fun i=> False.elim (hv ⟨i⟩)⟩; haveI := he; exact ⟨by rw [show addH F P=(fun x=> addH F P (0:Fish _)) from funext fun i=> congr_arg _ (Subsingleton.elim i _)]; exact contDiffAt_const,fun i=> False.elim (hv ⟨i 0⟩),fun i=> False.elim (hv ⟨i 0⟩)⟩
abbrev inLoop(K:ℕ→Atom G 2)(F:Forest S.ratio)(p:Fish (Uniform.Joint F G)):=Patch.average fun i:Signed=> uncut K (Uniform.signedFine F p i)
lemma alum(F:Forest S.ratio)(K:ℕ→Atom G 2)(p:SumBudget (fun i=> (K i).budget s) C)(hs:0<s)(h:Uniform.PaintSupply G 2 A):FloorZ (inLoop K F) (C*Newt.fareX G 2 2 A s S.patch.L):=by
 let a:=Uniform.entryWidth 2 S.patch.L s -- tune
 let c:=Uniform.weaker 2 a
 have hQ:Wax (inLoop K F) 0 2 c (C*Newt.fareX G 2 2 A s S.patch.L):= Wax.average fun i=> atomX hs h i K p (mem_ball_self zero_lt_one)
 have hp(j:ℕ)(hj:j<2)(v:Fin (j+1)→ _): |Uniform.entry (inLoop K F) 0 v| ≤ (C*Newt.fareX G 2 2 A s S.patch.L) :=by
    have ht:=hQ.hv _ (by omega) v 0; refine ht.trans (mul_le_of_le_one_right ?_ (Real.exp_le_one_iff.mpr ?_))
    · have hh:=Uniform.atomCost_nn h hs 2; apply mul_nonneg ((tsum_nonneg p.1).trans p.2.2) (mul_nonneg hh (Uniform.count_pos (half_pos (Uniform.width_positive hs 2 S.patch.L))).le)
    have hc:0<c:= div_pos (Uniform.width_positive hs 2 S.patch.L) (by positivity); exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by positivity)
 exact ⟨hQ.he.of_le le_top,hp 0 (by decide),hp 1 (by decide)⟩
lemma short_ix(F:Forest S.ratio)(R:PathData G)(p:SumBudget (fun i=>(R.loop i).budget s) C)(hs:0<s)(j:ℕ): inLoop R.loop F-inLoop (Vol.batch R.loop j) F=inLoop (haste j R.loop) F:=by
 ext i; simp only [Pi.sub_apply, inLoop, Patch.average, uncut, ← mul_sub, ← Finset.sum_sub_distrib]; congrm _ * ?_; refine Finset.sum_congr rfl (fun k _=>Finset.sum_congr rfl fun x _=>?_); rw [uncut_high _ hs p]; unfold Vol.batch; abel
end YM.CF.Souk
