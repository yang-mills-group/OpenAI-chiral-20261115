import YM.CF.Vol.Mile
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment
abbrev Ark(T:Tube G S)(F:Forest S.ratio):Type:= Mast G c× Fish (Key F G)
def windowH(T:Tube G S)(F:Forest S.ratio) (x:Ark T F):= Work.F03.inclusion F (tint G _ x.1,tint G _ x.2)
lemma snap_Q :windowH T F 0=0:= inclusion_zero F
lemma shotQ :DifferentiableAt ℝ (windowH T F) 0:=by
 let U: Ark T F →L[ℝ] Work.F03.ChartVars F G:= ((tint G _).prodCongr (tint G _)).toContinuousLinearMap
 apply (show DifferentiableAt ℝ (Work.F03.inclusion F) (U 0) by rw [map_zero]; exact (inclusion_smooth F).differentiableAt (by simp)).comp (f:=U) 0 U.differentiableAt
lemma Q_d(u:Ark T F):fderiv ℝ (windowH T F) 0 u= (tint G _ u.1, Bid.stretch (S:=S) F (tint G _ u.1,tint G _ u.2)):=by
 let U: Ark T F →L[ℝ] Work.F03.ChartVars F G:= ((tint G _).prodCongr (tint G _)).toContinuousLinearMap
 rw [show windowH T F=(Work.F03.inclusion F ∘ U) from rfl,fderiv_comp _ _ U.differentiableAt,U.fderiv,map_zero,ContinuousLinearMap.comp_apply]; exact inclusion_deriv F _
 rw [map_zero]; exact (inclusion_smooth F).differentiableAt (by simp)
lemma plumbs (k:S.Choices)(s:Signed): Jazz (F:=F) T k s =ᶠ[𝓝 0] (pull s 0 ∘ (UP G c f)) ∘ (windowH T F) ∧ Jade (F:=F) T k s= (pull s 0 ∘ (VQ G c f)) ∘ (windowH T F):=by
 refine ⟨?_,rfl⟩
 let U: Ark T F →L[ℝ] Work.F03.ChartVars F G:= ((tint G _).prodCongr (tint G _)).toContinuousLinearMap
 have he: Tendsto U (𝓝 0) (𝓝 0):=by rw [← U.map_zero]; exact U.continuous.continuousAt
 filter_upwards [he.eventually (inclusion_works F)] with i hi; exact congrArg (pull s 0) hi.symm
lemma stamps (k:S.Choices)(s:Signed)(f': Config G f→ Config G c→ E) (u:Ark T F):
 let g(v):= f' ((pull s 0 ∘ (UP G c f)) v) ((pull s 0 ∘ (VQ G c f)) v)
 let h(v:Ark T F):=f' (Jazz T k s v) (Jade T k s v)
 DifferentiableAt ℝ g 0 → minor g (tint G _ u.1, Bid.stretch F (tint G _ u.1,tint G _ u.2)) C → minor h u C:=by
 intro g h hg hb; obtain ⟨ha,hH⟩:= plumbs (F:=F) (T:=T) k s; have hp:h =ᶠ[𝓝 0] g ∘ windowH T F:=ha.mono fun i hi=> congr_arg₂ f' hi (congr_fun hH i); unfold minor; rw [hp.self_of_nhds,Function.comp_apply,snap_Q,hp.fderiv_eq,fderiv_comp _ _ shotQ,snap_Q,ContinuousLinearMap.comp_apply,Q_d]; exact hb
 rw [snap_Q]; exact hg
lemma slew {z:Bid.Dir G c→AxisChart G F}(h:Critical F T.high T.up z)(hp:Guessed F (installed S.ratio T.R.A0) z)(x:Mast G c) : (tint G _) (fderiv ℝ (station z) 0 x)=relative F (installed S.ratio T.R.A0) (tint G _ x):=by
 let U:=tint G F.Free; let L:=tint G (Body 1 c); let D:=h.2.1.differentiableAt (by simp);
 have hh : fderiv ℝ (station z) 0 = ((U.symm.toContinuousLinearMap.comp (fderiv ℝ z 0)).comp L.toContinuousLinearMap):=by
    have hp:DifferentiableAt ℝ z (L 0):=by rw [map_zero]; exact D
    rw [show station z= (U.symm ∘ z) ∘ L from rfl,fderiv_comp _ (U.symm.differentiableAt.comp _ hp) L.differentiableAt,ContinuousLinearEquiv.fderiv,fderiv_comp _ U.symm.differentiableAt hp,ContinuousLinearEquiv.fderiv,map_zero]
 rw [hh,ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]; change U (U.symm _)= _; rw [U.apply_symm_apply]; exact (Push.side z D (L x)).unique (hp (L x))
lemma rains (u:Fish (Key F G)): ‖Bid.stretch (S:=S) F ((0:Bid.Dir G c),tint G _ u)‖ ≤ shade G*‖u‖:=by
 let v:=tint G F.Free u; let X:= Bid.stretch (S:=S) F ((0:Bid.Dir G c),v)
 apply (le_trans ?_ (tint_le u)); change ‖X‖≤ ‖v‖
 apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; obtain ⟨i,j⟩:=i; obtain ⟨j,rfl⟩:= axisEquiv.surjective j
 change ‖collect G X (i,j)‖ ≤ _
 unfold X; rw [Work.F01.collect_vertical F v (i,j)]
 split; rw [norm_zero]; exact norm_nonneg _
 exact norm_le_pi_norm v _
lemma pluto(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n:ℕ) :∃ C δ:ℝ,0<C∧0<δ∧∀ {c f:Side}(S: StepData c f)(T:Tube G S)(F:Forest S.ratio), S.patch=P → Lift.Booth K S T →∀ z, Critical F T.high T.up z → Guessed F (installed S.ratio T.R.A0) z →∀ (s:Signed) (k:S.Choices) (r:ℕ) (x:Mast G c)(v:Fish (Key F G)),
 let U:=pull s 0 ∘ UP G c f; let V:=pull s 0 ∘ VQ G c f; let F':Ark T F → Config G f:=Jazz T k s; let Z':Ark T F → Config G c:=Jade T k s; let B:=C*Real.exp (-δ*r); let y:Ark T F:=(x, fderiv ℝ (station z) 0 x); ∀ R:ℝ, Marble n T U V k r 0 R → Frank T r k F' Z' (‖x‖*B) y ∧ Duke T r k F' Z' (‖x‖*B) y ∧ Duke T r k F' Z' (‖v‖*B) (0,v):=by
 obtain ⟨X,δ,hX,hδ,hF⟩:= mousse K P p n; obtain ⟨D,hD,H⟩:=low_cost K P; let C:=shade G; have hc:0<C:=shade_pos G; have hd:0<D:=zero_lt_one.trans_le hD
 refine ⟨D*C*X,δ,by positivity,hδ,?_⟩ -- wrong order
 intro c f S T F hp h z hz hu s k r x v U V F' Z' B y R hr; let A:=X*Real.exp (-δ*r); let u:=tint G _ x
 have hh:fderiv ℝ (windowH T F) 0 y=riseP T F u:=by rw [Q_d,slew hz hu]; rfl
 obtain ⟨h1,h2⟩:=hF S T F hp h s k r u (riseP T F u) R hr
 have h3: ‖u‖*A ≤ ‖x‖*B:=by
    calc
      _ ≤ C*‖x‖*A:= mul_le_mul_of_nonneg_right (tint_le x) (by unfold A; positivity)
      _ ≤ D*(C*‖x‖)*A:=mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (by positivity) hD) (by unfold A; positivity)
      _ = _:=by unfold B A C; ring
 have h0:0 ≤ A:=mul_nonneg hX.le (Real.exp_pos _).le
 have hf(f':Config G f→ Config G c→ G.Color)(i:Ark T F)(t:ℝ)(ha:Allows n (fun i=>f' (U i) (V i)) 0 R)(hc:minor (fun i=>f' (U i) (V i)) (fderiv ℝ (windowH T F) 0 i) t):minor (fun i=> f' (F' i) (Z' i)) i t:=stamps k s f' i (ha.analytic.differentiableAt (by simp)) ((Q_d i) ▸ hc)
 have he: ‖riseP T F u‖*A ≤ ‖x‖*B:=by
    have ht' : ‖riseP T F u‖ ≤ D*(C*‖x‖):= max_le ((tint_le _).trans (le_mul_of_one_le_left (mul_nonneg hc.le (norm_nonneg _)) hD)) ((H S T hp h.1 F u).trans (mul_le_mul_of_nonneg_left (tint_le _) hd.le))
    exact (mul_le_mul_of_nonneg_right ht' h0).trans_eq (by unfold A B C; ring)
 refine ⟨⟨fun i=>hf (fun _ V=>RiftN r V T i) y (‖x‖*B) (hr.nPole i) (hh.symm ▸ minr _ _ (h1.N i) h3),fun i=>hf (fun U V=> RiftF r U V T i) y (‖x‖*B) (hr.roof i) (hh.symm ▸minr _ _ (h1.F i) h3),fun i=>hf (fun U V=> RiftI r U V T k i) y (‖x‖*B) (hr.jamb i) (hh.symm ▸ minr _ _ (h1.I i) h3)⟩,⟨fun i=> hf (fun U V=> RiftL r U V T k i) y (‖x‖*B) (hr.letup i) (hh.symm ▸ minr _ _ (h2.L i) he),fun i=> hf (fun _ V=> RiftD r V T i) y (‖x‖*B) (hr.dPole i) (hh.symm ▸ minr _ _ (h2.D i) he)⟩,?_⟩ -- may specify f'
 let Y:Ark T F:=(0,v); let Z:= fderiv ℝ (windowH T F) 0 Y
 obtain ⟨h3,h4⟩:=hF S T F hp h s k r u Z R hr
 have hY:‖Z‖*A≤ ‖v‖*B:=by
    have ht':‖Z‖ ≤ D*(C*‖v‖):=by
        apply le_trans _ (le_mul_of_one_le_left (mul_nonneg hc.le (norm_nonneg _)) hD); unfold Z Y; rw [Q_d]; dsimp only; rw [map_zero]; exact max_le (by rw [norm_zero]; positivity) (rains v)
    exact (mul_le_mul_of_nonneg_right ht' h0).trans_eq (by unfold A B C; ring)
 exact ⟨fun i=> hf (fun U V=> RiftL r U V T k i) _ _ (hr.letup i) (minr _ Z (h4.L i) hY),fun i=> hf (fun _ V=> RiftD r V T i) _ _ (hr.dPole i) (minr _ Z (h4.D i) hY)⟩
end YM.CF.Vol
