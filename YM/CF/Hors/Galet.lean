import YM.CF.Hors.Toit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Push.Uniform (address Primary tint)
open Next.SectorChange Next.SectorChange.Wisps PatchReads
open Push.Uniform (weaker signedFine entryWidth Beacon)
def avail(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(l:ℕ)(y:Mast G c):= firmX (clipped T x F k) (sol S T k x F l) 1 y
abbrev cart(x:ℝ)(L:Side):= Stores.till x/L.val
def hut(T:Tube G S)(x:ℝ)(F: Forest S.ratio)(k:S.Choices)(l:ℕ)(y:Mast G c):= avail T x F k l y-mainTerm T.low (grainA T.down (cart x S.patch.L)) (facadeX G y)
lemma evalX(x y:ℝ)(k:S.Choices)(l:ℕ)(F:Forest S.ratio): (fun v:Mast G c=>avail T x F k l (y•v))=firmX (clipped T x F k) (fun v=> sol S T k x F l (y•v)) y:=by funext j; simp [avail,firmX]
lemma keyX (g: fieldDir G c 1→ AxisChart G F)(y:Mast G c)(H:ClassicalMatch F T.high T.low T.up T.down g)(i:Fin n→Primary c G)(hp:n ≤ 4)(k: S.Choices)(s:ℝ):
 let f(y:Mast G c):=firmX (costP F k T.high T.up) (fun v=>Uniform.station g (s•v)) s y-mainTerm T.low T.down (facadeX G (s•y))
 ContDiffAt ℝ ω f 0 ∧ Uniform.entry f 0 i=0:=by
 intro f; let B(x:fieldDir G c 1):= tested F k T.high T.up x (g x); let P(x:fieldDir G c 1):= mainTerm T.low T.down (represent x)
 let L:Mast G c →L[ℝ] fieldDir G c 1:= (tint G _).toContinuousLinearMap.comp (s • ContinuousLinearMap.id ℝ (Mast G c)); have hv:f=(B-P) ∘ L:=by
    funext y; unfold f firmX; rw [show costP F _ _ _ (meetVar _ _)= _ from Uniform.written F k _ _ _ _]; change _=B (L y) - P (L y); unfold B; simp only [Uniform.station, (tint G _).apply_symm_apply]; rfl -- tune
 obtain ⟨hh,hx,hQ⟩:= H n hp k
 rw [hv]; have he: ContDiffAt ℝ ω (B-P) (L 0):=by rw [map_zero]; exact hh.sub hx
 refine ⟨he.comp _ L.contDiff.contDiffAt,?_⟩; unfold Uniform.entry; rw [Uniform.iter_lin_at (he.of_le le_top),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_sub_apply (hh.of_le le_top) (hx.of_le le_top), hQ,sub_self]; rfl
lemma raises(G:Gauge)(L:Side)(l n:ℕ)(A:ℝ)(ha:0≤ A):∀ᶠ x in atTop,A*temp x*(raised G L ((l+1)*radiusB x)+1) ≤ 1:=by
 let D:ℝ:=L.val; let u:ℝ:=D*(l+1)+D; let g:= Uniform.townCost G; let M :ℝ:=g*(2*u+1)^4+1
 have hp:1 ≤ (L.val:ℝ):= Nat.one_le_cast.mpr L.property; have h:0 ≤ u:=by unfold u D; positivity
 have hh:= (Work.E09.radiusB_temp 4).const_mul (A*M); rw [mul_zero] at hh
 filter_upwards [hh.eventually (ge_mem_nhds zero_lt_one), Work.E01.radiusB_tendsto.eventually_ge_atTop 1] with x hx hv
 let B:ℝ:= radiusB x; let V:=raised G L ((l+1)*radiusB x)
 have hB:1 ≤ B:=Nat.one_le_cast.mpr hv
 have he:(touchH ((l+1)*radiusB x) L:ℝ) ≤ u*B:= by
    unfold touchH; push_cast; unfold u B D; have h : (L.val:ℝ) ≤ D*B:= le_mul_of_one_le_right (Nat.cast_nonneg _) hB; linarith
 have hz:V+1 ≤ M*B^4:=by
    unfold V raised; dsimp only; refine le_trans (b:=g*((2*u+1)*B)^4 + B^4) ?_ (le_of_eq (by unfold g M; ring))
    apply add_le_add _ (one_le_pow₀ hB); unfold g; gcongr; linarith
 have hq:= Work.E04.temp_nonneg x
 exact (mul_le_mul_of_nonneg_left hz (mul_nonneg ha hq)).trans (Eq.trans_le (show A*temp x*(M*B^4)=A*M*(B^4*temp x) by ring) hx)
set_option maxHeartbeats 650000 in
lemma pearlier (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(l n:ℕ)(hl:1≤l)(hs:n+1≤l+1)(hn:n+1 ≤4) (W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+4)):
 ∀ᶠ x in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x →sizedP G P K S T F → (∀ z,Critical F T.high T.up z→ClassicalMatch F T.high T.low T.up T.down z) → ∀ (k:S.Choices)(v:Fin (n+1)→Primary c G), ContDiffAt ℝ (n+1:ℕ) (hut T x F k l) 0 ∧ |Uniform.entry (hut T x F k l) 0 v| ≤ 2* temp x^(l+2-(n+1)):=by
 obtain ⟨A,D,ha,hd,H⟩:=push_paid K P p (n+1) l (by omega) W; obtain ⟨U,hU⟩:= Uniform.paint_supply G (n+1)
 let C:=K.below.paths; let s:=K.below.width; let B:= Stationary.gramCost G C*stip G n 2 U s+ C*stip G n 3 U s+ C*stip G n 4 U s; have hS:0<s:=K.below.width_pos
 let h':ℝ:= s/(4*P.L.val); have h0:0<h':= div_pos hS (by positivity)
 filter_upwards [H, ((show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0)).eventually (ge_mem_nhds hd), ((show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0)).eventually (ge_mem_nhds zero_lt_one), eventually_gt_atTop (0:ℝ), raises G P.L l 0 A ha.le, Newt.smallF (n:=l+2-(n+1)) h0 |B|, Work.E01.radiusB_tendsto.eventually_ge_atTop (100000*P.L.val)] with x hx hp hu he hM hg hL -- tune
 intro c f S T F hr hv hV k v; obtain ⟨z,hz,hQ⟩:=hx S T F hr hv; let t:=temp x; let L:= cart x P.L; have ha:0<t:=Work.E09.temp_pos he; let U(y:Mast G c):= mainTerm T.low T.down (facadeX G y)-mainTerm T.low (grainA T.down L) (facadeX G y)
 obtain ⟨m,H',he',hr'⟩:=hr.funds.1.feeds; rw [←hr.funds.1.low] at hr'
 obtain ⟨hd,hE⟩:= cany hU hr' v (by have hh:=hr.size; omega) L
 let M:ℕ:=l+2-(n+1); have hB:tollE s L * B ≤ t^M:=by
    apply le_trans ?_ hg; have h:P.L.val ≤ Stores.till x:=by unfold Stores.till; omega
    have ht' : Stores.till x ≤ 2*P.L.val* L:=by
       have hp:P.L.val ≤ P.L.val * L:= le_mul_of_one_le_right (by positivity) (Nat.div_pos h P.L.property); rw [mul_assoc]; have hx:Stores.till x % P.L.val + P.L.val* L= Stores.till x:=Nat.mod_add_div ..; have hy : Stores.till x % P.L.val < P.L.val:= Nat.mod_lt (Stores.till x) P.L.property; omega
    apply le_trans (mul_le_mul_of_nonneg_left (le_abs_self _) (show 0 ≤ tollE s L from (Real.exp_pos _).le)); unfold tollE; apply mul_le_mul_of_nonneg_right _ (abs_nonneg B); apply Real.exp_monotone
    unfold h'; have he:(Stores.till x:ℝ) ≤2*(P.L.val:ℝ)*(L:ℝ):=by exact_mod_cast ht'
    field_simp; linarith
 let K'(y):=firmX (costP F k T.high T.up) (fun y=>Uniform.station z (t•y)) t y
 let Ξ:=firmX (clipped T x F k) (fun y=>sol S T k x F l (t • y)) t-K'
 let Φ(y:Mast G c):= mainTerm T.low T.down (facadeX G (t•y)); let V:= hut T x F k l; obtain ⟨h₁,h₂⟩:= keyX z 0 (hV z hz.critical) v hn k t -- 0 vector
 obtain ⟨hA,hP⟩:=hQ k 0 t ha le_rfl hp (by simp)
 let R:Mast G c→L[ℝ] Mast G c:= t • ContinuousLinearMap.id ℝ _; have hR:U ∘ R=fun y=> U (t• y):=rfl
 have hf: (fun y=>V (t•y))=Ξ+ (K'-Φ)+ U ∘ R:=by -- parse
    funext y; rw [Pi.add_apply, Pi.add_apply, Pi.sub_apply]; unfold Ξ Φ U V Function.comp; rw [hut]; change _= (_- K' y)+_+_ -- tune
    rw [hr.got]; unfold L; rw [←evalX]; dsimp only; rw [show R y=t • y from rfl]; abel
 have hb: ContDiffAt ℝ (n+1:ℕ) Ξ 0:= hA.of_le (by norm_cast; omega)
 have hs :ContDiffAt ℝ (n+1:ℕ) (K'-Φ) 0:=h₁.of_le le_top
 have hc: ContDiffAt ℝ (n+1:ℕ) U (R 0):=by rw [map_zero]; exact hd.of_le le_top
 have hh':ContDiffAt ℝ (n+1:ℕ) (fun y=>V (t•y)) 0:=hf.symm ▸ ((hb.add hs).add (hc.comp 0 R.contDiff.contDiffAt))
 have hV':ContDiffAt ℝ (n+1:ℕ) V (t • 0):=by
    rw [smul_zero]; let f(y:Mast G c):= t⁻¹ • y; have ht:f 0=0:=smul_zero _; have he : V= (fun y=> V (t•y)) ∘ f:=funext fun y=>(congr_arg V (smul_inv_smul₀ ha.ne' y)).symm
    apply ContDiffAt.congr_of_eventuallyEq ((ht.symm ▸ hh':ContDiffAt ℝ (n+1:ℕ) (fun y=> V (t•y)) (f 0)).comp (f:=f) 0 (contDiffAt_id.const_smul _)); exact Eventually.of_forall (congr_fun he)
 refine ⟨by rwa [smul_zero] at hV',?_⟩
 have hD': |Uniform.entry (fun y=>V (t•y)) 0 v| ≤ t^(n+1)*(2*t^M):=by
    have hL: |Uniform.entry Ξ 0 v| ≤ t^(l+2):=by
        rw [bolt_entry hb]; apply le_trans ((Uniform.entry_bound _).trans ((hP (v (Fin.last n))).norm_le n (by omega))) ?_
        apply le_trans (Eq.le (show _=t^(l+2)*(A*t*(raised G P.L ((l+1)*radiusB x)+1)) from by ring)); exact mul_le_of_le_one_right (pow_nonneg ha.le _) hM
    rw [hf,show Uniform.entry (Ξ + (K' - Φ) + U ∘ R) 0 v=Uniform.entry Ξ 0 v + Uniform.entry (K'-Φ) 0 v+Uniform.entry (U∘ R) 0 v from ?_,show Uniform.entry (K'-Φ) 0 v=0 from h₂,add_zero,hR, entry_scale U t v 0 hc, smul_zero, smul_eq_mul]
    · apply (abs_add_le ..).trans; rw [abs_mul,abs_of_nonneg (pow_nonneg ha.le _)] -- T
      refine (add_le_add hL (mul_le_mul_of_nonneg_left (hE.trans hB) (pow_nonneg ha.le _))).trans (le_of_eq ?_)
      rw [show l+2=n+1+M by omega, pow_add]; ring
    unfold Uniform.entry; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ (n+1:ℕ) (Ξ+(K'-Φ)) 0 from hb.add hs) (hc.comp _ R.contDiff.contDiffAt),iteratedFDeriv_add_apply hb hs]; rfl
 rw [entry_scale V t v 0 hV', smul_zero, smul_eq_mul,abs_mul, abs_of_pos (pow_pos ha _)] at hD'; exact le_of_mul_le_mul_left hD' (pow_pos ha _)
end YM.CF.Hors
