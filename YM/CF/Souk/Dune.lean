import YM.CF.Souk.Bravo
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
open Planned.JetPort
open Next.SectorChange PatchReads Next.SectorChange.Wisps PhysicalNext.JointLoad
variable {k: S.Choices}{q:Chi}{a:ℝ}
lemma fruit_r {z}(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(hK:1 ≤ n)
 (hr:Ready T x)(hs:0 ≤ s)(ht:s ≤ 1)(hx:1000 ≤radiusB x)(hQ: Cert P K S T x)(hv:W.Service F T.high T.up z)
 (h: Protected 2 (ξ T F k s z-ζ₁ T F x k q D s l) 0 C)(hh: ∀ y:Mast G c, ‖y‖<1→ ((ξ T F k s z - ζ₁ T F x k q D s l) y).IsSymm):
 let H:=ξ T F k s z-ζ₁ T F x k q D s l; let X:= (l+52)*radiusB x; let R:=W.tables K.top.clip P
 let t:=transit R n; let e:ℝ:= Real.exp (-(t/2)*radiusB x); let M:ℝ:=Uniform.townCost G
 Jewel H 0 C (raised G S.patch.L X*C + e*chargeBill R n*(M*countCost (t/2))*(M*countCost t)):=by
 intro H L R t e M; let f:= address F G ∘ Sum.inr; let g:=address F G ∘ Sum.inl
 let A:= ξ T F k s z; let V:= majorX T x (bareStores S) F k q D 1 l; let X:= lathe x s F V
 refine ⟨h,h.germ ?_,?_⟩
 · filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_self (x:=(0:Mast G c)) zero_lt_one)] with y (hy:y∈ball _ _); change paintO (H y)=paintO (H y).transpose; rw [show (H y).transpose=H y from hh y (mem_ball_zero_iff.mp hy)]
 obtain ⟨⟨ht',h₁⟩,hp,hq⟩:=far_H W hQ hv k s hs ht; intro i hi j
 let u:=g (j (Fin.last i)); let B:=Finset.univ.filter fun v=> separation u (f v) ≤ touchH L S.patch.L; let P(v):= ∑ k,|pS (i+1) H j 0 v k|; let U(v):=∑ k,|pS (i+1) A j 0 v k|
 have hT':Protected (i+1) H 0 C:= h.order (by omega); have he:=steep hT'; have hA:ContDiffAt ℝ (i+1:ℕ) A 0:=hp.of_le (by norm_cast; omega); have hX:ContDiffAt ℝ (i+1:ℕ) X 0:= by
    rw [show X=A-H from (sub_sub_cancel A X).symm]; exact hA.sub he
 have hh':∀ y:Mast G c,∀ w:Mast G c, Sample k (facadeX G (s•y)) 1 L (V (facadeX G (s•y))) k (facadeX G (s • w)) 1 (V (facadeX G (s • w))):=fun y w i i' j j' h hi hj=> Char.hessN_read hr (h.lower (show (l+42)*radiusB x ≤ L from Nat.mul_le_mul_right _ (by omega))) hi hj hx -- tune
 have he v(hv:v∈ Bᶜ):P v= U v:=by
    refine Finset.sum_congr rfl fun w _=>?_ ; have ht: pS (i+1) X j 0 v w=0:= receipt hr hh' hX _ _ _ (by
       have hx:touchH L S.patch.L < separation u (f v):=by simpa [B] using hv
       exact hx)
    rw [show pS (i+1) H j 0=pS (i+1) A j 0-pS (i+1) X j 0 from ?_,Matrix.sub_apply,ht,sub_zero]; unfold pS Uniform.entry; erw [show H=A-X from rfl,iteratedFDeriv_sub_apply hA hX]; rfl
 have hy(t): P t ≤ C:= (row_S _ t).trans (scaleS hT' le_rfl _)
 change ∑ i,P i ≤ _; rw [←Finset.sum_add_sum_compl B, Finset.sum_congr (s₁:= Bᶜ) rfl he]; apply add_le_add
 · exact (Finset.sum_le_sum (fun i _=> hy i)).trans (by rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (lit F _ _) h.nonneg)
 refine farX hq ht' h₁.le (by omega) _ (by apply Multiplicity.comp (Uniform.town F) Sum.inr_injective) _ ?_ hA
 intro a ha; have hw:touchH L S.patch.L < separation u (f a):=by simpa [B] using ha
 have hz : radiusB x ≤ L:= le_mul_of_one_le_left (by omega) (by omega); change _ ≤ separation u (f a); apply le_trans hz; refine le_trans (b:=touchH L S.patch.L) ?_ hw.le; unfold touchH; apply le_trans (le_mul_of_one_le_left (by omega) (show 1≤ S.patch.L.val from S.patch.L.property)); omega
lemma carving {X H W: Fish ι→ Neige.Shelf τ}{L S D Q:ℝ}(u:Fish ι)(ht:Jewel X u L V)(hp:Jewel (fun i=> (X i).transpose * W i * X i-1) u S Q)(hx:Jewel (H-W) u D C):
 let E(y):= (X y).transpose *H y*X y-1
 Jewel E u (S+4*(4*L*D)* L) (Q+ (4*L*D*V+3*(L*C+3*V*D)*L)):=by
 intro E; exact gold_B (hf:=hp.merge ((ht.rotate.trade hx).trade ht)) le_rfl le_rfl (Eventually.of_forall fun i=>by unfold E; dsimp only; rw [Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul]; abel)
open Teller
lemma sieve (K:Teller G)(P:Patch)(p:P.Branches K.bind G)(l:ℕ)(hn:1≤l)(hl:l ≤ 18)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind 5): ∃ D C:ℝ,0<D∧0<C∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F → ∃ z,W.Service F T.high T.up z ∧∀ (k:S.Choices)(q:Chi)(a:ℝ),
 let w:=temp x; let H:=μ₁ T F x k q a w l; let X:=ξ T F k w z
 Jewel (fun y=> perturb (H y) (X y)) 0 (D*lamp x^3) (C*(raised G P.L ((l+52)*radiusB x)+1)*lamp x^3) ∧ Protected 2 H 0 C:=by
 obtain ⟨D,r,hD,hr,H⟩:=base_high K P p 2 l (by omega) W
 obtain ⟨m,v,C,U,hm,hv,hC,H'⟩:= metricsU K P 3 l (by omega) hl p W
 let L₀:= composeCost 2 U (Uniform.shade G); let L:=max 1 L₀
 let M:= L +4*(4*L*D)* L; let V₀:=L+(4*L*D*L+3*(L*(D+1)+3*L*D)*L); let V:=max V₀ L
 have hL:0<L:=zero_lt_one.trans_le (le_max_left ..); have hM:0<M:=by unfold M; positivity; -- ok
 let T:=transit (W.tables K.top.clip P) 2; let t:=if 0<T then T/2 else 1; have ht :0<t:=by unfold t; split; positivity; positivity
 let E:=chargeBill (W.tables K.top.clip P) 2; let g:=Uniform.townCost G; let b:=E*(g*countCost t)*(g*countCost T)
 have h : Tendsto temp atTop (𝓝 0):= by simpa using Work.E09.radiusB_temp 0
 refine ⟨M,V,hM,lt_of_lt_of_le hL (le_max_right ..),?_⟩
 filter_upwards [H,H',PatchReads.reserve K P, Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,h.eventually (ge_mem_nhds (lt_min hr zero_lt_one)), eventually_gt_atTop (0:ℝ), Newt.smallF (n:=3) ht b] with x HH HX Hu Hp Hr Hq HQ
 intro c f S U' F Kk Kv; have hi:= Hu S U' Kk.got Kk.size Kk.funds.1; obtain ⟨z,hz,hv'⟩:=HH S U' F Kk Kv; refine ⟨z,hz,?_⟩; intro k q a w Z X
 have hw:0<w:=Work.E09.temp_pos Hq; let A:=bareStores S; have hA:= (HX S U' Kk A F (1:Config G c) (Heir.noFlags ..).symm Kv k).2 q a 1
 have hA': Loom 2 x U (1:Config G c) U' F A 1 k q a l:= ⟨hA.major.order (by decide),hA.payX.order (by decide),hA.lump.order (by decide),hA.link.order (by decide),hA.back.order (by decide),hA.errorX.order (by decide),hA.errorH.order (by decide)⟩
 have h:=hv' k q a w hw le_rfl (Hr.trans (min_le_left ..)) 0 (by simp)
 let W₀:= ζ₁ U' F x k q a w l
 obtain ⟨hp',hY⟩:= reel_B hi Hp hA'; have hp:= fruit_r W (n:=2) (by decide) hi hw.le (Hr.trans (min_le_right ..)) Hp Kk hz h.1 (fun y hy=>(hv' k q a w hw le_rfl (Hr.trans (min_le_left ..)) y hy).2)
 let R:=raised G P.L ((l+52)*radiusB x); have ht':0<T:=(far_H W Kk hz k w hw.le (Hr.trans (min_le_right ..))).1.1
 have hB:w ≤ lamp x:=le_mul_of_one_le_left hw.le (one_le_pow₀ (show 1 ≤ (radiusB x:ℝ) by exact_mod_cast (show 1 ≤ radiusB x by omega)))
 let X₀:=lamp x^3; have hp₀:w^3 ≤ X₀:=pow_le_pow_left₀ hw.le hB 3; have hi':w^(l+2) ≤ X₀:= (pow_le_pow_of_le_one hw.le (Hr.trans (min_le_right ..)) (by omega)).trans hp₀
 have hR:0 ≤ R:=by unfold R raised; positivity
 have he: Jewel Z 0 L ((R+1)*L):=gold_B hp' (le_max_right ..) (by rw [Kk.got]; apply mul_le_mul _ (le_max_right ..) hp'.upper.nonneg (by linarith only [hR]); linarith only) (Eventually.of_forall fun y=>rfl)
 have hY': Jewel (fun y=>perturb (Z y) (W₀ y)) 0 (L*X₀) ((R+1)*(L*X₀)):=by
    apply gold_B hY (mul_le_mul_of_nonneg_right (show L₀ ≤ L from le_max_right ..) (pow_nonneg (hw.le.trans hB) 3)) ?_ (Eventually.of_forall fun y=>rfl); rw [Kk.got]; exact mul_le_mul (show R ≤ R+1 by linarith only) (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (hw.le.trans hB) _)) hY.upper.nonneg (show 0≤ R+1 by linarith)
 have hx:Jewel (X-W₀) 0 (D*X₀) ((D+1)*(R+1)*X₀):=by
    dsimp only at hp; apply gold_B hp (mul_le_mul_of_nonneg_left hi' hD.le) ?_ (Eventually.of_forall fun y=>rfl); rw [Kk.got]
    have hP:b=E*(g*countCost (T/2))*(g*countCost T):=by unfold b t; rw [if_pos ht']
    have hb:0 ≤ b:=by rw [hP]; have hT: 0<E:=(far_H W Kk hz k w hw.le (Hr.trans (min_le_right ..))).1.2; have hR:=Uniform.count_pos ht'; have hm:= Uniform.count_pos (half_pos ht'); positivity
    have hE: Real.exp (-(T/2)*radiusB x)*b ≤ X₀ :=by
       unfold t at HQ; rw [if_pos ht'] at HQ; refine (mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) hb).trans (HQ.trans hp₀)
       apply mul_le_mul_of_nonpos_left ?_ (by linarith); exact_mod_cast (show Stores.till x ≤ radiusB x by unfold Stores.till; omega)
    apply (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi' hD.le) hR) (le_trans ?_ hE)).trans
    · have h:0 ≤ X₀:=(pow_nonneg hw.le _).trans hp₀; have hh:0≤ R+D:=by positivity
      nlinarith only [mul_nonneg hh h,mul_nonneg (add_nonneg hR hD.le) h]
    exact le_of_eq (by rw [hP]; unfold T E g; ring)
 have hQ := carving (X:=Z) (W:=W₀) 0 he hY' hx; refine ⟨gold_B hQ (le_of_eq (by unfold M X₀; ring)) ?_ (Eventually.of_forall fun i=>rfl), he.upper.mono (le_max_right ..)⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left V₀ L) (by linarith only [hR])) (pow_nonneg (hw.le.trans hB) _)); exact le_of_eq (by unfold V₀ R X₀; ring)
end YM.CF.Souk
