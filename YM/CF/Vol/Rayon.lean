import YM.CF.Vol.Tempo
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
lemma moon (h:0≤ C)(he:0≤ A)(f:E→B)(u:E)(i:ℕ)(σ:ℝ)(hp:∀ᶠ s:ℝ in 𝓝 0, ‖f (s • u)‖≤ C*(A*|s|)*widen i (A*|s|) σ) (hh: DifferentiableAt ℝ f 0): f 0=0 ∧ ‖fderiv ℝ f 0 u‖≤ C*A*Real.exp (-σ*i):=by
 have hF:f 0=0:=by simpa using hp.self_of_nhds
 refine ⟨hF,?_⟩; have hx:= (Push.side f hh u).tendsto_slope; let F(s:ℝ):=f (s•u); let H(s:ℝ):=C*A*widen i (A*|s|) σ
 have he:Tendsto H (𝓝[≠] 0) (𝓝 (C*A*Real.exp (-σ*i))):=by have he := (show Continuous H from by unfold H widen; fun_prop).tendsto 0; simpa [H,widen] using he.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))
 apply le_of_tendsto_of_tendsto hx.norm he
 filter_upwards [hp.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin (a:=(0:ℝ)) (s:={0}ᶜ)] with s hv hs
 have h : |s| ≠0:= (abs_pos.mpr hs).ne'
 rw [slope_def_module,sub_zero, zero_smul, hF,sub_zero,norm_smul,norm_inv, Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by unfold H; field_simp)
lemma low_cost (K:Teller G)(P:Patch) :∃ D:ℝ,1 ≤ D∧∀ {c f:Side} (S:StepData c f)(T:Tube G S), S.patch=P → K.Funds S T → ∀ (F: Forest S.ratio)(v: Bid.Dir G c), ‖Lift.low T F v‖ ≤ D*‖v‖:=by
 obtain ⟨C,h,H⟩:=Lift.carry_summary G P K.bind K; refine ⟨C+1,le_add_of_nonneg_left h,fun {c f} S T p t F v=>?_⟩
 let Q:= Lift.doc T F v; let U:=Lift.blueprint S v
 rw [show Lift.low T F v= Next.SectorChange.Flat.labels Q + U from ?_]; swap
 · unfold Q Lift.doc; rw [Lift.converted,sub_add_cancel]
 have hu:‖Next.SectorChange.Flat.labels Q‖ ≤ ‖Q‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg Q)).mpr (fun i=> norm_le_pi_norm Q _)
 refine (norm_add_le ..).trans ((add_le_add (hu.trans (H S T p t.knobs t F v)) (Lift.blueprint_bill v)).trans_eq (by ring))
-- calculation along a = dA0 B, any signed. X_f, Z, N all.
structure BillK (T:Tube G S)(r:ℕ)(k:S.Choices)(U:Config G f)(V:Config G c)(s:ℝ): Prop where
 N i: ‖RiftN r V T i‖ ≤ s
 F i: ‖RiftF r U V T i‖≤ s
 I i: ‖RiftI r U V T k i‖≤ s
lemma rates (K:Teller G)(P:Patch)(p:P.Branches K.bind G) : ∃ C σ t:ℝ,0<C∧0<σ∧0<t∧ ∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch=P→Lift.Booth K S T→ ∀ (F:Forest S.ratio)(k:S.Choices)(x:Bid.Dir G c)(s:Signed)(r:ℕ)(R:ℝ), ‖Bid.pulled x s‖ ≤ R → ‖Bid.pulled (Lift.low T F x) s‖ ≤ R → R≤ t→ BillK T r k (pull s 0 (represent (Lift.low T F x))) (pull s 0 (represent x)) (C*R*widen r R σ):=by
 obtain ⟨A,r₁,hA,hr,hF⟩:= x_chart_cost G K.top 1 (by decide); obtain ⟨B,r₂,hB,hr',hC⟩:=x_chart_cost G K.below P.L.val P.L.property
 obtain ⟨D,r₃,hD,hr₃,hN⟩:= z_chart_cost P K.bind G p; obtain ⟨X,δ,Y,hX,hδ,hY,hY'⟩:=kernel_chart_cost G P.L K.η K.C K.width
 let N:=max (max A B) D; have ha : A ≤ N:= (le_max_left ..).trans (le_max_left ..); have hb:B ≤ N := (le_max_right ..).trans (le_max_left ..); have hd:D ≤ N :=le_max_right ..; have hz:0<N:=hD.trans_le hd; let u:= min K.top.width (K.below.width/P.L.val)
 have hu:=lt_min K.top.width_pos (div_pos K.below.width_pos (show 0<(P.L.val:ℝ) by positivity))
 let p':=min δ u; have ht :0<p':=lt_min hδ hu; let t:= min (min r₁ r₂) (min r₃ Y); let Z:=2*X*N; have hZT:0 ≤ Z:=by unfold Z; positivity
 refine ⟨Z+N,p',t,add_pos_of_nonneg_of_pos hZT hz,ht,lt_min (lt_min hr hr') (lt_min hr₃ hY),?_⟩
 intro c f S T H hF0 F k x s r R hx he hQ
 obtain ⟨hq,M,T',a,b,v,w,hH',hL',hUF,hy,hJ,hJ',hI,hR⟩:= hF0
 obtain ⟨C',C,hx0,hx1⟩:=hq.feeds
 let f':= Bid.pulled (Lift.low T F x) s; let y:= Bid.pulled x s
 let t:= widen r R p'; let χ:= represent f'; let φ:= represent y; let V:=T.Xn r φ; let V':= xLin T.low T.down y
 have hq':= hq.kernel; rw [← hq.knobs] at hq'; obtain ⟨he1,he2,he3⟩:= Lift.uncut s T F k hq' hI hR x hUF (hq.high.symm ▸ hx0) hH' hJ hy (hq.low.symm ▸ hx1) hL' hJ'; have h_:0≤ R:= (norm_nonneg _).trans hx; have he' := widen_nonneg r (τ:=p') h_
 have hp(j) : ‖xLin T.high T.up f' j‖ ≤ N*R ∧ ‖T.Xf r χ j-xLin T.high T.up f' j‖ ≤ N*R*t:=by
    unfold Tube.Xf; rw [hq.high]; obtain ⟨X,Y⟩:=hF _ _ _ hx0 r f' R he (hQ.trans ((min_le_left ..).trans (min_le_left ..))) j
    rw [Nat.cast_one,div_one] at Y; exact ⟨X.trans (by gcongr), Y.trans (mul_le_mul (by gcongr) (widen_anti r R ((min_le_right ..).trans (min_le_left ..))) (widen_nonneg r h_) (mul_nonneg hz.le h_))⟩
 have hv(j): ‖V' j‖ ≤ N*R ∧ ‖V j -V' j‖ ≤ N*R*t:=by
    unfold V V' Xn; rw [hq.low,H]; have hu:= hC c T.down _ hx1 r y R hx (hQ.trans ((min_le_left ..).trans (min_le_right ..))) j; exact ⟨hu.1.trans (by gcongr),hu.2.trans (mul_le_mul (by gcongr) (widen_anti r R ((min_le_right ..).trans (min_le_right ..))) (widen_nonneg r h_) (mul_nonneg hz.le h_))⟩
 let Q:= S.prediction χ k; have hh(j): ‖Tube.Z S Q φ j-zLin S f' y j‖ ≤ N*R*t:=by
    have hj:‖(f',y)‖ ≤ R:=max_le he hx
    refine ((hN c f S H hq.knobs k j (f',y)).2 (hj.trans (hQ.trans ((min_le_right ..).trans (min_le_left ..))))).trans (le_trans (b:=D*(R^2)) ?_ ?_)
    · gcongr
    rw [sq,← mul_assoc]; exact mul_le_mul (by gcongr) (le_widen _ h_) h_ (mul_nonneg hz.le h_)
 obtain ⟨hK,hS,hT⟩:=hY' S T (congr_arg _ H) ⟨_,hq.crosses⟩ r y R hx (hQ.trans ((min_le_right ..).trans (min_le_right ..)))
 have HZ {ι:Type}[Fintype ι](P P':ι→ Twin c→ Pay G)(h:NearFlat P P' X (widen r R δ))(j:ι) : ‖zip P V j-zip P' V' j‖ ≤ Z*R*t:=by
    apply (Lift.v_cost h _ _ (mul_nonneg hz.le h_) (mul_nonneg (mul_nonneg hz.le h_) he') (fun j=>(hv j).1) (fun j=>(hv j).2) _).trans
    calc
      _ ≤ X*t*(N*R)+X*(N*R*t):= by gcongr; exact widen_anti r R (min_le_left ..)
      _ = _:=by unfold Z; ring
 rw [←Lift.turned_repr,← Lift.turned_repr]; constructor
 · intro i; have hh:= HZ _ _ hT i; unfold RiftN; change zip (flatN T) V'=0 at he3; rw [he3,Pi.zero_apply,sub_zero] at hh; exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hz.le) h_) he')
 · intro i; unfold RiftF; have hy:= hp i; change xLin T.high T.up f'=zip (flatF T) V' at he1; rw [he1] at hy
   have hh:=HZ _ _ hK i; exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hy.2 ((norm_sub_rev ..).ge.trans hh)).trans_eq (by ring)) -- infer?
 intro i; unfold RiftI; have hy:= hh i; change zLin S f' y=zip (flatI T) V' at he2; rw [he2] at hy
 have hx:=HZ _ _ hS i; exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hy ((norm_sub_rev ..).ge.trans hx)).trans_eq (by ring))
end YM.CF.Vol
