import YM.CF.Vol.Rayon
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
lemma low_smul (t:ℝ)(F:Forest S.ratio)(x:Bid.Dir G c):Lift.low T F (t•x)=t•Lift.low T F x:=by
 ext i j; change parts G 1 (Lift.low T F (t•x)) j i= t * parts G 1 (Lift.low T F x) j i
 unfold Lift.low; rw [Work.F04.parts_stretch,Work.F04.parts_stretch,show parts G 1 (t•x) j=t • parts G 1 x j from rfl,mulVec_smul]; rfl
private lemma waiting (h:0<A)(t:ℝ):∀ᶠ s:ℝ in 𝓝 0,t*|s| ≤ A:=by
 have hh:Tendsto (fun s:ℝ=> t*|s|) (𝓝 0) (𝓝 0):=by simpa only [Pi.mul_apply,abs_zero,mul_zero] using! (((continuous_const (y:=t)).mul continuous_abs).tendsto 0)
 exact hh.eventually (ge_mem_nhds h)
def minor (f:E→B)(v:E)(s:ℝ):Prop:= f 0=0∧ ‖fderiv ℝ f 0 v‖ ≤ s
lemma minr(f:E→B)(v:E)(h:minor f v s)(he:s≤ C): minor f v C := ⟨h.1,h.2.trans he⟩
structure Frank (T:Tube G S)(r:ℕ)(k:S.Choices)(U:E → Config G f)(V:E → Config G c)(s:ℝ)(v:E): Prop where
 N i: minor (fun y=>RiftN r (V y) T i) v s
 F i: minor (fun y=> RiftF r (U y) (V y) T i) v s
 I i: minor (fun y=> RiftI r (U y) (V y) T k i) v s
structure Duke (T:Tube G S)(r:ℕ)(k:S.Choices)(U:E → Config G f)(V:E → Config G c)(s:ℝ)(v:E): Prop where
 L i: minor (fun y=> RiftL r (U y) (V y) T k i) v s
 D i: minor (fun y=> RiftD r (V y) T i) v s
abbrev riseP(T:Tube G S)(F:Forest S.ratio)(x:Bid.Dir G c): LogsP G c f:=(x,Lift.low T F x)
lemma mousse(K:Teller G)(P:Patch)(p:P.Branches K.bind G)(n:ℕ) :∃ C δ:ℝ,0<C∧0<δ∧∀ {c f:Side}(S: StepData c f)(T:Tube G S)(F:Forest S.ratio), S.patch=P → Lift.Booth K S T →∀ (s:Signed) (k:S.Choices) (r:ℕ) (x: Bid.Dir G c) (z:LogsP G c f),
 let U:=pull s 0 ∘ UP G c f; let V:=pull s 0 ∘ VQ G c f; let B:=C*Real.exp (-δ*r); ∀ R:ℝ, Marble n T U V k r 0 R → Frank T r k U V (‖x‖*B) (riseP T F x)∧ Duke T r k U V (‖z‖*B) z:=by
 obtain ⟨A,σ,t,hA,hσ,ht,H⟩:= rates K P p; obtain ⟨D,hD,h⟩:= low_cost K P
 obtain ⟨Y,d,y,hY,hd,hy,hL⟩:=global_chart_cost K P p; obtain ⟨Z,v,hZ,hv,hZ'⟩:= x_chart_cost G K.below P.L.val P.L.property
 let w:=K.below.width/P.L.val; have hW:0<w:= div_pos K.below.width_pos (by positivity)
 -- D cost need ∥Xn∥≤Z h(scale) uniform `widen` product ≤2 if λ small since exp≤1 on x. β.
 let B:=A*D; have hD':0<D:=zero_lt_one.trans_le hD; have hb:0<B:=mul_pos hA hD'; let C:=max B (Y*(3*Z+1)); have hg:0<C:=hb.trans_le (le_max_left ..); let δ:=min σ d; have he:=lt_min hσ hd
 refine ⟨C,δ,hg,he,?_⟩; intro c f S T F hp hr s k r x z U V Y' R hK
 have hH :∀ᶠ u:ℝ in 𝓝 0, BillK T r k (U (u • riseP T F x)) (V (u • riseP T F x)) (A*((D*‖x‖)* |u|)* widen r ((D*‖x‖)*|u|) σ):=by
    filter_upwards [waiting ht (D*‖x‖)] with i h0
    change BillK T _ _ (pull _ _ (represent (i • Lift.low T F x))) (pull _ _ (represent (i • x))) _
    rw [← low_smul]; apply H S T hp hr F k (i • x) s r _ _ _ h0
    · apply (Lift.swapped ..).trans; rw [norm_smul, Real.norm_eq_abs]; nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (norm_nonneg x)) (abs_nonneg i)]
    apply ((Lift.swapped ..).trans (h S T hp hr.1 F _)).trans; rw [norm_smul,Real.norm_eq_abs]; exact le_of_eq (by ring)
 have he' : A*(D*‖x‖)*Real.exp (-σ*r)≤ ‖x‖*Y':= by
    rw [show A*(D*‖x‖)=‖x‖*B by unfold B; ring,mul_assoc]; refine mul_le_mul_of_nonneg_left (mul_le_mul (le_max_left ..) ?_ (Real.exp_pos _).le hg.le) (norm_nonneg _); apply Real.exp_monotone; gcongr; exact min_le_left ..
 constructor
 · exact ⟨fun i=> minr _ _ (moon hA.le (show 0 ≤ D*‖x‖ from by positivity) _ _ _ _ (hH.mono fun j h=>h.N i) ((hK.nPole i).analytic.differentiableAt (by simp))) he', fun i=> minr _ _ (moon hA.le (show 0 ≤ D*‖x‖ from by positivity) _ _ _ _ (hH.mono fun j h=>h.F i) ((hK.roof i).analytic.differentiableAt (by simp))) he',fun i=> minr _ _ (moon hA.le (show 0 ≤ D*‖x‖ from by positivity) _ _ _ _ (hH.mono fun j h=>h.I i) ((hK.jamb i).analytic.differentiableAt (by simp))) he'⟩ -- tune inference
 let N:=3*Z+1; have hN:0<N:=by unfold N; positivity
 have h t (h0: ‖z‖*|t| ≤ y)(hV:‖z‖*|t| ≤ v)(hw:(1+(r:ℝ))*(‖z‖* |t|) ≤ 1)(i:Twin c):
  let A:=‖z‖*|t|; ‖RiftL r (U (t•z)) (V (t•z)) T k i‖ ≤ Y*A*widen r A d∧ ‖RiftD r (V (t•z)) T i‖ ≤ Y*N*A*widen r A d:=by
    intro A; let x₁:= Bid.pulled (t • z.1) s; let x₂:=Bid.pulled (t • z.2) s
    rw [show V (t•z)=represent x₁ from (Lift.turned_repr ..).symm, show U (t•z)=represent x₂ from (Lift.turned_repr ..).symm]
    have hA:0≤ A:=mul_nonneg (norm_nonneg _) (abs_nonneg _)
    have h₁:‖x₁‖≤ A:= (Lift.swapped ..).trans ((show ‖t • z.1‖= ‖z.1‖*|t| by rw [norm_smul,Real.norm_eq_abs,mul_comm]).trans_le (mul_le_mul_of_nonneg_right (norm_fst_le _) (abs_nonneg _)))
    have h₂:‖x₂‖≤ A:= (Lift.swapped ..).trans ((show ‖t • z.2‖= ‖z.2‖*|t| by rw [norm_smul,Real.norm_eq_abs,mul_comm]).trans_le (mul_le_mul_of_nonneg_right (norm_snd_le _) (abs_nonneg _)))
    obtain ⟨h1,h2⟩:= hL _ _ S T hp hr.1 k r x₂ x₁ A h₂ h₁ h0 i
    refine ⟨h1,(h2 (T.Xn r (represent x₁)) (N*A) (mul_nonneg hN.le hA) ?_).trans_eq (by ring)⟩
    intro j; obtain ⟨B₁,B₂,hv,H⟩:=hr.1.feeds; let q:=K.below.clip; obtain ⟨h',h3⟩:=hZ' c T.down _ H r x₁ A h₁ hV j; unfold Tube.Xn; rw [hp,hr.1.low]
    have hv : widen r A w ≤ 2:=by have he: Real.exp (-w*(r:ℝ))≤1:= Real.exp_le_one_iff.mpr (by have hu:=Nat.cast_nonneg (α:=ℝ) r; nlinarith [mul_nonneg hW.le hu]); unfold widen; change (1+(r:ℝ))*A ≤ 1 at hw; linarith
    have h4 := h3.trans (mul_le_mul_of_nonneg_left hv (mul_nonneg hZ.le hA))
    apply (show ‖plotted _ _ _ _ _ j‖≤ ‖plotted _ _ _ _ _ j-xLin q T.down x₁ j‖+‖xLin q T.down x₁ j‖ from ?_).trans ((add_le_add h4 h').trans ?_)
    · exact norm_le_norm_sub_add ..
    unfold N; nlinarith only [hA]
 have hHC:= (waiting hy ‖z‖).and ((waiting hv ‖z‖).and (waiting zero_lt_one ((1+(r:ℝ))*‖z‖)))
 have hβ(a:ℝ)(ha:a ≤ C):a*‖z‖*Real.exp (-d*r) ≤ ‖z‖*Y':=by rw [mul_comm a,mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul ha (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right ..)) (Nat.cast_nonneg _))) (Real.exp_pos _).le hg.le) (norm_nonneg _)
 exact ⟨fun i=>minr _ _ (moon hY.le (norm_nonneg z) _ _ _ _ (hHC.mono fun j hx=> (h _ hx.1 hx.2.1 ((mul_assoc ..).symm.trans_le hx.2.2) i).1) ((hK.letup i).analytic.differentiableAt (by simp))) (hβ _ ((le_mul_of_one_le_right hY.le (show 1 ≤ N from by unfold N; nlinarith)).trans (le_max_right ..))),fun i=> minr _ _ (moon (mul_nonneg hY.le hN.le) (norm_nonneg z) _ _ _ _ (hHC.mono fun j hx=> (h _ hx.1 hx.2.1 ((mul_assoc ..).symm.trans_le hx.2.2) i).2) ((hK.dPole i).analytic.differentiableAt (by simp))) (hβ _ (le_max_right ..))⟩
end YM.CF.Vol
