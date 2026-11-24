import YM.CF.Vol.Trip
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
-- section compar norms
lemma drops2 {E F : Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{g:E→F}{x:E}(p:Jet.Allows n g x C)(h:1 ≤ n): ‖fderiv ℝ g x‖ ≤ C:= by rw [←norm_iteratedFDeriv_one]; exact p.norm_le 1 h
structure stance(f:E→ B)(t:ℝ) :Prop where
 origin:f 0=0
 rud:‖fderiv ℝ f 0‖≤ t
lemma stance.mono {f:E→B}(h:stance f t)(he:t≤ D):stance f D:=⟨h.origin,h.rud.trans he⟩
-- compass via tangent of z. s. minor v total variation. stencil E subtract δ. Eps dims.
def pulse {α β:Type} [Add β] (z:α→β) (x:α×β):α×β:=(x.1,x.2+z x.1)
lemma ring_pair {F:E→B}(h:DifferentiableAt ℝ F 0)(x:E×B): fderiv ℝ (pulse F) 0 x = (x.1,x.2+fderiv ℝ F 0 x.1):=by
 have he:=((ContinuousLinearMap.fst ℝ E B).hasFDerivAt (x:=0)).prodMk (((ContinuousLinearMap.snd ℝ E B).hasFDerivAt (x:=0)).add (h.hasFDerivAt.comp (f:=ContinuousLinearMap.fst ℝ E B) 0 (ContinuousLinearMap.fst ℝ E B).hasFDerivAt)); unfold pulse; erw [he.fderiv]; rfl
lemma stance_p{α β γ:Type}[NormedAddCommGroup α][NormedSpace ℝ α][NormedAddCommGroup β][NormedSpace ℝ β][NormedAddCommGroup γ][NormedSpace ℝ γ]{m:α→β}{f g:α×β→ γ}{z:α→L[ℝ] β}
 (hx:0≤ t)(hm:m 0=0)(hp:DifferentiableAt ℝ m 0)(hs:‖fderiv ℝ m 0 - z‖ ≤ C)(ht:DifferentiableAt ℝ f 0)(he:‖fderiv ℝ f 0‖≤ D)(hh:∀ x, minor f (x,z x) (‖x‖*t))(hZ:g 0=0)(hr:DifferentiableAt ℝ g 0)(h:∀ x, ‖fderiv ℝ f 0 (0,x.2)-fderiv ℝ g 0 x‖ ≤ ‖x‖*t): stance (f ∘ pulse m -g) (t+t+D*C):=by
 have hu:pulse m 0=0:= Prod.ext rfl (show (0:β)+m 0=0 from by rw [hm,add_zero])
 let U:=pulse m
 have hb:DifferentiableAt ℝ U 0 := (ContinuousLinearMap.fst ℝ α β).differentiableAt.prodMk ((ContinuousLinearMap.snd ℝ α β).differentiableAt.add (hp.comp (f:= Prod.fst) (0:α×β) differentiableAt_fst))
 have hC:0≤ C:=(norm_nonneg _).trans hs; have hD:0≤ D:=(norm_nonneg _).trans he
 refine ⟨by rw [Pi.sub_apply,hZ,Function.comp_apply,hu,(hh 0).1,sub_zero],?_⟩
 let F:=fderiv ℝ f 0; let G:= fderiv ℝ g 0
 rw [fderiv_sub ((show DifferentiableAt ℝ f (U 0) by rw [show U 0=0 from hu]; exact ht).comp _ hb) hr,fderiv_comp _ (by rw [show U 0=0 from hu]; exact ht) hb,show U 0=0 from hu]; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x
 erw [_root_.sub_apply, ContinuousLinearMap.comp_apply,ring_pair hp]
 let t':= fderiv ℝ m 0-z
 rw [show (x.1,x.2+fderiv ℝ m 0 x.1)=(x.1,z x.1) + (0,t' x.1) + (0,x.2) from by unfold t'; simp; abel]
 rw [map_add,map_add,add_sub_assoc]; apply (norm_add_le ..).trans
 have ht: ‖F (0,t' x.1)‖ ≤ D*(C*‖x‖):= (F.le_opNorm _).trans (mul_le_mul he (show max _ _ ≤ _ from max_le (by rw [norm_zero]; positivity) ((t'.le_opNorm x.1).trans (mul_le_mul hs (norm_fst_le x) (norm_nonneg _) hC))) (norm_nonneg _) hD)
 exact (add_le_add ((norm_add_le ..).trans (add_le_add ((hh _).2.trans (mul_le_mul_of_nonneg_right (norm_fst_le x) hx)) ht)) (h x)).trans_eq (by ring)
abbrev circle (T:Tube G S)(x:ℝ)(F:Forest S.ratio)(a: Ark T F): Pot S G:= (a.1,meal F x a.2)
def pill(T:Tube G S)(x:ℝ)(F: Forest S.ratio): Ark T F→L[ℝ] Pot S G:=ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ _) (meal F x)
lemma pill_le : ‖pill T x F‖≤ shade G:=by
 apply ContinuousLinearMap.opNorm_le_bound _ (shade_pos _).le; intro t
 exact max_le ((norm_fst_le t).trans (le_mul_of_one_le_left (norm_nonneg t) (shade_one G))) ((meal_n F x t.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le _) (shade_pos _).le))
lemma van_g (h:K.Funds S T)(V:Config G c)(k:S.Choices): Rows.bump T x V k 0=0:=by
 obtain ⟨a,b,hx,h⟩:= h.feeds; have he:= bump_smul T x V k hx (0:Directions G f) 0; rwa [zero_smul,zero_smul] at he
def gloss(T:Tube G S)(x:ℝ)(F: Forest S.ratio)(k:S.Choices)(i:Slots S): Ark T F→ G.Color:=fun y=>dragB T x k (pill T x F y) i
lemma down_D(T:Tube G S)(x:ℝ)(F:Forest S.ratio)(k:S.Choices)(p:Slots S)(h:K.Funds S T)(ha:DifferentiableAt ℝ (gloss T x F k p) 0)(a:Ark T F):
 gloss T x F k p 0=0 ∧ fderiv ℝ (gloss T x F k p) 0 a= Rows.bump T x 1 k (meal F x a.2) p:=by
 obtain ⟨A,B,H,H'⟩:=h.feeds; let L:=meal F x (G:=G); let g:=gloss T x F k p; let y:=Rows.bump T x (1:Config G c) k (L a.2) p
 have hV(v:Mast G c): g (v,0) =0:=by unfold g gloss dragB; change bump T x _ k (L (0)) p=_; rw [map_zero,van_g h]; rfl
 have he(g:Ark T F→G.Color)(hf:DifferentiableAt ℝ g 0)(hV:∀ v,g (v,0)=0): fderiv ℝ g 0 a=fderiv ℝ g 0 (0,a.2):=by
    have hh:= Push.side g hf (a.1,0); have hL(x:ℝ):g (x • (a.1,0))=0:=by change g (x • a.1,x • 0)=0; rw [smul_zero]; exact hV _ -- tune
    simp_rw [hL] at hh; nth_rw 1 [show a=(a.1,0)+(0,a.2) from by simp]; rw [map_add, hh.unique (hasDerivAt_const ..),zero_add]
 refine ⟨hV _,?_⟩
 rw [he _ ha hV]; apply (Push.side _ ha _).unique; let F(t:ℝ):=g (t • ((0:Mast G c),a.2)); have hF(t:ℝ): F t=t • y:=by
    unfold F g gloss dragB; change bump T x (facadeX G ((t:ℝ) • (0:Mast G c))) k (L (t•a.2)) p= _; rw [smul_zero,show facadeX G (0:Mast G c)=1 from by simp [facadeX], show L _=t • L a.2 from map_smul L t a.2,bump_smul T x 1 k H]; rfl
 change HasDerivAt F y 0; rw [funext hF]; simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const y)
end YM.CF.Vol
