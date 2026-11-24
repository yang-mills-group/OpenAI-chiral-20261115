import YM.CF.Cascade.Nylon
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
def assets (j:ℕ)(M:Male)(U:Dress n)(I:Pride n)(x:Bkg (More n)):ℂ:= ((gala M j U x:ℝ):ℂ)+pigment I x -- includes imag I
lemma Vale.plus {v g:Cloud n→ℂ}(p:Pec.Vale v)(q:Pec.Vale g):Pec.Vale (v+g):=by
 constructor
 intro k x; filter_upwards [p.life k x,q.life k x] with i h t; exact congrArg₂ (· + ·) h t
 intro x z; filter_upwards [p.pier x z,q.pier x z] with i h t; exact congrArg₂ (· + ·) h t
lemma vaseI(I:Pride n): Pec.Vale (pigment I∘ represent):=by
 constructor; intro g x; filter_upwards with i; simp_rw [Function.comp_apply,orderD,pinG]
 intro x z; filter_upwards [wraps z x] with i hi; rw [Function.comp_apply,hi]; exact pinG ..
lemma worthW (w:Stamped j L ho Y)(l:0<e)(p:1≤j)(h:P.roundZ≤ n.val)(M:Male)(U:Dress n)(I:Pride n)(k:Ample U)(Q:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More n)) 0): let g:=assets j M U I ∘ represent; Pec.Vale g ∧ ContDiffAt ℝ ω g 0:=by
 intro g; exact ⟨Vale.plus (vase h M l U k.ripe) (vaseI I), (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (gala_h h l p w _ _ k Q)).add (tuck I)⟩
lemma assets_up (M:Male)(U:Dress (CSide m B))(I:Pride (CSide m B))(s: Shape)(x: CoreX)(g:1≤j)(K:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More (CSide m B))) 0)(Q:Stamped j L ho Y)(w:P.roundZ≤(CSide m B).val)(p:Ample U)(t:WordK I)(l:0<e)(a:Cover): let L:=Complex.reCLM ∘ assets j M U I ∘ represent ∘ pour (CSide m B) x; L∘rake a =ᶠ[𝓝 0] L:=by
 intro L; let S:= CSide m B; let A:Tulip.Male:= M; let T:= ArcJ x j M U; have hp:= Grace x l g Q _ w _ p K; let B:= gala M j U; let f(i):=represent (pour S x i)
 have he(z:Air S): B (f z)= Aroma.cash (Aroma.Met T z):=by
    rw [plume]; exact (beamCash ..).symm
 filter_upwards [met_curve _ hp.curve a] with i hi
 have hv:f (rake a i)=Yg (lagX a) (f i):=core_t ..
 have hh: B (f (rake a i))=B (f i):=by rw [he,he,show Aroma.Met T (rake a i)=twist (clime _) (Aroma.Met T i) from hi]; unfold Aroma.cash; rw [twist_formula,Matrix.det_mul,Matrix.det_mul, mul_comm (clime a).val.det,mul_assoc,←Matrix.det_mul,(clime a).property.2,Matrix.det_one,mul_one] -- infer n Slot
 change ((↑(B (f (rake a i))):ℂ)+ pigment I (f (rake a i))).re=((↑(B (f i)):ℂ)+ (pigment I (f i))).re -- syntax
 rw [hh,hv,tolls t]
section
variable {E D:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup D][NormedSpace ℝ D]
lemma trim_J(f g:E→ℂ)(h:f=ᶠ[𝓝 0] g):trim t f=trim t g:=by unfold trim cake; rw [(h.iteratedFDeriv ℝ t).eq_of_nhds]
lemma trim_L(f:E→ℂ)(h: ContDiffAt ℝ (↑(2:ℕ)) f 0): trim 2 (deflate f)= trim 2 f:=by unfold trim; rw [cake_p h (by omega)]
lemma zoomPlus (x:ℂ→L[ℝ]ℂ)(f:E→ℂ)(h:ContDiffAt ℝ t f 0): trim t (x∘ f)=x ∘ trim t f:=by funext y; unfold trim cake Tensor.diagonal; rw [x.iteratedFDeriv_comp_left h le_rfl,_root_.smul_apply]; change _= x (((t.factorial:ℝ)⁻¹) • _); rw [map_smul]; rfl
lemma trim_up (x:ℝ→L[ℝ]ℂ)(f:E→ℝ)(h:ContDiffAt ℝ t f 0): trim t (x∘ f)=x ∘ trim t f:=by funext y; unfold trim cake Tensor.diagonal; rw [x.iteratedFDeriv_comp_left h le_rfl,_root_.smul_apply]; change _= x (((t.factorial:ℝ)⁻¹) • _); rw [map_smul]; rfl
lemma Trim_z(f:E→ℂ)(h:cFoot (t+1) f): trim t f=0:=by unfold trim cake Tensor.diagonal; rw [h _ (by omega),smul_zero]; rfl
lemma trim_s(f:E→ℂ)(h:ContDiffAt ℝ t f 0)(z:ℝ): trim t (z • f)=z • trim t f:=by unfold trim cake Tensor.diagonal; rw [iteratedFDeriv_const_smul_apply h,smul_comm]; rfl
lemma trim_d(f g:E→ℂ)(h:ContDiffAt ℝ t f 0)(p:ContDiffAt ℝ t g 0): trim t (f-g)= trim t f-trim t g:=by unfold trim cake Tensor.diagonal; rw [iteratedFDeriv_sub_apply h p,smul_sub]; rfl
end
lemma nais (H:Hull j L ho a b d e t m X B G T F z Y P)(M:Male)(U:Dress (CSide X B))(V:Dress (CSide m B))(I:Pride (CSide X B))(J:Pride (CSide m B))(p:Ample U)(q:Ample V)(fh: cFoot 3 (emergence L j ho G F z M U - flareP L j ho M V)) {R:RG.PathData group}{c:RG.Clip}{α η ν τ:ℝ}(ih:cFoot 3 (myth G F z c R P M U I J α))(r:R.Bounds c η ν τ)
 (s:ContDiffAt ℝ ω (spar j M ∘ represent (n:=More (CSide X B))) 0)(v:ContDiffAt ℝ ω (spar j (upMale L ho M) ∘ represent (n:=More (CSide m B))) 0)(l:ContDiffAt ℝ (↑(2:ℕ)) (deflate (lush G P M U ∘ ears F z)) 0) (x:Cloud (CSide m B)): let N:=upMale L ho M
 (trim 2 (assets j N V J∘ represent) x).re + α*(trim 2 (secondM c R) x).re= (trim 2 (assets j M U I ∘ represent) (fderiv ℝ (chartOf F z) 0 x)).re:=by
 intro N; let Y':= CSide X B; let A:=gala M j U; let B':= gala N j V
 let f:= assets j M U I ∘ represent; let F':=chartOf F z; obtain ⟨hA,hB⟩:= worthW H.stamp H.hi H.above (P.clock_fine G H.size_p) M U I p s; let h(v):=baby F z v; let g:= assets j M U I ∘ h; have hp: ContDiffAt ℝ (↑(2:ℕ)) f 0:=hB.of_le le_top; have he:g=ᶠ[𝓝 0] f∘ F':= H.native.foldM.mono fun i hi=> congrArg (assets j M U I) hi
 have hx:F' 0=0:=H.native.icicle; have hf:=def_c hp; have hm:= (bio hA).first (show deflate f 0=0 from sub_self _) (hf.of_le (by norm_num)); obtain ⟨hK,Ht⟩:= ride_eps hf F' (H.native.kala.of_le le_top) hx hm; have hQ: ContDiffAt ℝ (↑(2:ℕ)) (deflate f∘ F') 0:=(hx.symm ▸ hf).comp _ (H.native.kala.of_le le_top); have hμ: deflate (f ∘ F') = deflate f∘ F':= by funext; simp only [deflate,Function.comp_apply,hx]
 have hR:ContDiffAt ℝ ω (A ∘ h) 0:=((show ContDiffAt ℝ ω ((gala M j U)∘ represent) (F' 0) from (hx.symm ▸ gala_h (P.clock_fine G H.size_p) H.hi H.above H.stamp _ _ p s)).comp _ H.native.kala).congr_of_eventuallyEq (H.native.foldM.mono fun i hi=> congrArg (gala M j U) hi)
 let Z:=Complex.ofRealCLM; let L':=deflate (lush G P M U ∘ ears F z)
 let f0:Cloud (CSide m B)→ℂ:= pigment I ∘ baby F z; let B0:=secondM (n:=CSide m B) c R; let z0:= pigment J ∘ represent; change cFoot 3 (f0+L'-α • B0-z0) at ih
 have H' :ContDiffAt ℝ (↑(2:ℕ)) (B' ∘ represent) 0 :=(gala_h H.size_p H.hi H.above H.stamp N _ q v).of_le le_top
 have HA:ContDiffAt ℝ (↑(2:ℕ)) (A ∘ h) 0:= hR.of_le le_top; have hs:ContDiffAt ℝ (↑(2:ℕ)) z0 0:=(tuck J).of_le le_top; have hw:ContDiffAt ℝ (↑(2:ℕ)) f0 0:=(pane H.native I).of_le le_top; have ht: ContDiffAt ℝ (↑(2:ℕ)) B0 0 := (sane r).of_le le_top
 have hT:=Trim_z _ ih; rw [trim_d (f0+L'-α • B0) z0 ((hw.add l).sub (ht.const_smul α)) hs, trim_d (f0+L') (α • B0) (hw.add l) (ht.const_smul α),trim_s B0 ht, trim_addI (g:=L') hw l] at hT; have hh:= congrArg Complex.re (congrFun hT x); simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Complex.sub_re, Complex.add_re, Complex.smul_re,smul_eq_mul,Pi.zero_apply,Complex.zero_re] at hh
 have hp': trim 2 f (fderiv ℝ F' 0 x)=trim 2 g x:=by rw [←trim_L f hp, trim_J g _ he,←trim_L (f∘ F') ((hx.symm ▸ hp).comp (g:=f) _ (H.native.kala.of_le le_top)),hμ]; exact tendsto_nhds_unique (Ht x) ((argent hQ).mp hK x)
 let Fh:=Z ∘ (B' ∘ represent); let Lh:= Z ∘ (A ∘ h)
 change (trim 2 (Fh+z0) x).re + α*(trim 2 B0 x).re=(trim 2 f (fderiv ℝ F' 0 x)).re; rw [hp',show g= Lh+f0 from rfl, trim_addI (show ContDiffAt _ _ Lh _ from Z.contDiff.contDiffAt.comp _ HA) hw, trim_addI (show ContDiffAt _ _ Fh _ from Z.contDiff.contDiffAt.comp _ H') hs]; unfold Lh Fh; rw [trim_up Z _ HA,trim_up Z _ H']; change (↑(trim 2 (B' ∘ represent) x)+(trim 2 z0 x) :ℂ).re + _= (↑(trim 2 (A ∘ h) x)+ _ :ℂ).re; have hy:= congrFun (taxMove H M U V s p v q fh l) x; rw [show trim 2 (A ∘ h) x=(trim 2 L' x).re+trim 2 (B' ∘ represent) x from hy]; rw [Complex.add_re, Complex.ofReal_re,Complex.add_re, Complex.ofReal_re]; linarith only [hh]
end YM.CF.Cascade
