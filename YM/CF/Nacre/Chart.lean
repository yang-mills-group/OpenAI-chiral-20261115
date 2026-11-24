import YM.CF.Nacre.Bliss
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch NormedSpace Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {E F G:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
variable {m:ℕ}{f:E→F}
def cake(k:ℕ)(X:E→F):= ((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k X 0
def trim(k:ℕ)(X:E→F):E→F:=fun p=>Tensor.diagonal (cake k X) p
-- includes smooth finite order only
def cFoot(k:ℕ)(f:E→F):Prop:=∀ i:ℕ,i<k→ iteratedFDeriv ℝ i f 0=0
def crystal(k:ℕ)(f X:E→F):Prop:= ∀ x,Tendsto (fun t:ℝ=> (t^k)⁻¹ • f (t • x)) (𝓝[≠] 0) (𝓝 (X x))
private lemma farm {f:ℝ→ℝ}(h:ContDiffAt ℝ (m:ℕ) f 0)(he:∀ j:ℕ,j<m→ iteratedDeriv j f 0=0): Tendsto (fun t:ℝ=> f t/t^m) (𝓝[≠] 0) (𝓝 ((m.factorial:ℝ)⁻¹ * iteratedDeriv m f 0)):=by
 obtain ⟨s,hs,hh⟩:= h.contDiffOn (m:=(m:WithTop ℕ∞)) le_rfl (by simp)
 obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp hs; let I:=Metric.ball (0:ℝ) r; have hz: (0:ℝ)∈I:= mem_ball_self hr
 have hw (x:ℝ): taylorWithinEval f m I 0 x=(m.factorial:ℝ)⁻¹*x^m *iteratedDeriv m f 0:=by
    have hk i: iteratedDerivWithin i f I 0= iteratedDeriv i f 0:=iteratedDerivWithin_of_isOpen isOpen_ball hz
    rw [taylor_within_apply,sum_range_succ, sum_eq_zero,zero_add,hk]; simp
    intro i hi; rw [hk,he _ (mem_range.mp hi),smul_zero]
 have hp := Real.taylor_tendsto (n:=m) (convex_ball (0:ℝ) r) hz (hh.mono H)
 unfold I at hw; simp_rw [hw, sub_zero,nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hz)] at hp
 let C:= (m.factorial:ℝ)⁻¹ * iteratedDeriv m f 0; have hG:=hp.add_const C; rw [zero_add] at hG
 refine (hG.mono_left (nhdsWithin_le_nhds (s:={(0:ℝ)}ᶜ))).congr' ?_; filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:={(0:ℝ)}ᶜ)] with t ht; have hx:t≠0:=ht; unfold C; field_simp; ring
private def silo(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F] : F≃L[ℝ](Fin (Module.finrank ℝ F)→ℝ):=(Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv -- def
lemma extendJ (k n:ℕ)(f:E→F)(x:E)(h:ContDiffAt ℝ (n:ℕ) f 0)(hk:k≤n)(L:F→L[ℝ]ℝ): trim k (L ∘ f) x=L (trim k f x):=by
 unfold trim cake Tensor.diagonal; rw [L.iteratedFDeriv_comp_left h (by exact_mod_cast hk), _root_.smul_apply, _root_.smul_apply, map_smul]; rfl
lemma argent (h:ContDiffAt ℝ (m:ℕ) f 0): cFoot m f ↔ crystal m f (trim m f):=by
 let V:=silo F; let I:=Fin (Module.finrank ℝ F); let L(i:I): F→L[ℝ]ℝ:= (ContinuousLinearMap.proj i).comp V.toContinuousLinearMap
 have hx(i:I):ContDiffAt ℝ (m:ℕ) ((L i) ∘ f) 0:=(L i).contDiff.contDiffAt.comp (0:E) h
 have ht(i:I)(x:E): ContDiffAt ℝ (m:ℕ) (fun t:ℝ=> ((L i) ∘ f) (t • x)) 0:=(show ContDiffAt ℝ (m:ℕ) ((L i) ∘ f) ((0:ℝ) • x) by rw [zero_smul]; exact hx i).comp (g:=L i ∘ f) (f:=fun t:ℝ=> t • x) 0 (by fun_prop)
 constructor
 · intro p x
   have hh:Tendsto (fun t:ℝ=> V ((t^m)⁻¹ • f (t • x))) (𝓝[≠] 0) (𝓝 (V (trim m f x))):=by
      apply tendsto_pi_nhds.mpr; intro i; have hg:= farm (ht i x) fun j hj=> by rw [Next.Foundations.iteratedDeriv_on_line ((hx i).of_le (Nat.cast_le.mpr hj.le)), (L i).iteratedFDeriv_comp_left h (by exact_mod_cast hj.le),p _ hj]; change L i 0= _; simp
      rw [Next.Foundations.iteratedDeriv_on_line (hx i)] at hg; change Tendsto (fun t:ℝ=> L i ((t^m)⁻¹ • _)) _ (𝓝 (L i _)); simp_rw [map_smul,← extendJ _ _ _ _ h le_rfl]; convert hg using 1; ext1 t; change (t^m)⁻¹ * _= _; ring_nf; rfl
      rfl
   have H:= (V.symm.continuous.tendsto _).comp hh; simpa only [comp_def,V.symm_apply_apply] using H
 intro he n hg; ext1 z; apply V.injective; ext1 i; let g:=L i∘ f; have hp := hx i
 have hG(x): Tendsto (fun t:ℝ=> g (t • x)/t^n) (𝓝[≠] 0) (𝓝 0) := Iteration.Jets.drop hg (show Tendsto _ (𝓝[≠] 0) (𝓝 (L i (trim m f x))) from (((L i).continuous.tendsto _).comp (he x)).congr (fun t=>by unfold g; simp [mul_comm,div_eq_mul_inv])) -- tune
 have hE:= Iteration.Jets.negligible (hp.of_le (Nat.cast_le.mpr hg.le)) hG n le_rfl; rw [(L i).iteratedFDeriv_comp_left h (by exact_mod_cast hg.le)] at hE; change (L i).compContinuousMultilinearMap _ z=L i 0; rw [hE,map_zero]; rfl
lemma asideF (h:ContDiffAt ℝ (m:ℕ) f 0)(y:E→ F)(p:crystal m f y): cFoot m f ∧ ∀ x,y x=trim m f x:=by
 have he:cFoot m f:=by
    let V:= silo F; intro i e; have h':ContDiffAt ℝ (i:ℕ) f 0:=h.of_le (Nat.cast_le.mpr e.le); ext1 x; apply V.injective; ext1 a; let L: F →L[ℝ]ℝ:=(ContinuousLinearMap.proj a).comp V.toContinuousLinearMap
    have hl(z:E): Tendsto (fun t:ℝ=> L (f (t • z))/t^m) (𝓝[≠] 0) (𝓝 (L (y z))):= (((L.continuous.tendsto _).comp (p z))).congr (fun x=>by simp [div_eq_inv_mul])
    have hh:= Iteration.Jets.negligible (L.contDiff.contDiffAt.comp 0 h') (fun y=>Iteration.Jets.drop e (hl y)) i le_rfl; rw [L.iteratedFDeriv_comp_left h' le_rfl] at hh; change L.compContinuousMultilinearMap _ x=L 0; rw [hh,map_zero]; rfl
 exact ⟨he,fun x=>tendsto_nhds_unique (p x) ((argent h).mp he x)⟩
lemma ride_eps(h:ContDiffAt ℝ (m:ℕ) f 0)(g:G→E)(e:ContDiffAt ℝ (m:ℕ) g 0)(k:g 0=0)(p:cFoot m f): cFoot m (f∘ g)∧ crystal m (f ∘ g) (fun x : G=> trim m f (fderiv ℝ g 0 x)):=by
 let L:= fderiv ℝ g 0
 have hv:ContDiffAt ℝ (m:ℕ) (f ∘ g) 0:=(k.symm ▸ h).comp (f:=g) (g:=f) _ e
 have hx:ContDiffAt ℝ (m:ℕ) (f ∘ L) 0:=((map_zero L).symm ▸ h).comp (g:=f) (f:=L) _ L.contDiff.contDiffAt
 have hh(i:ℕ)(q:i≤m): iteratedFDeriv ℝ i (f∘ g) 0=iteratedFDeriv ℝ i (f∘ L) 0:=by
    ext1 w; let U:=silo F; apply U.injective; funext a; let P:F→L[ℝ]ℝ:= (ContinuousLinearMap.proj a).comp U.toContinuousLinearMap
    have ht:=Iteration.Jets.tangent (d:=m) (P.contDiff.contDiffAt.comp 0 h) (g:=g) e k (fun j w=> by rw [P.iteratedFDeriv_comp_left h (by exact_mod_cast w.le),p _ w]; ext1 u; change P 0=0; rw [map_zero]) i q
    change iteratedFDeriv ℝ i (P∘ (f∘g)) 0=iteratedFDeriv ℝ i (P ∘ (f ∘ L)) 0 at ht; rw [P.iteratedFDeriv_comp_left hv (by exact_mod_cast q), P.iteratedFDeriv_comp_left hx (by exact_mod_cast q)] at ht; exact DFunLike.congr_fun ht w
 have ht:= asideF hx (fun x=>trim m f (L x)) fun x => by simpa only [Function.comp_apply,map_smul] using (argent h).mp p (L x)
 have hy : cFoot m (f ∘ g):=fun i s=> (hh i s.le).trans (ht.1 i s); refine ⟨hy,fun x=>?_⟩
 change Tendsto (fun t:ℝ=> (t^m)⁻¹ • f (g (t • x))) _ (𝓝 (trim m f (L x))); rw [show trim m f _= _ from ht.2 x,trim,cake, ← hh m le_rfl]; exact (argent hv).mp hy x
lemma flares {f:E→F}(g:ℝ→E)(h: ContDiffAt ℝ (m:ℕ) f 0)(e:ContDiffAt ℝ (m:ℕ) g 0)(x:E)(w:g 0=0)(t:HasDerivAt g x 0)(p:cFoot m f) : Tendsto (fun l:ℝ=> (l^m)⁻¹ • f (g l)) (𝓝[≠] 0) (𝓝 (trim m f x)):=by
 have hp:(fderiv ℝ g 0) 1=x:=t.deriv; simpa only [hp, Function.comp_apply, smul_eq_mul, mul_one] using (ride_eps h g e w p).2 (1:ℝ)
lemma nextF(h:ContDiffAt ℝ (m:ℕ) f 0)(p:crystal m f 0):cFoot (m+1) f:=by
 have hp:=asideF h 0 p
 let L:=silo F; intro j e; ext1 x; apply L.injective; funext i; let P:F→L[ℝ]ℝ:= (ContinuousLinearMap.proj i).comp L.toContinuousLinearMap
 have hl(z:E): Tendsto (fun t:ℝ=> P (f (t • z))/t^m) (𝓝[≠] 0) (𝓝 0):=by
    have he:=(P.continuous.tendsto _).comp (p z); simp only [Function.comp_def, Pi.zero_apply,map_zero,map_smul, smul_eq_mul, inv_mul_eq_div] at he; exact he
 have hx:j≤m:=by omega
 have hh:= Iteration.Jets.negligible (P.contDiff.contDiffAt.comp 0 h) hl j hx; rw [P.iteratedFDeriv_comp_left h (by exact_mod_cast hx)] at hh; change P.compContinuousMultilinearMap _ x=P 0; rw [hh,map_zero]; rfl
end YM.CF.Nacre
