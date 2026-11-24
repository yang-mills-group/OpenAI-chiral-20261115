import YM.SU5.Selected.Rail.Traie
/-! # Transverse phase of a fixed displacement. ALL finite offsets. Construct positive ball lower using one alias.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
local notation "d" y:max v:max=> dollar y v
def grappa (W:FaceL)(x:Facet3):ℂ:= prefixG W (road x)
@[simp] lemma grappa_0 (W:FaceL): grappa W 0=1:= by unfold grappa prefixG; simp [road]
@[fun_prop] lemma grappa_c(W:FaceL): Continuous (grappa W):= (prefix_c _).comp road_c
lemma grappa_m(W:FaceL)(x:Facet3): |(grappa W x).re| ≤ 1:= (Complex.abs_re_le_norm _).trans (prefix_norm ..).le
variable {k n:ℕ}{δ:ℝ}(k:ℕ)(W:FaceL)
-- pick anchor x with δ small and s2 positive. polynomials. 
variable {p:ℕ} (Z:Fin p →ℂ)
def plum(Z: Fin p→ℂ) (y:Facet3) (v:FaceL):= ∑ i:Fin p,(d y v^ i.val:ℝ) * Z i -- THIS may coerce bad! check
lemma pace_c(v:FaceL) : Continuous (fun y=>d y v):=by unfold dollar tempoE tempoL turn; fun_prop
lemma plum_c(v:FaceL): Continuous (fun y=> plum Z y v):= by unfold plum; have h:= pace_c v; fun_prop -- maybe real coe
def focus(x:ℝ): Facet3:= Pi.single 2 x
private lemma stay_0 (x:Facet3): tempoL x 0=x:=by funext i; simp [tempoL,turn]
private lemma trail (x:ℝ): tempoE (focus x)=|x|:=by
 unfold focus tempoE; rw [sum_eq_single 2]; · simp [Real.sqrt_sq_eq_abs]
 · intro w _ h; simp [h]
 simp
private lemma fall(x:ℝ): ‖focus x‖=|x|:= Pi.norm_single _
private lemma sanction {x:ℝ}(h:0<x)(p:x<π):0< stake k 4 (focus x) 0:=by
 unfold stake dollar summer; dsimp only; rw [stay_0 _,trail,if_pos rfl,abs_of_pos h]; let s:=focus x; have he:sol s=sinc (x/2):=by
    unfold sol; rw [Finset.prod_eq_single 2]; · simp [s,focus]
    · intro w _ h; simp [s,focus,h];
    simp
 have hv:0<sol s:=he.symm ▸ (show 0<Real.sinc (x/2) from ?_); rotate_left -- this rotates?
 · rw [Real.sinc_of_ne_zero (by positivity)]; exact div_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith only [h,p])) (by positivity)
 change 0<(1-Real.exp (-x))^ k*(2*sol s^8 * ((x+s 2)*sponsor _ _*_)); have hp:0<s 2 := by simpa [s,focus]
 have he:0<1-Real.exp (-x):= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)); have ht :0< weight x:=weight_pos h; unfold sponsor; positivity
private lemma sparkle (h:Z≠0){ε:ℝ}(z:0<ε) : ∃ t:ℝ,0<t∧t<ε ∧ plum Z (focus t) 0≠0:=by
 let f(i:Fin p):ℝ:= ε*(i.val+1:ℕ) / (p+1:ℕ); have h₀:0< (↑(p+1:ℕ):ℝ):= by positivity
 have hv(i:Fin p): 0<f i∧ f i<ε :=by
    unfold f; constructor; · positivity
    apply (div_lt_iff₀ h₀).mpr; gcongr; have e:=i.isLt; omega
 let a(i:Fin p):ℂ:= d (focus (f i)) 0; have hg(i:Fin p): a i= Real.exp (-(f i)):=by unfold a dollar; rw [stay_0 _,trail,abs_of_pos (hv i).1]
 have he:Injective a:=by
    intro i j h; rw [hg,hg] at h; apply Fin.ext; have ht(i:Fin p): f i / ε * (p+1:ℕ)=(((i.val+1:ℕ)):ℝ):=by unfold f; field_simp
    have h':f i=f j:= neg_inj.mp (Real.exp_injective (Complex.ofReal_injective h)); have hz:=ht j; rw [← h'] at hz -- binder tune
    exact Nat.add_right_cancel (Nat.cast_injective (R:=ℝ) ((ht i).symm.trans hz))
 by_contra! q; apply h; apply Matrix.eq_zero_of_mulVec_eq_zero (Matrix.det_vandermonde_ne_zero_iff.mpr he); ext1 i; simpa only [a,plum,← Complex.ofReal_pow, Matrix.mulVec,dotProduct, Pi.zero_apply,Matrix.vandermonde_apply] using q (f i) (hv i).1 (hv i).2
-- Root stake times x neighbors. proof pointwise bound δ ball around 0 from grappa (>0).
def royalty(k:ℕ)(W:FaceL)(Z:Fin p→ ℂ)(x:Facet3): ℝ:= (grappa W x).re * (stake k 4 x 0 * ‖plum Z x 0‖^2)
lemma hot {x:Facet3}(t:x∈ Cliff): ContinuousAt (royalty k W Z) x:=by -- add x implicit
 let F:=tempoE
 have he: Continuous F:= by unfold F tempoE; fun_prop
 have hH: Continuous sol:=by unfold sol; fun_prop
 let v:=fun x:Facet3=> F x+x 2; have hx:F x≠0:=by have h:=born_e 0 t; rw [stay_0] at h; exact h.ne'
 let L(t:ℝ):= sponsor t 8; have hv: ContinuousAt L (F x):=by unfold L sponsor weight; fun_prop (disch:= assumption)
 unfold royalty stake summer; dsimp only; simp_rw [stay_0]; simp only [if_true]; exact ((Complex.continuous_re.comp (grappa_c W)).continuousAt).mul ((((continuousAt_const.sub (pace_c 0).continuousAt).pow k).mul ((continuousAt_const.mul (hH.pow _).continuousAt).mul (((he.add (continuous_apply 2)).continuousAt.mul (hv.comp he.continuousAt)).mul ((continuous_exp.comp ((he.neg).mul_const _)).continuousAt)))).mul (((plum_c Z 0).norm.pow _).continuousAt)) -- Continuous.mul_const
lemma crane : ∃ H, H∈ Set.Ioo 0 π ∧ ∀ y:Facet3, ‖y‖≤ H→ 0<(grappa W y).re:=by
 have hp:0<(grappa W 0).re:=by simp; -- simp
 obtain ⟨G,h,z⟩:= Metric.mem_nhds_iff.mp ((Complex.continuous_re.comp (grappa_c W)).continuousAt.tendsto.eventually (lt_mem_nhds hp)) -- z
 refine ⟨min (G/2) (π/2),⟨lt_min (by positivity) (by positivity),by linarith [min_le_right (G/2) (π/2),pi_pos]⟩,fun y v=> z (?_)⟩
 rw [mem_ball,dist_zero_right]; linarith [min_le_left (G/2) (π/2)]
lemma habitat (h:Z≠0) :∃ H y C R t:ℝ, 0<H∧ 0<C∧ t<1∧ 0<R∧ Real.exp (-H)<t∧ -- H cutoff, R radius aperture
   (∀ x:Facet3, ‖x‖ ≤ H→ 0<(grappa W x).re) ∧
    ∀ x:Facet3,x∈ball (focus y) R→ ‖x‖ ≤ H ∧ x∈Cliff ∧ t ≤ dollar x 0 ∧ C ≤ royalty k W Z x:=by
 obtain ⟨H,H₀,φ'⟩:=crane W; obtain ⟨y,p,g,r⟩:=sparkle Z h H₀.1; let u':=focus y; have hp: ‖u'‖=y:=(fall _).trans (abs_of_pos p); have hd:d u' 0=Real.exp (-y):=by unfold dollar u'; rw [stay_0 _,trail,abs_of_pos p]
 have hk:0<(grappa W u').re:=φ' _ (hp.trans_le g.le); obtain ⟨t,p',q⟩:=exists_between (show Real.exp (-H)< Real.exp (-y) from Real.exp_lt_exp.mpr (neg_lt_neg g)); have hm:u'∈Cliff:=⟨hill_mem.mpr (hp.trans_le (g.trans H₀.2).le), norm_pos_iff.mp (hp.symm ▸ p)⟩; obtain ⟨C,hC,b⟩:=exists_between (mul_pos hk (show 0< stake k 4 u' 0*‖plum Z u' 0‖^2 from mul_pos (sanction k p (g.trans H₀.2)) (sq_pos_of_ne_zero (norm_pos_iff.mpr r).ne'))); change C<royalty k W Z u' at b
 have ht: ∀ᶠ x in 𝓝 u', ‖x‖ ≤ H ∧ x∈Cliff ∧ t≤d x 0 ∧ C≤royalty k W Z x:= by
    filter_upwards [continuous_norm.continuousAt.tendsto.eventually (ge_mem_nhds (hp.trans_lt g)),(isOpen_compl_singleton (x:=(0:Facet3))).mem_nhds hm.2,(pace_c 0).continuousAt.tendsto.eventually (le_mem_nhds (hd.symm ▸ q)),(hot k W Z hm).tendsto.eventually (le_mem_nhds b)] with x v e z l; exact ⟨v,⟨hill_mem.mpr (v.trans H₀.2.le),e⟩,z,l⟩
 obtain ⟨R,g,q'⟩:=Metric.mem_nhds_iff.mp ht
 exact ⟨H,y,C,R,t,H₀.1,hC,lt_trans q (Real.exp_lt_one_iff.mpr (by linarith)),g,p',φ',fun x h=> q' h⟩
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms habitat
#print axioms hot
