import YM.SU5.FiniteGaugeData.Largo.Helm
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset
open scoped Topology BigOperators Pointwise Polynomial
variable (o:Rim) (p: Slab o) (r t:ℝ)
def keyL(x:Tip ×ℤ)(t:ℝ):ℝ:= let v:= scar t x.2; floam o x.1 * (Real.sinc (v/2))^8*(2*v / ((bush o x.1)^2+v^2))
def hymn(z:ℂ):ℂ:= acre (pinHeight o) (heritage o) z
section
include p
private lemma pure_domain : (r:ℂ)∉ Set.range (pinHeight o):=by rintro ⟨⟨⟨i,j⟩,l⟩,e⟩; have he:=(altitude o i j l).1; rw [e,Complex.ofReal_im,abs_zero] at he; exact (bush_pos o i p).ne he
lemma soma(z:ℂ): Summable (fun i:Locks=> ‖heritage o i z/(z-pinHeight o i)‖):= by obtain ⟨e,h,g,_⟩:=(slippery o p).analyticL z; exact g z (by simpa using h)
lemma crew (x:Tip×ℤ): ∑ b:Bool, heritage o (x,b) r/((r:ℂ)-pinHeight o (x,b))=keyL o x r:=by
 let v:= scar r x.2; let s:= bush o x.1; let t:=floam o x.1; let a:= Real.sinc (v/2)
 have he: afar (r:ℂ) x.2 = v:= by unfold afar v scar; push_cast; rfl
 have hp:s≠0:=(bush_pos o x.1 p).ne'
 let g:= pinHeight o; let K(y):= (r:ℂ)-g (x,y); have h(b): K b ≠0:= sub_ne_zero.mpr (fun e=>pure_domain o p r ⟨_,e.symm⟩)
 have hB:(s:ℂ)^2+(v:ℂ)^2≠0:=by exact_mod_cast (show s^2+v^2 ≠0 from (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hp) (sq_nonneg _)).ne')
 have hv: K false=v+Complex.I*s:=by unfold K g pinHeight afar v scar; push_cast; ring
 have hz: K true=v- Complex.I*s:=by unfold K g pinHeight afar v scar; push_cast; simp only [if_true]; ring
 have hx(l):heritage o (x,l) (r:ℂ)=((((t*a^8):ℝ)):ℂ):=by unfold heritage; dsimp only; rw [he, ←show (((v/2:ℝ)):ℂ)=(v:ℂ)/2 from (by push_cast; rfl), h_real]; push_cast; rfl
 simp_rw [hx]; unfold keyL; rw [Fintype.sum_bool]; change ((t*a^8:ℝ):ℂ) / K true + _= ((t*a^8*(2*v/(s^2+v^2)):ℝ):ℂ); change ((_:ℝ):ℂ)/_+ ((_:ℝ):ℂ)/ K false=_; push_cast; let d:= (s:ℂ)^2+(v:ℂ)^2; have he:d=K true*K false:=by unfold d; rw [hv,hz]; ring_nf; simp
 unfold d at he; rw [he]; field_simp [h]; rw [hv,hz]; ring
-- Summable real version keyL and hymn expressed on real. Allows frequency recurrence.
lemma rateDim : Summable (fun x: Tip × ℤ=> ‖keyL o x r‖):=by
 let f(x:Locks):= ‖heritage o x (r:ℂ)/((r:ℂ)-pinHeight o x)‖; apply Summable.of_nonneg_of_le (fun x=>norm_nonneg _) (f:=fun i=>∑' a:Bool, f (i,a)); · intro i; rw [← Complex.norm_real, ← crew o p, tsum_fintype]; exact norm_sum_le ..
 exact (summable_prod_of_nonneg (f:=f) (fun x=>norm_nonneg _)).1 (soma o p _)|>.2
lemma onActual : hymn o (r:ℂ)= ∑' i: Tip×ℤ, ((keyL o i r:ℝ):ℂ):= by
 unfold hymn acre; rw [Summable.tsum_prod' (soma o p _ |>.of_norm)]; simp_rw [tsum_fintype (β:=Bool),crew o p]; intro i; exact (hasSum_fintype _).summable
lemma epoch : Function.Periodic (fun r:ℝ=>hymn o r) τ:=by
 let e:Tip×ℤ ≃ Tip×ℤ:= Equiv.prodCongr (Equiv.refl Tip) (Equiv.addRight 1); intro t; dsimp only; rw [onActual o p,onActual o p]; nth_rw 2 [← Equiv.tsum_eq e]
 refine tsum_congr fun i=>?_ ; unfold keyL; have he: scar (t+τ) i.2= scar t (e i).2:=by change _ = scar t (i.2+1); unfold scar; push_cast; ring
 rw [he]; rfl
omit p
lemma hugeB (C:ℝ): ∃ q,bush o q ≥ C:=by
 obtain ⟨n,t⟩:=exists_nat_gt ((C-o 0)/τ); let q:Tip:=fun _=> n; refine ⟨q,(le_abs_self _).trans (bush_ge o q 0) |>.trans' ?_⟩; unfold scar q; push_cast; linarith only [(div_lt_iff₀ tau_pos).mp t]
private abbrev P_A(Z:ℝ): ℂ := Complex.I* Z
private abbrev L₀(x:Locks):= pinHeight o x
include p
lemma bumpOrder (x:Tip) : (∑ j∈ (slippery o p).stash (P_A (bush o x)), heritage o j (P_A (bush o x)))≠0:=by
 let K:= slippery o p; let v:=bush o x; let P:= Complex.I*v; let h(j:Locks):= heritage o j P; let T:= K.stash P
 let b:=Real.sinh (v/2)/(v/2); have hP:= s_height_pos _ (half_pos (bush_pos o x p)); have he:0<b:= hP.2
 let A(j:Locks):= floam o j.1.1 * b^8; have ha(j:Locks):0<A j:=mul_pos (floam_pos _ _ p) (pow_pos he _); let i:Locks:= ((x,0),true); have hu: i∈T:= (K.store ..).mpr (by unfold P i pinHeight; simp [afar,v]) -- L₀ not in goal
 have hv : (∑ i∈ T,h i).re >0:=by
    rw [Complex.re_sum]; refine Finset.sum_pos (fun j hj=>?_) ⟨i,hu⟩; obtain ⟨⟨y,n⟩,l⟩:=j; have hg: pinHeight o ((y,n),l)=P:= (K.store ..).1 hj; have hw:n=0:= by
       have hx:= (altitude o y n l).2; rw [hg] at hx; unfold P at hx; have ht:0<τ:=tau_pos; simp only [Complex.I_mul_re,Complex.ofReal_im, neg_zero,abs_zero] at hx; exact_mod_cast abs_eq_zero.mp ((mul_eq_zero.mp hx.symm).resolve_left ht.ne')
    subst n; apply lt_of_lt_of_le (ha ((y,0),l)); refine Eq.ge ?_; unfold h heritage A; dsimp only; rw [show afar P 0/2= P_A (v/2) from (by unfold P_A P; simp [afar]; ring),hP.1]; norm_cast
 change ∑ i∈T,h i≠ 0; exact fun hm=> by rw [hm] at hv; exact lt_irrefl _ hv -- tune
end
local notation "Cι"=> (Set.range (pinHeight o))ᶜ
private abbrev clockB(x:ℂ):ℂ:= Complex.exp (Complex.I*x)
include p
lemma notRational (P:Polynomial ℂ)(h:P≠0)(G:ℂ→ℂ)(v:Differentiable ℂ G) (q:∀ t:ℝ,G t= P.eval (Complex.exp (Complex.I*t)) * hymn o t): False:= by
 let A(w:ℂ):= P.eval (clockB w); have hA:Differentiable ℂ A:= P.differentiable.comp (by unfold clockB; fun_prop)
 have H:= slippery o p; have hx : Set.EqOn G (A*hymn o) (Cι):= by
    apply AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (v.differentiableOn.analyticOnNhd (slippery o p).openGate) ((hA.differentiableOn.mul (fun w q=>(H.smoothOff w q).differentiableWithinAt)).analyticOnNhd H.openGate) ((Set.Countable.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (Set.countable_range (pinHeight o))).isConnected.isPreconnected) (pure_domain o p (0:ℝ))
    -- frequently equality via sequence
    intro g; obtain ⟨ε,h,u⟩:=Metric.mem_nhdsWithin_iff.mp g; let t:=ε/2; have he:0<t:=half_pos h; refine u ⟨Metric.mem_ball.mpr ?_,(show (t:ℂ)∈{((0:ℝ):ℂ)}ᶜ from by simp [he.ne'])⟩ (q t)
    simpa [dist_zero_right, abs_of_pos he, Real.norm_eq_abs] using (show t<ε from half_lt_self h)
 have hv(y:Tip): P.eval ((Real.exp (-(bush o y)):ℝ):ℂ)=0:=by
    let P:= P_A (bush o y); have hz: A P=0:=by
       apply (mul_eq_zero.mp ?_).resolve_right (bumpOrder o p y); let s:=∑ j∈H.stash P,heritage o j P; apply tendsto_nhds_unique_of_eventuallyEq (l:=(𝓝[≠] P)) (((hA P).continuousAt.continuousWithinAt).tendsto.mul (H.localOrder P)) (g:=fun w=> (w-P)*G w) ?_ ?_
       · simpa using! ((show Continuous (fun w=> (w-P)*G w) from (continuous_id.sub continuous_const).mul v.continuous).continuousWithinAt (x:=P) (s:={P}ᶜ)).tendsto
       · filter_upwards [H.floorMe P rfl|>.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin (s:={P}ᶜ) (a:=P)] with x u f
         have h:x∈(Set.range (pinHeight o))ᶜ:=by
            rintro ⟨y,r⟩; by_cases b:y∈H.stash P; · exact f (r ▸ (H.store ..).1 b)
            exact u y b r
         change A x*((x-P)*hymn o x)=_; rw [hx h]; change _=(x-P)*(A _* _); ring
    unfold A clockB P P_A at hz; rw [←mul_assoc, Complex.I_mul_I, neg_mul, one_mul, ←Complex.ofReal_neg, ←Complex.ofReal_exp] at hz; exact hz
 obtain ⟨S1,hP,X⟩: ∃ ε:ℝ,0<ε∧∀ w:ℂ, P.eval w=0 → w≠0 → ε≤‖w‖:=by
    let B:= P.roots.toFinset.erase 0; obtain ⟨ε,g,e⟩:= (((eventually_all_finset B).mpr (fun w u=> ge_mem_nhds (show 0<‖w‖ from norm_pos_iff.mpr (mem_erase.mp u).1))).filter_mono nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin (s:=Set.Ioi (0:ℝ)) (a:=0))).exists; exact ⟨ε,e,fun x p q=>g x (mem_erase.mpr ⟨q, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots h).2 p)⟩)⟩
 obtain ⟨y,u⟩:=hugeB o (-Real.log S1+1); let z:ℝ:= Real.exp (-bush o y); have he:0<z:=Real.exp_pos _; have hk:= X _ (hv y) (ofReal_ne_zero.mpr he.ne'); simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hk; exact not_lt_of_ge hk ((Real.exp_lt_exp.mpr (show -(bush o y) < Real.log S1 from (by linarith))).trans_eq (Real.exp_log hP))
end YM.CF.Window.Largo
