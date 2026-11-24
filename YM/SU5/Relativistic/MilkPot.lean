import YM.SU5.Relativistic.Armor
/-! # free row stencil: smooth aliases up to arbitrarily high order on full observing box
 by compactification in all component coordinates and the overall max.
-/
set_option autoImplicit false
set_option maxHeartbeats 540000
noncomputable section
namespace YM.CF.Crest.Sleet.Sorcerer
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "w"=>3*Real.pi/2
local notation "Θ"=> closedBall (0:Bin) (3*Real.pi/2)
@[fun_prop] lemma ho (x:ℝ): ContDiffAt ℝ ω ((↑) : ℝ→ℂ) x:= Complex.ofRealCLM.contDiff.contDiffAt
private lemma sin_w (x:ℝ): skirt x= dslope Complex.sin 0 (↑(x/2:ℝ):ℂ):=by
 by_cases t:x=0
 · subst x; rw [skirt]; simp [dslope_same,(Complex.hasDerivAt_sin 0).deriv]
 have he:x/2≠0:=div_ne_zero t two_ne_zero
 rw [dslope_of_ne _ (by exact_mod_cast he), skirt,Real.sinc_of_ne_zero he,slope_def_field]; simp -- .ofreal
lemma evenSkirt : ContDiff ℝ ω skirt:=by
 have hp:DifferentiableOn ℂ (dslope Complex.sin 0) Set.univ:= (Complex.differentiableOn_dslope Filter.univ_mem).mpr (by fun_prop)
 have hc:ContDiff ℂ ω (dslope Complex.sin 0):= contDiff_iff_contDiffAt.mpr (fun i=> ((hp.analyticAt (Filter.univ_mem : Set.univ ∈ 𝓝 i))).contDiffAt)
 rw [funext sin_w]; exact (hc.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ω (fun x:ℝ=> x/2) by fun_prop)) -- tune
private lemma sin_unit (k:ℤ)(x:ℝ) : Real.sin (x+k*Real.pi)^8 = Real.sin x ^8:=by
 rw [Real.sin_add_int_mul_pi,mul_pow]; have he: |(-1:ℝ)^k|=1:=by rw [abs_zpow]; simp
 rw [←(Even.pow_abs (by decide: Even 8) ((-1:ℝ)^k)), he]; simp
private lemma replay (k:ℤ)(p:k≠0)(x:ℝ): skirt (x+φ*k)^8 =
    ( (k:ℝ)⁻¹:ℂ)^8 * (↑((2*Real.sin (x/2))/(φ+(k:ℝ)⁻¹*x):ℝ):ℂ)^8 ∨ x+φ*k=0 :=by
 by_cases t:x+φ*k=0; · exact Or.inr t
 left
 have hz:(k:ℝ) ≠0:=by exact_mod_cast p
 have he: φ+(k:ℝ)⁻¹*x=(k:ℝ)⁻¹*(x+φ*k):=by field_simp; ring
 rw [he,skirt,Real.sinc_of_ne_zero (div_ne_zero t two_ne_zero), ←Complex.ofReal_pow,←Complex.ofReal_pow,←Complex.ofReal_inv, ←Complex.ofReal_pow,←Complex.ofReal_mul]; congr 1
 rw [div_pow,show Real.sin ((x+φ*k)/2) ^8=Real.sin (x/2)^8 by rw [show (x+φ*k)/2=x/2+k*Real.pi by ring,sin_unit], div_pow]; field_simp <;> ring
abbrev Corner:= {j: Cover // j≠0}
abbrev Sail:= Bin × ℝ × Bin
private abbrev warp (i:Axis) (S:Finset Axis) (a:Sail) (x:Bin) :=
 let y:= a.2.1 • x + (2*Real.pi) • a.2.2; (∏ j:Axis, if j∈S then (↑((2*Real.sin (x j/2))/(φ+a.1 j*x j):ℝ):ℂ)^8 else skirt (x j)^8) *
     (a.2.1:ℂ)*(2*(y i:ℂ)/radius y)
abbrev sailRange : Set Sail:= (closedBall 0 1) ×ˢ ((Set.Icc 0 1) ×ˢ Metric.sphere 0 1)
lemma closedSail : IsCompact sailRange:= (isCompact_closedBall _ _).prod (isCompact_Icc.prod (isCompact_sphere _ _))
private lemma sapile {x:Bin}{a:Sail}(h:x∈ Θ)(e:a∈sailRange) (j:Axis) : φ+a.1 j*x j≠0:=by
 have hx: ‖x‖ ≤ w:= by simpa using Metric.mem_closedBall.mp h
 have hp: ‖a.1‖ ≤ 1:=by simpa using Metric.mem_closedBall.mp (e.1 : a.1 ∈ _)
 apply ne_of_gt; have hX:|x j|≤ w:=(norm_le_pi_norm x j).trans hx; have hv:|a.1 j|≤1:=(norm_le_pi_norm _ _).trans hp
 nlinarith only [neg_le_of_abs_le ((abs_mul _ _).trans_le (mul_le_mul hv hX (abs_nonneg _) zero_le_one)),pi_pos]
private lemma locus {a:Sail}{x:Bin}(h:x∈ Θ)(e:a∈sailRange): a.2.1 • x + (2*Real.pi) • a.2.2 ≠ 0:=by
 have hx: ‖x‖ ≤ w:= by simpa using Metric.mem_closedBall.mp h
 have hp: ‖a.2.2‖=1:= by simpa using Metric.mem_sphere.mp (e.2.2 : a.2.2 ∈ _)
 have he:= (e.2.1 : a.2.1 ∈ Set.Icc (0:ℝ) 1)
 intro z; have ht:a.2.1 •x= -((2*Real.pi) • a.2.2):= eq_neg_of_add_eq_zero_left z
 have hf:=congrArg norm ht; rw [norm_neg,norm_smul,norm_smul, hp, Real.norm_of_nonneg he.1, Real.norm_of_nonneg (by positivity)] at hf
 linarith only [pi_pos,hf, mul_le_mul he.2 hx (norm_nonneg x) zero_le_one]
private lemma sailing {a:Sail}{x:Bin}(i:Axis)(S:Finset Axis)(h:x∈ Θ)(e:a∈sailRange) : ContDiffAt ℝ ω (Function.uncurry (warp i S)) (a,x):=by
 have hx(j:Axis): ContDiffAt ℝ ω (fun p:Sail×Bin=>if j∈S then (↑((2*Real.sin (p.2 j/2))/(φ+p.1.1 j*p.2 j):ℝ):ℂ)^8 else skirt (p.2 j)^8) (a,x):=by
    by_cases t:j∈S
    · simp only [if_pos t]; fun_prop (disch:= exact sapile h e _)
    simp only [if_neg t]; apply ContDiffAt.pow; exact (evenSkirt.comp (by fun_prop)).contDiffAt
 apply ContDiffAt.mul (ContDiffAt.mul (contDiffAt_prod (fun j _=>hx j)) (by fun_prop)); have he:(↑(radius _):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (radius_pos _ (locus h e)).ne'; let f(q:Sail×Bin):=q.1.2.1 • q.2 + (2*Real.pi) • q.1.2.2; let g(q:Sail×Bin):= (↑(radius (f q)):ℂ); have hc:ContDiffAt ℝ ω g (a,x):=by unfold g radius; apply (ho _).comp (f:=fun p:Sail × Bin=> ∑ i:Axis,(f p i)^2); apply ContDiffAt.sum; intro j _; unfold f; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; fun_prop
 have hP: ContDiffAt ℝ ω (fun q:Sail×Bin=> 2 * (↑(f q i):ℂ)) (a,x):=by unfold f; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; fun_prop
 simp only [div_eq_mul_inv]; exact hP.mul (hc.inv (show g (a,x)≠0 from he))
-- represent
private def here(v:Cover):Bin:=fun j=>(v j:ℝ)
private lemma standing (v:Corner) : 1 ≤ ‖here v.val‖:=by
 obtain ⟨i,h⟩:= Function.ne_iff.mp v.property; apply le_trans _ (norm_le_pi_norm (here v.val) i); unfold here; rw [Real.norm_eq_abs,←Int.cast_abs]; exact_mod_cast (show 1≤|v.val i| from abs_pos.mpr h)
def fillS (v:Corner): Sail := (fun j=>(v.val j:ℝ)⁻¹, ‖here v.val‖⁻¹, ‖here v.val‖⁻¹ • here v.val)
lemma stationS (v:Corner):fillS v∈ sailRange:=by
 have hx:=standing v; have hp:0<‖here v.val‖:=zero_lt_one.trans_le hx
 refine ⟨Metric.mem_closedBall.mpr ?_,⟨inv_nonneg.mpr (norm_nonneg _),inv_le_one_of_one_le₀ hx⟩, Metric.mem_sphere.mpr ?_⟩
 · rw [dist_zero_right]; apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; unfold fillS; dsimp only; rw [Real.norm_eq_abs,abs_inv, ←Int.cast_abs]; by_cases h:v.val i=0; · simp [h]
   exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1≤|v.val i| from abs_pos.mpr h))
 rw [dist_zero_right]; unfold fillS; dsimp only; rw [norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hp.ne']
private def chips (v:Corner):ℝ:= ∏ j:Axis,if v.val j≠0 then (v.val j:ℝ)⁻¹^8 else 1
private def surgeS (v:Corner):= Finset.univ.filter fun i=>v.val i≠0
private lemma relate (x:Bin)(p:x∈Θ)(v:Corner)(i:Axis) : slat x v.val i= chips v • warp i (surgeS v) (fillS v) x:=by
 let A:= fillS v; let H:= x+stem v.val; let T:= A.2.1 • x+(2*Real.pi) • A.2.2
 have hy:= locus p (stationS v); have he(j):T j=A.2.1* H j:=by unfold T A H stem fillS here; simp only [Pi.smul_apply,smul_eq_mul, Pi.add_apply]; ring
 have hk:0<A.2.1:= inv_pos.mpr (zero_lt_one.trans_le (standing v))
 have hf:radius T=A.2.1^2*radius H:=by unfold radius; simp_rw [he,mul_pow]; rw [Finset.mul_sum]
 have hl:radius H≠0:= fun z=> (radius_pos T hy).ne' (by rw [hf,z,mul_zero])
 have hX: weave H ^8= (chips v:ℂ)*∏ j:Axis, if j∈surgeS v then (↑((2*Real.sin (x j/2))/(φ+A.1 j*x j):ℝ):ℂ)^8 else skirt (x j)^8 :=by
    unfold weave chips; rw [←Finset.prod_pow,Complex.ofReal_prod,←Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; simp only [surgeS,mem_filter,Finset.mem_univ,true_and]; split_ifs with w₀
    · rcases replay (v.val j) w₀ (x j) with h|h
      · rw [Complex.ofReal_pow,Complex.ofReal_inv]; exact h
      have he:=sapile p (stationS v) j; change φ+(v.val j:ℝ)⁻¹* x j ≠0 at he; have hX:(v.val j:ℝ)≠0:=by exact_mod_cast w₀
      exact (he (by field_simp; linarith only [h])).elim
    · simp [H,stem,Classical.not_not.mp w₀]
 unfold slat; rw [hX]; let U:ℂ:= 2*(T i:ℂ)/radius T
 have hs: (2:ℂ)*(H i:ℂ)/(↑(radius H):ℂ)= (A.2.1:ℂ)*U:=by unfold U; rw [hf,he]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hk.ne'] <;> ring
 change _*(2*(H i:ℂ)/_)= chips v • (_*_*U); rw [hs,Complex.real_smul]; ring
-- asymptotically every Wallet receipt for these Mell terms
private lemma chide (k:ℤ) : let z:ℝ:= if k≠0 then (k:ℝ)⁻¹^8 else 1
    0≤ z ∧ z ≤ 4*((1+(k.natAbs:ℝ))^2)⁻¹:=by
 by_cases t:k=0
 · subst k; norm_num
 dsimp only; rw [if_pos t]; have he:1 ≤ (k.natAbs:ℝ):=by exact_mod_cast (Int.natAbs_pos.mpr t)
 refine ⟨by positivity,?_⟩
 rw [← (Even.pow_abs (by decide:Even 8) ((k:ℝ)⁻¹)), abs_inv, ←Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]; refine le_trans (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ he) (by omega:2≤8)) ?_ -- Nat.cast_natAbs?
 rw [inv_pow]; field_simp; nlinarith only [he]
private lemma chin (v:Corner):0 ≤ chips v∧ chips v ≤ 4^4*income v.val:=by
 refine ⟨Finset.prod_nonneg (fun i _=>(chide (v.val i)).1), le_trans (Finset.prod_le_prod (f:=fun j:Axis=>_) (fun i _=>(chide (v.val i)).1) (fun i _=>(chide (v.val i)).2)) ?_⟩; apply le_of_eq; rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib,Finset.prod_pow]; congr 1; simp -- maybe order
private lemma pot : Summable chips:= by
 exact Summable.of_nonneg_of_le (fun i=>(chin i).1) (fun i=>(chin i).2) ((wallet.mul_left (4^4)).subtype _)
section
variable {X F E:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup E][NormedSpace ℝ E]
private lemma cont_part (V:E→F→X) {i:E}{j:F}(p:ContDiffAt ℝ ω (uncurry V) (i,j))(k:ℕ) : ContDiffAt ℝ ω (fun x:E×F=> iteratedFDeriv ℝ k (V x.1) x.2) (i,j):=by
 induction k with
 | zero => simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]; exact (continuousMultilinearCurryFin0 ℝ F X).symm.contDiff.contDiffAt.comp _ p
 | succ k ih=>
    simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have he : ContDiff ℝ ω ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => F) X).symm) := by fun_prop
    refine he.contDiffAt.comp (i,j) (f:=fun x:E×F=> fderiv ℝ (iteratedFDeriv ℝ k (V x.1)) x.2) ?_
    exact (ih.comp (f:=fun y:(E×F)×F=>(y.1.1,y.2)) ((i,j),j) (by fun_prop)).fderiv (f:=fun x:E×F=>iteratedFDeriv ℝ k (V x.1)) contDiffAt_snd le_top
-- derivative series compact dominance
private lemma snowfall {ι: Type} [CompleteSpace X] (N:ℕ)(g:ι→ F → X)(T:Set F)(e:IsOpen T)(t:IsPreconnected T)
    (u: ∀ i x,x∈T→ContDiffAt ℝ ω (g i) x) (p:∀ j:ℕ,∃ b:ι→ℝ, Summable b∧ ∀ i x,x∈ T → ‖iteratedFDeriv ℝ j (g i) x‖ ≤ b i) : ContDiffOn ℝ (↑N) (fun x=> ∑' i,g i x) T:=by
 induction N generalizing X with
 | zero=>
    obtain ⟨b,q,r⟩:=p 0; exact contDiffOn_zero.mpr (continuousOn_tsum (fun i=>fun x h=>(u i x h).continuousAt.continuousWithinAt) q (fun i x h=> (norm_iteratedFDeriv_zero (𝕜:=ℝ)).symm.trans_le (r i x h)))
 | succ k ih=>
    rw [Nat.cast_add_one,contDiffOn_succ_iff_fderiv_of_isOpen e]
    obtain ⟨b,q,r⟩:=p 1; have ht(x)(h:x∈T):HasFDerivAt (fun x=>∑' i,g i x) (∑' i,fderiv ℝ (g i) x) x:=by
       obtain ⟨a,hc,v⟩:=p 0
       apply hasFDerivAt_tsum_of_isPreconnected (E:=F) q e t (fun i x h=> ((u i x h).differentiableAt (by simp)).hasFDerivAt) (fun i x h=> by simpa only [norm_iteratedFDeriv_one] using r i x h) h (Summable.of_norm_bounded hc (fun i=>by rw [←norm_iteratedFDeriv_zero (𝕜:=ℝ)]; exact v i x h)) h
    refine ⟨fun i h=>(ht i h).differentiableAt.differentiableWithinAt,fun h=>by simp at h,(ih _ (fun i x h=>(u i x h).fderiv_right le_top) (fun j=>?_)).congr (fun i h=> (ht i h).fderiv)⟩ -- order
    obtain ⟨B,q,r⟩:=p (j+1); exact ⟨B,q,fun i x h=> norm_iteratedFDeriv_fderiv.trans_le (r i x h)⟩
end
abbrev feast (i:Axis)(x:Bin):= ∑' v: Corner,slat x v.val i
local notation "E"=> ball (0:Bin) (3*Real.pi/2)
lemma buffet (i:Axis)(k:ℕ):ContDiffOn ℝ (↑k) (feast i) E:=by
 let g(v:Corner) (x:Bin):= warp i (surgeS v) (fillS v) x; let T(v:Corner):= chips v • g v
 have he(v)(x)(z:x∈Θ):ContDiffAt ℝ ω (g v) x:= by
    exact (sailing i (surgeS v) ‹_› (stationS v)).comp (f:=fun x:Bin=> (fillS v,x)) x (by fun_prop)
 --
 apply (snowfall k T E isOpen_ball (convex_ball ..).isPreconnected (fun v x h=> (he v x (ball_subset_closedBall h)).const_smul (chips v)) _).congr (fun x h=> tsum_congr (fun v=> relate x (ball_subset_closedBall h) v i))
 intro j
 have ht (S:Finset Axis) : ∃ B:ℝ,∀ p∈sailRange ×ˢ Θ, ‖iteratedFDeriv ℝ j (warp i S p.1) p.2‖ ≤ B:= (closedSail.prod (isCompact_closedBall ..)).exists_bound_of_continuousOn (fun x h=> (cont_part (warp i S) (sailing i S h.2 h.1) j).continuousAt.continuousWithinAt)
 choose F w' using ht; let A:=∑ i:Finset Axis,|F i|
 refine ⟨_,pot.mul_left A,fun v x h=>?_⟩; unfold T; rw [iteratedFDeriv_const_smul_apply ((he v x (ball_subset_closedBall h)).of_le le_top),norm_smul, Real.norm_of_nonneg (chin v).1];
 apply (mul_le_mul_of_nonneg_left ((w' (surgeS v) (fillS v,x) ⟨stationS v,ball_subset_closedBall h⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (f:=fun i=>|F i|) (fun i _=>abs_nonneg _) (Finset.mem_univ (surgeS v))))) (chin v).1).trans_eq (mul_comm ..)
lemma snack (i:Axis)(x:Bin)(p:x∈ Θ):Summable (fun v: Corner=>slat x v.val i):=by
 have H (S:Finset Axis) : ∃ B:ℝ,∀ q∈sailRange ×ˢ Θ, ‖warp i S q.1 q.2‖ ≤ B:= (closedSail.prod (isCompact_closedBall ..)).exists_bound_of_continuousOn (fun q h=>(sailing i S h.2 h.1).continuousAt.continuousWithinAt)
 choose F w' using H; let A:=∑ i:Finset Axis,|F i|
 refine Summable.of_norm_bounded (pot.mul_left A) (fun v=>?_); rw [relate x p v i,norm_smul,Real.norm_of_nonneg (chin v).1]; exact (mul_le_mul_of_nonneg_left ((w' (surgeS v) (fillS v,x) ⟨stationS v,p⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (f:=fun i=>|F i|) (fun i _=>abs_nonneg _) (Finset.mem_univ (surgeS v))))) (chin v).1).trans_eq (mul_comm ..)
end YM.CF.Crest.Sleet.Sorcerer
#print axioms YM.CF.Crest.Sleet.Sorcerer.buffet
