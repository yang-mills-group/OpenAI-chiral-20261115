import YM.SU5.Reconstruction.Seams.Gulf
/-! # The two-axis seam limit. Normal family continuation through the spacelike window. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.ConePrice
namespace Sail
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup CF.Floral
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder Classical
variable (q : ℕ→ℂ→ℂ)
-- ultrafilter trick: avoid invoking sequential cluster extraction on all parameters and convergence
-- on strips simultaneously which doesn't follow just from bounded pointwise.
lemma limit_chance {D : Set ℂ} {Q : ℝ} (h:IsOpen D) (v:∀ n, Hol D (q n)) (e:∀ n,∀ z∈D,‖q n z‖≤ Q) :
    ∃ f:ℂ→ℂ,AnalyticOnNhd ℂ f D ∧ ∀ z∈ D, Tendsto (fun i=> q i z) ((Ultrafilter.of (atTop:Filter ℕ)) : Filter ℕ) (𝓝 (f z)) := by
  let A : Ultrafilter ℕ := Ultrafilter.of atTop
  let B := fun z=> A.map (fun i=> q i z)
  let f (z:ℂ) := lim (B z : Filter ℂ)
  have he z (p:z∈D): Tendsto (fun i=> q i z) A (𝓝 (f z)):= by
    let s:= Metric.closedBall (0:ℂ) Q
    obtain ⟨x,b,g⟩:= (isCompact_closedBall 0 Q).ultrafilter_le_nhds (B z) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (A:Filter ℕ), q i z∈ Metric.closedBall 0 Q
      apply Eventually.of_forall; intro i; exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact e i z p)
      )
    change (B z : Filter ℂ)≤ _; unfold f; rw [lim_eq g]; exact g
  exact ⟨f,(chalk h (Eventually.of_forall v) (Eventually.of_forall e) he).analyticOnNhd h,he⟩

def veil (r t a : ℝ) := {x : ℂ | r < x.re ∧ x.re < t ∧ x ∈ slit a}
lemma veil_open (r t a : ℝ) : IsOpen (veil r t a) := (isOpen_lt continuous_const Complex.continuous_re).inter ((isOpen_lt Complex.continuous_re continuous_const).inter (slit_open a))
lemma veil_connected (r t a : ℝ) : IsPreconnected (veil r t a) := by
  have h : slit a = {x : ℂ | x.im<a} ∩ {x:ℂ| -a<x.im} := by ext x; simp only [slit,abs_lt,mem_inter_iff,mem_setOf_eq]; exact and_comm
  unfold veil; rw [h]
  exact ((convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear r).inter ((convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear t).inter ((convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear a).inter (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear (-a))))).isPreconnected
lemma veil_real {r t a : ℝ} (p:0<a) (w:ℝ)(v:w∈ Ioo r t): (w:ℂ)∈ veil r t a:= ⟨by simpa using v.1,by simpa using v.2,slit_ground a p w⟩
lemma veil_slit {t r a}: veil r t a⊆ slit a:=fun _ h=>h.2.2
lemma piers {f g : ℂ→ℂ} {r t a : ℝ} (p:0<a)(w : r<t) (h:AnalyticOnNhd ℂ f (slit a))(b:AnalyticOnNhd ℂ g (veil r t a))
    (c:∀ z ∈ slit a,Tendsto (fun i=> q i z) ((Ultrafilter.of (atTop:Filter ℕ)) : Filter ℕ) (𝓝 (f z))) (U : Set ℝ) (D: Dense U) (e:∀ x∈ Ioo r t, x∈ U→ Tendsto (fun i=> q i (x:ℂ)) atTop (𝓝 (g (x:ℂ)))) : EqOn f g (veil r t a) := by
  obtain ⟨z,u,v⟩:= exists_between w; refine pioneer (veil_connected r t a) (veil_real p z ⟨u,v⟩) _ _ ⟨u,v⟩ (h.mono veil_slit) b ?_
  have hf : ContinuousOn (fun i:ℝ=> f (i:ℂ)) (Ioo r t):= h.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun i _=> slit_ground a p i)
  have hg : ContinuousOn (fun i:ℝ=> g (i:ℂ)) (Ioo r t):= b.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun i t=>veil_real p i t)
  intro x hx; haveI : (𝓝[Ioo r t ∩ U] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (D.open_subset_closure_inter isOpen_Ioo hx)
  apply tendsto_nhds_unique (f:= fun i:ℝ=>f (i:ℂ)) (l:=𝓝[Ioo r t∩ U] x) ((hf x hx).mono_left (nhdsWithin_mono _ inter_subset_left))
  · apply ((hg x hx).mono_left (nhdsWithin_mono x (s:=Ioo r t∩ U) inter_subset_left)).congr'; filter_upwards [self_mem_nhdsWithin] with i hi; exact tendsto_nhds_unique ((e i hi.1 hi.2).mono_left (Ultrafilter.of_le atTop)) (c _ (slit_ground a p i))

-- Given family agreeing with the two analytic prices in the limit on a REAL LINE SEGMENT each side, conclude
-- boundary value equality everywhere throughout the imaginary-time slit.
lemma seam_chance {f g : ℂ→ℂ} {a r Q : ℝ} (p:0<a) (he:0<r)
    (u:∀ n, Hol (slit a) (q n)) (e:∀ n,∀ z∈slit a,‖q n z‖≤Q) (U:Set ℝ) (d:Dense U)
    (b:AnalyticOnNhd ℂ f (veil 0 r a)) (w:AnalyticOnNhd ℂ g (veil (-r) 0 a))
    (b':∀ x∈Ioo 0 r,x∈U→ Tendsto (fun i=>q i (x:ℂ)) atTop (𝓝 (f x)))
    (w':∀ x∈Ioo (-r) 0,x∈U→ Tendsto (fun i=>q i (x:ℂ)) atTop (𝓝 (g x)))
    (z:ℂ)(zA : z∈ slit a) (t : z.re=0) (ff : ContinuousAt f z) (gg: ContinuousAt g z): f z=g z:= by
  obtain ⟨F,h,v⟩:= limit_chance q (slit_open a) u e
  have hx:= piers q p he h b v U d b'; have hy:=piers q p (neg_lt_zero.mpr he) h w v U d w'
  let P (i:ℝ) := (i:ℂ)+ z; let A:=veil 0 r a; let B:= veil (-r) 0 a
  have fh : ContinuousAt F z:= (h z zA).continuousAt; have hP: Tendsto P (𝓝 0) (𝓝 z):= by
    have h: Continuous P:= Complex.continuous_ofReal.add continuous_const; simpa [P] using h.tendsto 0
  have hu : ∀ᶠ i in 𝓝[>] (0:ℝ),P i∈ A:=by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds he)] with i hi g
    refine ⟨by simp [P,t]; exact hi,by simp [P,t]; exact g,?_⟩; change |(P i).im| < _; simpa [P] using (show |z.im|<a from zA)
  have hg : ∀ᶠ i in 𝓝[<] (0:ℝ),P i∈ B:=by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (neg_lt_zero.mpr he))] with i hi g
    refine ⟨by rw [show (P i).re=i from by simp [P,t]]; exact g,by simp [P,t]; exact hi,?_⟩; change |(P i).im| < _; simpa [P] using (show |z.im|<a from zA)
  let hp:= hP.mono_left (nhdsWithin_le_nhds (s:=Ioi 0)); let hn:= hP.mono_left (nhdsWithin_le_nhds (s:=Iio 0))
  exact (tendsto_nhds_unique (ff.tendsto.comp hp) ((fh.tendsto.comp hp).congr' (hu.mono fun _ k=>hx k))).trans (tendsto_nhds_unique (fh.tendsto.comp hn) ((gg.tendsto.comp hn).congr' (hg.mono fun _ k=>(hy k).symm)))
end Sail
end YM.ConePrice
