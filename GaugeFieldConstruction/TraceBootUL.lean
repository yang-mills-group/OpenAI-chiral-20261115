import GaugeFieldConstruction.ArchicleYL
/-!
# Bootstrap on polystar charts
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Fathom
open Function Filter Analysis Points Set MeasureTheory Complex Asymptotics
open scoped Topology BigOperators ContDiff Classical
variable {n:ℕ}(a:Axis)(p:Points n)(b:Bulb)(k:Fin n)
abbrev CellsUL (b:Bulb)(k:Fin n):Set (Points n):= {x | BreatherMars b k x}
lemma ArchUL : IsOpen {x: Points n × ℝ | calmYL k a x.2 x.1 b}:=by
 let T (x:(Points n × ℝ) × ℝ):= ledgeYL k a x.1.2 x.1.1 x.2
 have H:Continuous T:= (continuous_fst.comp continuous_fst).add (continuous_snd.smul ((continuous_snd.comp continuous_fst).smul continuous_const))
 refine isOpen_iff_mem_nhds.mpr ?_; intro x h; change calmYL _ _ _ _ _ at h
 obtain ⟨U,V,u,_,e,f,g⟩ := generalized_tube_lemma (s:={x}) isCompact_singleton (t:=α0_YL) isCompact_Icc ((BreathingMars b k).preimage H) (by
   rintro ⟨z,i⟩ hz; obtain ⟨(rfl : z=x),j⟩:= hz; exact h i j)
 filter_upwards [u.mem_nhds (e (mem_singleton x))] with y v
 exact fun t w=> @g (y,t) ⟨v,f w⟩
variable (i:Axis)
lemma RouteUL (F: Points (n+1)→ℂ)(h: ContinuousOn F (conf (n+1))): ContinuousOn (fun x:Points n × ℝ=> ScrollOpYL a x.1 b i k x.2 F) {x| calmYL k a x.2 x.1 b}:=by
 haveI:= RΦayComYL b i; haveI:=RΦayCanYL b i; let Y:= Points n × ℝ; let Z:=ZonesYL b i
 let K(t:Y×Z):= rayMoveYL a t.1.1 k t.1.2 b i t.2
 have q: Continuous K:=by
   have p:Continuous (fun x:Y×Z=>x.2.2.val):= continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
   have hq: Continuous (fun x:Y×Z=>x.2.1.val):= continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
   exact alabasterYL.comp (p.prodMk ((continuous_fst.comp continuous_fst).add (hq.smul ((continuous_snd.comp continuous_fst).smul continuous_const))))
 let J:Set Y:= {x|calmYL k a x.2 x.1 b}
 have hp: ContinuousOn (F ∘ K) (J ×ˢ (univ:Set Z)):= h.comp q.continuousOn fun x u=> RΦayHappyYL a _ b i k _ u.1 _
 exact continuousOn_integral_of_compact_support isCompact_univ (((RΦayPriceYL b i).comp continuous_snd).continuousOn.mul hp) (fun _ x _ p=> (p (mem_univ _)).elim)
variable (h:BreatherMars b k p)
include h
lemma calmUL : calmYL k a 0 p b:=fun _ _=> by simpa [ledgeYL] using h
lemma ChargeUL (F:Points (n+1)→ℂ)(z:ContinuousOn F (conf _)): ScrollOpYL a p b i k 0 F=raysCostYL b i F p:=by
 rw [ScrollCubicYL a p b i k 0 (calmUL a p b k h) _ z, rayαYL (fun t=> raysCostYL b i F (ledgeYL k a 0 p t))]; simp [ledgeYL]
omit h
lemma TrackUL (L:Points n →L[ℝ] ℝ)(g:Points n→ℂ)(t: ContinuousAt g p): HasFDerivAt (fun x=> L (x-p) • g x) (ContinuousLinearMap.toSpanSingleton ℝ (g p) ∘L L) p:=by
 have hl:(fun x=> L (x-p)) =O[𝓝 p] fun x=> ‖x-p‖:= by
   rw [isBigO_norm_right]
   exact .of_bound _ (Eventually.of_forall fun x=>L.le_opNorm _)
 have hg:(fun x=> g x-g p) =o[𝓝 p] fun _=> (1:ℝ):=(isLittleO_one_iff _).mpr (by simpa using t.tendsto.sub (g:=fun _=>g p) tendsto_const_nhds)
 rw [hasFDerivAt_iff_isLittleO, ←isLittleO_norm_right]
 simpa only [smul_sub,sub_self, map_zero,zero_smul,sub_zero,ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul, mul_one] using (hl.smul_isLittleO hg)
#print axioms TrackUL
end YM.GaugeFieldConstruction.Fathom
end
