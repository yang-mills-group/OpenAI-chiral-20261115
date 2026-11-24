import GaugeFieldConstruction.ChernoRT
/-!
 # hatch ret. independence for any conserving distributions with on-cone support.
 # b=1 only near v=0, h_i choice ∂ on future & 0 behind on CAUSAL. No claim evaluating a discontinuous Heaviside. Local contour translated with v= T position MINUS field position (timelike opens both).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
abbrev DmoveRT (i:Axis) := ΦshiftΛ (basis i)
structure HatchRT (b:Test4) (h:Axis→Test4) : Prop where
 cb:HasCompactSupport ⇑b
 ch i:HasCompactSupport ⇑(h i)
 always: ⇑b =ᶠ[𝓝 0] (1:E4→ℂ)
 grow i v: v∉ Mink.spacelike → 0 < time v → ⇑(h i) =ᶠ[𝓝 v] ⇑(DmoveRT i b)
 fade i v: v∉ Mink.spacelike → time v ≤ 0 → ⇑(h i) =ᶠ[𝓝 v] 0
lemma zenTimeRt (v:E4)(e:v∉Mink.spacelike)(p:time v=0): v=0 :=by
 rw [Mink.lateral,p,abs_zero,not_lt] at e; have h:= norm_le_zero_iff.mp e
 exact Mink.divide.injective (by ext1; exact h; exact p) -- tune
lemma revForRt (B:Test4)(p:HasCompactSupport ⇑B)(t:⇑B=ᶠ[𝓝 0] 0):∃ U:Test4, HasCompactSupport ⇑U ∧
    (∀ x:E4, x∉ Mink.spacelike → time x≤0 → ⇑U=ᶠ[𝓝 x] 0) ∧ (∀ x:E4,x∉Mink.spacelike → 0<time x → ⇑U=ᶠ[𝓝 x] ⇑B):=by
 let W:= tsupport B ∩ ((Mink.spacelike)ᶜ ∩ time ⁻¹' Ici 0); have hW:IsCompact W:= p.inter_right (Mink.open_spacelike.isClosed_compl.inter (isClosed_Ici.preimage (by fun_prop)))
 have ht:{0} ∩ tsupport B=∅:=by
    apply Set.eq_empty_iff_forall_notMem.2; rintro _ ⟨hx,h⟩; exact (notMem_tsupport_iff_eventuallyEq.mpr t) ((mem_singleton_iff.mp hx) ▸ h)
 have hi(y: E4)(u:y∈W): 0<time y:=lt_of_le_of_ne (show 0≤time y from u.2.2) fun v=>notMem_empty y (ht ▸ ⟨Set.mem_singleton_iff.mpr (zenTimeRt y u.2.1 v.symm),u.1⟩ : y∈ (∅ : Set E4)) -- syntax
 obtain ⟨c,pc,hc⟩:∃ c:ℝ,0<c ∧ ∀ y∈W,c<time y:=by
    rcases W.eq_empty_or_nonempty with q|q; · exact ⟨1,one_pos, fun y py=> (by simp [q] at py)⟩
    obtain ⟨y,hy,h⟩:= hW.exists_isMinOn q (show Continuous time by fun_prop).continuousOn
    exact ⟨time y/2,half_pos (hi y hy),fun x u=> (half_lt_self (hi y hy)).trans_le (h u)⟩
 let H(y:E4):ℂ:= Real.smoothTransition (time y/c); have eH: ContDiff ℝ ∞ H:= by
    apply Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_); exact (show ContDiff ℝ ∞ fun x:E4=> time x / c by unfold time; fun_prop)
 let U : Test4:= (HasCompactSupport.toSchwartzMap (show HasCompactSupport (H * ⇑B) from p.mul_left) (eH.mul (B.smooth ⊤))) -- tune
 have he(x:E4): U x=H x * B x:=rfl
 refine ⟨U,p.mul_left,?_,?_⟩
 · intro x u q; rcases q.lt_or_eq with l|l
   · filter_upwards [((show Continuous time by fun_prop).tendsto x).eventually (gt_mem_nhds l)] with y hy
     rw [he,show H y=0 from by unfold H; rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (show time y≤0 from hy.le) pc.le)]; simp,zero_mul]; rfl
   rw [zenTimeRt x u l]; filter_upwards [t] with y hy; rw [he,show B y=0 from hy,mul_zero]; rfl
 intro y u q; by_cases g:y∈tsupport B
 · filter_upwards [((show Continuous time by fun_prop).tendsto y).eventually (lt_mem_nhds (hc y ⟨g,u,q.le⟩))] with x hx
   rw [he,show H x=1 from by unfold H; rw[Real.smoothTransition.one_of_one_le ((le_div_iff₀ pc).2 (by simpa using (show c≤time x from hx.le)))]; simp,one_mul]
 filter_upwards [notMem_tsupport_iff_eventuallyEq.1 g] with x hx; rw [he,show B x=0 from hx,mul_zero]
lemma hatchBreakRt (b c:Test4)(h g:Axis→Test4)(e:HatchRT b h)(s:HatchRT c g):∃ U:Test4,HasCompactSupport ⇑U ∧ ∀ i:Axis,tsupport (h i-g i - (DmoveRT i U)) ⊆ spacelike:=by
 let W:= b-c; obtain ⟨U,A,p,q⟩:= revForRt W (e.cb.sub s.cb) (by filter_upwards [e.always,s.always] with x a s; exact sub_eq_zero.mpr (a.trans s.symm))
 refine ⟨U,A,fun i x hx=>by
    by_contra r; apply (notMem_tsupport_iff_eventuallyEq.2 ?_ : x ∉ tsupport ⇑(h i-g i-DmoveRT i U)) hx
    by_cases k:0<time x
    · have a:= e.grow i x r k; have d:= s.grow i x r k
      filter_upwards [a,d,(q x r k).fderiv (𝕜:=ℝ)] with y ay dy t
      change (h i y-g i y)-(ΦshiftΛ _ U y)=0; rw [ay,dy,ΦsΛKnownL _ U,t,← ΦsΛKnownL]
      simp only [ΦshiftΛ, W, map_sub,sub_apply, DmoveRT, sub_self]
    have t:=p x r (not_lt.mp k); filter_upwards [e.fade i x r (not_lt.mp k), s.fade i x r (not_lt.mp k),t.fderiv (𝕜:=ℝ)] with y a w t
    change (h i y-g i y)-ΦshiftΛ _ U y=0; rw [a,w,ΦsΛKnownL,t]; simp⟩ -- tune
#print axioms HatchRT
end YM.NSF.Boundary
end
