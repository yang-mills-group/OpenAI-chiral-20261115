import YM.CF.Newt.High
set_option autoImplicit false
noncomputable section
namespace YM.CF.Newt
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.RelativeLogdet.Ink PhysicalNext.JointLoad.Heir Jet Push AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open Push.Uniform (Before Primary curve Slope meetVar Positions upperCol lowerCol block meet_derivative entry)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {C D v K d N X U s r a e:ℝ}{n l:ℕ}
open Next.SectorChange (panels shots)
open Next.SectorChange.Rows (gram)
variable {G:Gauge}{P:Patch}{c f:Side}{T:StepData c f}{R:Tube G T}{T':Teller G}
abbrev sol(T:RG.StepData c f)(U:Tube G T)(t:T.Choices)(x:ℝ) (F:Forest T.ratio)(i:ℕ):=streak (costP F t U.high (grainA U.up (Stores.till x))) (gall U x t F) 1 (budX U x F t) i
lemma stripG {ι τ:Type} [Fintype ι] [Fintype τ] (f:Fish (ι⊕τ)→ℝ)(m:Fish ι→Fish τ)(U:Fish ι→Fish τ→L[ℝ] Fish τ)(s:ℝ)(j:ℕ): (fun y=> streak f U 1 m j (s•y))=streak f (fun y=> U (s•y)) s (fun y=>m (s•y)) j:=by
 induction j with
 | zero=>simp [streak]
 | succ i ih=> ext1 y; simp only [streak,nudge]; rw [← ih]; dsimp only; rw [one_smul]
lemma scales_m {s:ℝ} (x:ℝ)(F:Forest T.ratio)(i:ℕ)(t:T.Choices): (fun y=>sol T R t x F i (s • y))= streak (costP F t R.high (grainA R.up (Stores.till x))) (fun y=>gall R x t F (s•y)) s (fun z=>budX R x F t (s • z)) i:= stripG _ _ _ _ _
lemma yields (K:Teller G)(n i:ℕ)(hm:2≤n)(P:Patch)(p:P.Branches K.bind G)(W:Before G K.top.width K.top.paths K.j K.bind (n+1+1)) :
 ∃ a t v C ε:ℝ,0<a∧0<t∧0<v∧0<C∧0<ε ∧∀ᶠ x:ℝ in atTop, ∀ {c f:Side}(T:StepData c f)(U:Tube G T)(F:Forest T.ratio), Cert P K T U x → (∃ z, Critical F U.high U.up z ∧ Guessed F (Bloch.installed T.ratio U.R.A0) z) →
 ∃ z,W.Service F U.high U.up z ∧ jewel T U F z (W.tables K.top.clip P) (n+1+1) n a v C ∧ Guessed F (Bloch.installed T.ratio U.R.A0) z ∧ ∀ (k:T.Choices),∀ s,0<s →temp x≤s →s≤ε→ Folded (fun y=> sol T U k x F i (s • y)) (fun y=> Uniform.station z (s•y)) n (t*s^(i+2)):=by
 have hn:1≤n:=by omega
 obtain ⟨b,a,X,t,hb,ha,hX,ht,h⟩:= rentsD K p n (i+2) hn W; obtain ⟨u,C,d,hu,hc,hd,H⟩:= zenith P K (n+1+1) n (by omega) W; obtain ⟨r,Y,hr,hY,H'⟩:= month K p n hn; let A:= Y+C
 let L:=max C 1; have hA:0<A:=add_pos hY hc; have hL:1≤L:=le_max_right ..; have h2:2 ≤ i+2:= by omega
 obtain ⟨B,U,hB,hU,H0⟩:= purchase n (i+2) hn h2 ha hX (show 0<2*A by positivity) hL hb i le_rfl
 let D:= min U (min t (min r (min 1 (u/2))))
 refine ⟨u,B,d,C,D,hu,hB,hd,hc,lt_min hU (lt_min ht (lt_min hr (lt_min zero_lt_one (half_pos hu)))),?_⟩
 filter_upwards [h,H'] with x he hp
 intro c f S T F h hq; obtain ⟨g,hg,hG⟩:=H S T x F h; obtain ⟨z,hz,hZ⟩:=hq
 have hl := hg.is_extension hz
 have hv:Guessed F (Bloch.installed S.ratio T.R.A0) g:=by
    intro v; exact (hZ v).congr_of_eventuallyEq ((show Tendsto (fun r:ℝ=> r • v) (𝓝 0) (𝓝 0) by simpa using (show Continuous fun r:ℝ=> r • v from by fun_prop).tendsto 0).eventually hl.symm)
 have Hg : Uniform.station g 0=0:=by simp [Uniform.station,hg.critical.1]
 refine ⟨g,hg,hG,hv,?_⟩
 intro k s hs ht' hB'; have H₁:=hp S T h F k; obtain ⟨hx,H₂⟩:=he S T h F k; let Z:=budX T x F k; let G':=Uniform.station g; have he:‖fderiv ℝ Z 0-fderiv ℝ G' 0‖ ≤ Y*temp x:=by unfold G'; rw [recover F x k g hg.critical.2.1 hv]; exact H₁.miss
 have ht'':= hB'.trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))) -- likely s<=r
 have hS:=hB'.trans ((min_le_right ..).trans (min_le_left ..))
 let t:= min r (u/2); have hmin : s≤t:= le_min ht'' (hB'.trans ((min_le_right ..).trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..)))))
 have hj:s≤1:=hB'.trans ((min_le_right ..).trans ((min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))))
 have hΓ:=H₂ s hs ht' hS
 rw [scales_m]; apply H0 _ _ _ _ _ _ hs (hB'.trans (min_le_left ..)) hΓ
 · intro y hy; have hw:= (near_s (f:=Uniform.station g) hs.le hj hn (hmin.trans_lt ((min_le_right ..).trans_lt (half_lt_self hu))) (fun z hz=> (hG z hz.le).2.1) hy.le); rw [Hg] at hw; simp_rw [sub_zero] at hw
   have ht : ‖s•y‖ ≤ s := by rw [norm_smul,Real.norm_of_nonneg hs.le]; exact mul_le_of_le_one_right hs.le hy.le
   exact ⟨hw.mono (mul_le_mul_of_nonneg_right (le_max_left ..) hs.le),(hG _ (ht.trans (hmin.trans ((min_le_right ..).trans (half_lt_self hu).le)))).2.2.1 k⟩
 have h0:‖(0:Mast G c)‖ ≤ t:=by rw [norm_zero]; exact hs.le.trans hmin
 let J:=fun x=> Z x-G' x; have HJ : Portrait J (0:Mast G c→L[ℝ] Fish (Key F G)) n s t A:=by
    refine ⟨fun x hw=>?_,?_,?_⟩
    · have hℓ:= H₁.uniform x (hw.trans (min_le_left ..)); have ht: ‖x‖ ≤ u:=hw.trans ((min_le_right ..).trans (half_lt_self hu).le)
      have hh:= subtract_p (show Allows n Z x Y from ⟨hℓ.1,hℓ.2⟩) (hG x ht).2.1; exact ⟨hh.1,hh.2⟩
    · unfold J G'; rw [Hg,sub_zero]; exact H₁.home
    · rw [sub_zero,show J=Z-G' from rfl,fderiv_sub ((H₁.uniform 0 (h0.trans (min_le_left ..))).smooth.differentiableAt (by exact_mod_cast (show n ≠0 by omega))) (((hG 0 (by simpa using hu.le)).1).differentiableAt (by simp))]
      exact he.trans ((mul_le_mul_of_nonneg_left ht' hY.le).trans (mul_le_mul_of_nonneg_right (show Y ≤ A from le_add_of_nonneg_right hc.le) hs.le))
 exact ⟨fun y hy=> portrait hm HJ hs.le hmin hj hy.le⟩
end YM.CF.Newt
