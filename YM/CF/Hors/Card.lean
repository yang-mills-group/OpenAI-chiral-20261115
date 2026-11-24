import YM.CF.Char.Casier
import YM.CF.Rel.It
/-! Root-dues (no log-volume loss) for weighted Taylor matching. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Hors
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Jet Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push
open Push.Uniform (curve Slope meetVar Positions upperCol lowerCol block meet_derivative bolt)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
section norm
variable {ι τ:Type} [Fintype ι] [Fintype τ]{f g:Fish (ι⊕τ)→B}
def arrow(u:E→ B)(e:E)(x:E) : B:= fderiv ℝ u x e
def glance(f:Fish ι→B)(i:ι):=arrow f (Uniform.bolt i)
lemma bolt_g{p:ι⊕τ→Site c}{f:Fish (ι⊕τ)→ℝ}{x: Fish (ι⊕τ)}(h:ContDiffAt ℝ ω f x)(hm:Uniform.Multiplicity p l)(hp:Uniform.Scatter p s (n+1) f x A)(hs:0<s)(ht:0 ≤ A) : -- Wax tied! drop
 ∀ i, Allows n (glance f i) x (A*(1+l*Uniform.countCost s)^n):=by
 intro i
 let t:ℝ:=l*Uniform.countCost s; let z:=Uniform.bolt i; have he:glance f i= (ContinuousLinearMap.apply ℝ ℝ z) ∘ (fderiv ℝ f):=rfl
 have hh : ContDiffAt ℝ ω (fderiv ℝ f) x:= h.fderiv_right (by simp)
 refine ⟨he ▸ ((ContinuousLinearMap.apply ℝ ℝ z).contDiff.contDiffAt.comp x hh).of_le le_top,fun j hj=>?_⟩
 refine (stall (iteratedFDeriv ℝ j (glance f i) x) (p i) p ?_ hm ht hs).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_add_of_nonneg_right (show 0  ≤  t from mul_nonneg (by positivity) (Uniform.count_pos hs).le)) hj) ht)
 intro q
 let w := Fin.snoc (α:=fun _ : Fin (j+1)=>ι⊕τ) q i
 rw [he,ContinuousLinearMap.iteratedFDeriv_comp_left _ hh le_top]
 have hx := hp (j+1) (Nat.add_le_add_right hj 1) w (Fin.last j)
 have hl : Uniform.spanSites p (p (w (Fin.last j))) w =Uniform.spanSites p (p i) q:=by unfold Uniform.spanSites w; simp [Fin.sum_univ_castSucc]
 rw [hl] at hx; refine le_trans ?_ hx; unfold Uniform.entry
 rw [iteratedFDeriv_succ_apply_right]
 have ha: Fin.init (α:=fun _=> Fish (ι⊕τ)) (fun i=>bolt (w i))=fun i=>bolt (q i):=by ext; simp [Fin.init,w]
 rw [ha,show w (Fin.last j)=i from Fin.snoc_last ..]; exact le_rfl
set_option maxHeartbeats 700000 in
lemma varying {m z:Fish ι→Fish τ}[FiniteDimensional ℝ B] {x:Fish ι}
 (h:∀ y, ‖y‖<r→ Allows (n+1) f y C)(ht:‖x‖<1)
 (hm:∀ y:Fish ι, ‖y‖<1 → Allows n m y (A * s)  ∧ Allows n z y (A * s)) (hs:0 ≤ s)(ha:1 ≤ A)(hv:(3 * A * s) < r)(he:(3 * A * s)  ≤  1)
 (hp: Allows n (fun a=> m a-z a) x Q): Allows n (fun a=> f (meetVar (s•a) (m a))- f (meetVar (s•a) (z a))) x (2^n * composeCost n C 1 * Q):=by
 let D:=fun y=> m y-z y; let L:=lowerCol (ι:=ι) (τ:=τ); let Φ(a:Fish ι×ℝ):=meetVar (s•a.1) (z a.1 + a.2 • D a.1)
 let U(y:Fish ι×ℝ):= fderiv ℝ f (Φ y) (L (D y.1)); let ξ:= U
 have hb y (hy:‖y‖<1) u (hu:u∈interval): Allows n (fun a=> Φ (a,u)) y ((3 * A * s)):= turn_safe (hm _ hy).1 (hm _ hy).2 hs ha hy u hu
 have hF y (hy:‖y‖<1) u (hu:u∈interval):Allows (n+1) f (Φ (y,u)) C:=h _ ((hb y hy _ hu).value.trans_lt hv)
 have hh y (hy: ‖y‖<1):Arc ξ n y:=by
    intro u hu; have ht : ContDiffAt ℝ (n:ℕ∞ω) D y:= (hm _ hy).1.smooth.sub (hm _ hy).2.smooth
    have h1 : Arc Φ n y:= fun u _=> (Uniform.partSpace ..).symm.contDiff.contDiffAt.comp (f:=fun q:Fish ι×ℝ=>(s • q.1,z q.1+q.2 • D q.1)) _ ((contDiffAt_fst.const_smul _).prodMk (((hm y hy).2.smooth.comp _ contDiffAt_fst).add (contDiffAt_snd.smul (ht.comp (y,u) contDiffAt_fst))))
    exact (((hF _ hy _ hu).slide.smooth.comp _ (h1 u hu)).clm_apply ((L.contDiff.contDiffAt.comp _ (ht.comp (y,u) contDiffAt_fst))))
 refine (spirit (hh _ ht) (fun i hi=> (appliance (f:=L ∘ D) ((hF x ht _ hi).slide.comp (f:=fun y=>Φ (y,i)) ((hb _ ht _ hi).mono he)) ((hp.linear L lower_n).mono (one_mul _).le)))).germ ?_
 filter_upwards [Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr ht)] with i (hi: i∈ball (0:Fish ι) 1)
 have hi':‖i‖<1:= mem_ball_zero_iff.mp hi; let V(t:ℝ):= Φ (i,t)
 have hd t(ht:t∈interval) : HasDerivAt (f ∘ V) (ξ (i,t)) t:=by
    refine ((hF _ hi' t ht).smooth.differentiableAt (by norm_cast)).hasFDerivAt.comp_hasDerivAt t ?_
    let K(q:ℝ):= z i+q•D i
    have h:HasDerivAt K (D i) t:=by unfold K; simpa using (((hasDerivAt_id' t).smul_const (D i)).const_add (z i))
    exact (meet_derivative (s•i) _).comp_hasDerivAt t h
 rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=f ∘ V) (fun x hx=>hd x (by simpa only [uIcc_of_le zero_le_one] using hx)) ((hh _ hi').slice.intervalIntegrable_of_Icc zero_le_one)]
 simp [Φ,V,D]
end norm
end YM.CF.Hors
