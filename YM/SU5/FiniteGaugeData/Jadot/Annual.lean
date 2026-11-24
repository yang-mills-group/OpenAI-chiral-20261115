import YM.SU5.FiniteGaugeData.Jadot.Solan
/-! # Credit supply beyond Volume. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade Dial Spire Paige Vault
open Avenue RouteM Spindle
open Rhythm Pilot PhaseM Steve VolumeRate
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Reduction.Hutch Fist Reduction.Verna Reduction.Dinar Reduction.Dijon Reduction.Rheims Reduction.Ziz Reduction.Dijon.Currency Reduction.Celeste Window.Presidio Window.Presidio.Menton Window.Presidio.Gato Thera Gall Girt
namespace Turnist
variable {n B L:Side} {ε t tH t' v H μ C C' cₛ c a' a M u x h d e α₁ m₀ α β b f e' v' cE X₀:ℝ}{r s k w j:ℕ} {o: Odd L.val} {U: Pricing k L o (Thread k)} (G:Grasp U B d)
structure Broom (w r j:ℕ)(a c C M C' p:ℝ)(s:Stage)(ε ν v v' x u e:ℝ): Prop where
 zone : j≤ w
 barrier :2 ≤ w
 so : r≤ w
 pieces : 0<v
 healthy:0<v'
 prime : 0< x
 opacity : 0< e
 extra : 2* Window.Brique.tailCost c C' r + e * C' ≤ x
 far :2 ≤ v'*Real.exp (a*w)
 macroRate : v'^2*C + (2*180)*v + BadgeKN ν v * owed x C' w ≤ ε/2 -- use WP15 shape approx budget
-- Eventually horizon constraints exterior.Stipend independent Ks etc
private lemma invest (x:ℝ)(he:0<ε):∃ v:ℝ,0 < v∧ v^2*x<ε:=by
 let K(v:ℝ):= v^2*x; let f:=𝓝[>] (0:ℝ); have p:Tendsto K f (𝓝 0):=by unfold f; apply @Tendsto.mono_left _ _ _ (𝓝 0) _ _ ?_ nhdsWithin_le_nhds; unfold K; simpa using (((show Tendsto (fun i:ℝ=> i) (𝓝 0) (𝓝 0) from tendsto_id).pow 2).mul_const x)
 exact ((p.eventually (eventually_lt_nhds he)).and (self_mem_nhdsWithin)).exists.imp fun i h=>⟨h.2,h.1⟩ -- tune
lemma electgraph(R₀:ℕ) (u:0<c)(z:0≤C)(hy:0<C')(b:ℝ)(e':ℝ)(ha:0<a)(x:0<M)(ν:ℝ)(v₀:0<ε)(X:Stage)(U:ℕ→ℝ)(wP:∀w,0<U w): ∃ w r:ℕ, R₀≤ w ∧ ∃ v v' x f:ℝ, M*f≤ U w ∧ Broom w r j a c C M C' b X ε ν v v' x e' f:=by
 let q:= ε/12; let m:ℝ:= 2*180; let v:= q/m; have hq:0<q:=div_pos v₀ (by norm_num); have hm:0 < m:= mul_pos two_pos (by norm_num)
 have hv:0<v:=by unfold v; positivity
 obtain ⟨v',hv',pF⟩:= invest C hq; let X':= BadgeKN ν v; have hp:0≤X':=by unfold X' BadgeKN; positivity
 let L:ℝ:= Fintype.card (Ember.coneA SU.Slot)
 obtain ⟨x',ht,hu⟩:= invest (X'*L) hq
 have he: Tendsto (fun w:ℕ=> (diamC/(w:ℝ)^2)) atTop (𝓝 0):= (tendsto_const_nhds (x:=diamC)).div_atTop ((tendsto_pow_atTop (by decide: (2:ℕ)≠0)).comp tendsto_natCast_atTop_atTop)
 have hh:Tendsto (fun w:ℕ=> X'*owed x' C' w) atTop (𝓝 (x'^2* (X'*L))):=by
    have h:= (((((he.const_mul ((C'+C')^2)).const_add (x'^2)).const_mul L)).const_mul X'); simp only [mul_zero,add_zero] at h; rw [show x'^2*(X'*L)=X'*(L*x'^2) by ring]; exact h -- tune order
 let K:= tailCloud c C' u; have hx:Tendsto (fun r:ℕ=> 2* tailCost c C' r) atTop (𝓝 0):=by simpa only [mul_zero] using K.const_mul 2
 obtain ⟨r,p⟩:= (hx.eventually (ge_mem_nhds (half_pos ht))).exists
 have hy':Tendsto (fun w:ℕ => v'*Real.exp (a*(w:ℝ))) atTop atTop:= (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha)).const_mul_atTop hv'
 obtain ⟨w,⟨zW,z',zT,y⟩,hqg,f⟩:= (( (eventually_ge_atTop R₀).and ((eventually_ge_atTop 2).and ((eventually_ge_atTop j).and (eventually_ge_atTop r)))).and ((hh.eventually (ge_mem_nhds hu)).and (hy'.eventually_ge_atTop 2))).exists; let V:= min (x'/2/C') (U w/M); have hW:0<V:=lt_min (by positivity) (div_pos (wP w) x); have hH:M*V ≤ U w:=by rw [mul_comm]; exact (le_div_iff₀ x).mp (min_le_right ..)
 have hu': V*C' ≤ x'/2:= (le_div_iff₀ hy).mp (min_le_left ..); refine ⟨w,r,zW,v,v',x',V,hH,zT,z',y,hv,hv',ht,hW,by linarith only [hu',p],f,?_⟩; have hm:m*v=q:=by unfold v; field_simp
 unfold q at *; linarith only [v₀,hqg,pF,hm]
end Turnist
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
