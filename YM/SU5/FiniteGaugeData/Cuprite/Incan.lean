import YM.SU5.FiniteGaugeData.Cuprite.Alchemy
import YM.SU5.FiniteGaugeData.Cuprite.Helen
import YM.SU5.FiniteGaugeData.Galope.Folios
/-! # Pointwise extensivity on future resolution, payments so far. Retain ink term and EVERYTHING dimensioned. -/
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
variable {n B L:Side} {ε t p b v H μ C C' c a a' M u x h d e α₁ m α β e' v':ℝ}{r s k w j:ℕ} {o: Odd L.val} {U: Pricing k L o (Thread k)} (G:Grasp U B d)
namespace Vapors
variable {T:GramM (mid n B)} (Y:Loom (mid n B))(X:Orbit (mid n B))(K:Roof (mid n B) p d j Y) {g:Mosquito (mid n B)} {W:Op (Single (mid n B))} -- p bind.
local notation "Θ" => tickA (mid n B)
local notation "Yz"=> (Y X)
local notation "R"=> (spar k T.J.M (1:Pane (mid n B)))
-- profitL = chiral true directional tangent at field one, already transformed the Mark kernel by the ACTUAL purchased same gauge. h-turn-angle.
def puff(k:ℕ){n:Side}(T:GramM n) (g:Mosquito n)(W:Op (Single n)):=curlR (tickA n) (spar k T.J.M (1:Pane n)) (twist (tradew n g) W)
include K
-- expose explicit log. W amount
abbrev factorC (μ r C:ℝ):= (μ+r^2)*C/2
lemma voucher(hQ:G.roundZ≤(mid n B).val)(I:Ledger h m m a C T)(_ℓ:1≤ k)(lx:Invites k H (mid n B))(H0:2*(45*Real.sqrt H)+2 ≤ h)
 (v₀:0< v)(f:0<a)(℘:0<μ)(d':μ ≤ 1)(w0:t=T.p.threshold)(he:t≤p)(hv:‖W-1‖^2 ≤ μ/2)(hy:‖W-1‖≤ b)
 (ch:0<v')(cc:0≤C)(w':w≤(More (mid n B)).val)(hi:T.p.threshold≤v')(z:2≤v'*Real.exp (a*w))
 (hx:0≤ d)(hn:0≤ C')(E:Casing (mid n B) d (blend k T.J false) c C' M)(F:Casing (mid n B) d (spar k T.J.M) c C' M) (ℵ:CoversU X Y w t x (M* α₁) g)(hg:r≤w)(o:2*tailCost c C' r+ α₁ * C'≤ ε):
 ‖inner ℂ (mateK _) (acts (quant W) (Graph.beam T G Y X))‖ ≤ Real.exp (
 Parcel.Tanin.photo_ψ k (mid n B) T.J.M + puff k T g W +
 factorC μ b H*((mid n B).val:ℝ)^4 +
 (v'^2*C*((mid n B).val:ℝ)^4+(m+m+m)*sites (mid n B) + 2*v*(Fintype.card (Single (mid n B)):ℝ) + Mix μ (C'+1) v * Pilot.Ticket X t ε C' w + accrues w j C * once X t)) :=by
 obtain ⟨A,Q,S,uP,hvS,Qe⟩:= lx.issued T.J.M g⁻¹ ((G.broadness (mid n B) hQ T.J.M).projection _ (guard0 hx)); -- v shadows v; tune!
 let N':=mid n B; let P:=spar k T.J.M (Y X); let D:=Graph.actF k T Y X; let L:=blend k T.J false; have hZ:Guard (Y X) d:= K.paid X; have hT:IsStarProjection P:= (G.broadness _ hQ T.J.M).projection _ hZ; have hp: (1+D)*P=L (Y X):= blend_motto _ hT
 have hl:L 1= R:=by unfold L; rw [Brique.jewel]; unfold spar; rw [profile_trivial]
 let F':= tollX g R; let α:= Pilot.Ticket X t ε C' w; have hz: Reduction.Drama.Pack μ (C'+1) α Θ P F' (1+D) W:= ⟨hT,plus_P _, A,℘,d',hv,by linarith only [hn],Q, by rw [hp,show F'=tollX g (L 1) from hl ▸ rfl]; exact egress Y X ℵ E hZ hx hg o, egress Y X ℵ F hZ hx hg o, by rw [hp]; exact (ambient_value E _ hZ).trans (le_add_of_nonneg_right zero_le_one)⟩
 -- keep τ Pigment.
 have hg:= exactory X K he I.field.2 cc f ch (hi.trans' w0.le) w' z
 have he': pLine Θ F' μ b ≤ Parcel.Tanin.photo_ψ k N' T.J.M +factorC μ b H*(N'.val:ℝ)^4:= by -- explicit inequality
    unfold pLine horizonM; let H':= spring Θ (Θ*F'); change rueD H'/2= _ at hvS; rw [show spring Θ _=_ from (rfl: spring Θ (Θ*F')=H'),hvS]; apply add_le_add le_rfl; unfold factorC; change TrR (spring Θ (Θ*F'))⁻¹ ≤ H *(N'.val:ℝ)^4 at S; linarith only [mul_le_mul_of_nonneg_left S (show 0≤μ+b^2 from by positivity)]
 apply (whole (v:=_) Y X I hz (sea_g hQ _ hZ _) uP hy (by positivity) v₀ H0 hg)|>.trans; apply Real.exp_le_exp.mpr
 have he: puff k T g W=curlR Θ F' W:=by unfold puff; refine Eq.trans ?_ (Qe W).symm; rw [Mono_tradew,star_star]
 rw [he]; linarith only [he']
omit K
local notation "L'"=> sites (mid n B)
section
-- fee numerator loose rounding global
lemma kmix (u:0≤μ)(d:0≤M)(w:0≤ v):0≤Mix μ M v:=by unfold Mix XrayPay RedAccount; positivity
lemma kmal (r':ℝ)(u:0≤μ)(d:0≤C):0≤factorC μ r' C:=by unfold factorC; positivity -- r' implicit binder
lemma spoors(n:Side): Fintype.card (Site (More n))=(More n).val^4:=site_card _
lemma matrixp(n:Side): (n.val:ℝ)^4 ≤ sites n:=by
 unfold sites; gcongr; exact Nat.le_mul_of_pos_right n.val (by decide:0<(2:ℕ))
-- effective epoch request purely calibrated by income params. θ sign compar. before phys cal. room for any tilt
structure BoostM (w r j:ℕ)(a c C M C' p:ℝ)(s:Stage)(ε μ v v' x u e:ℝ): Prop where
 zone : j≤ w
 barrier :2 ≤ w
 so : r≤ w
 pieces : 0<v
 healthy:0<v'
 prime : 0< x
 opacity : 0< e
 extra : 2* Window.Brique.tailCost c C' r + e * C' ≤ x
 far :2 ≤ v'*Real.exp (a*w)
 macroRate : v'^2*C + (2*180)*v + Mix μ (C'+1) v * owed x C' w ≤ ε/2 -- use WP15 shape approx budget
-- Eventually horizon constraints exterior.Stipend independent Ks etc
private lemma invest (x:ℝ)(he:0<ε):∃ v:ℝ,0 < v∧ v^2*x<ε:=by
 let K(v:ℝ):= v^2*x; let f:=𝓝[>] (0:ℝ); have p:Tendsto K f (𝓝 0):=by unfold f; apply @Tendsto.mono_left _ _ _ (𝓝 0) _ _ ?_ nhdsWithin_le_nhds; unfold K; simpa using (((show Tendsto (fun i:ℝ=> i) (𝓝 0) (𝓝 0) from tendsto_id).pow 2).mul_const x)
 exact ((p.eventually (eventually_lt_nhds he)).and (self_mem_nhdsWithin)).exists.imp fun i h=>⟨h.2,h.1⟩ -- tune
lemma election_chart(R₀:ℕ) (u:0<c)(z:0≤C)(hy:0<C')(b:ℝ)(e':ℝ)(ha:0<a)(x:0<M)(℘:0<μ)(v₀:0<ε)(X:Stage)(U:ℕ→ℝ)(wP:∀w,0<U w): ∃ w r:ℕ, R₀≤ w ∧ ∃ v v' x f:ℝ, M*f≤ U w ∧ BoostM w r j a c C M C' b X ε μ v v' x e' f:=by
 let q:= ε/12; let m:ℝ:= 2*180; let v:= q/m; have hq:0<q:=div_pos v₀ (by norm_num); have hm:0 < m:= mul_pos two_pos (by norm_num)
 have hv:0<v:=by unfold v; positivity
 obtain ⟨v',hv',pF⟩:= invest C hq; let X':= Mix μ (C'+1) v; have hp:0≤X':=kmix ℘.le (add_nonneg hy.le zero_le_one) hv.le
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
end
end Vapors
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
