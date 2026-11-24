import YM.Heat.Duration
/-!
# Identify R momenta instead of dummy spectator OS.E4
When carrying reconstructed time for our experiment; NO use of artificial spacetime ground match.
Test that x outside strict-time ground iff diagonal actually places mass on strictly positive energies.
Need atom and strict projection identities not just `Semigroup.bright`. Assumes arbitrary Semigroup here so later
whether monoAxis or true upgraded Lorentz, can use these TIME-ONLY conclusions.
-/
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.Spectral.Alps
open OS OS.Semigroup Function Set Filter MeasureTheory Measure Spectral Complex Analysis Boundary Probe
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "U"=> S.edge
local notation "E"=> S.E
def spectralP : PVM H ℝ:= S.ℚmeasure.route (fun t:E4=>t a) (by fun_prop)
local notation "P"=> spectralP S
local notation "μ" x:max => (P).diagonal x
variable (x y:H)
def evolve : Spectral.Orbit H ℝ:= ⟨S.edge,S.birth,S.send,S.life,S.cont⟩
lemma mature : ∀ᵐ t∂(μ x),0≤ (t:ℝ):=by
 have h:Measurable (fun i:E4=>i a):=by fun_prop
 exact (ae_map_iff h.aemeasurable (measurableSet_le measurable_const measurable_id)).2 (S.bright x)
-- optional support vs ae
lemma spectral (t:ℂ)(p: 0≤ t.im) : inner ℂ x (U t.re (E t.im.toNNReal x))=(∫ u:ℝ, Complex.exp ((u:ℂ)*t*I) ∂(μ x)):=by
 let e(u:E4):ℝ:=u a; have he:Measurable e:= by unfold e; fun_prop
 unfold spectralP PVM.route; rw [integral_map he.aemeasurable (f:=fun r:ℝ=>Complex.exp ((r:ℂ)* t*Complex.I)) ((by fun_prop : Continuous (fun r:ℝ=>Complex.exp ((r:ℂ)*t*Complex.I))).aestronglyMeasurable)];
 have ht:=S.heat 0 x (z:=t) (show t∈_ from p); simpa [OS.Semigroup.J,OS.Semigroup.ray,S.unit.origin,Probe.plane,e] using ht
lemma harmonizes(t:ℝ): ∫ u:ℝ,Complex.exp ((u:ℂ)*(t:ℂ)*I) ∂(μ x)=inner ℂ x (U t x):= by simpa [S.eZero] using (spectral S x (t:ℂ) (by simp)).symm
lemma moment : (evolve S).Spectrum (P):= by
 intro x t; rw [charFun_apply]; change _=inner ℂ x (U t x); simpa [mul_comm,I_sq] using harmonizes S x t -- orientation sign real_inner
lemma snow (t:ℝ≥0): inner ℂ x (E t x) = ∫ u:ℝ, (Real.exp (-(t:ℝ)*u):ℂ)∂(μ x):=by
 let c:= (((t:ℝ):ℂ)*I); have hi: c.im=t:=by unfold c; simp; -- syntax implicit t cast?
 have h: c.im ≥ 0:= by rw [hi]; exact t.property
 have he : U c.re (E c.im.toNNReal x)= E t x:=by rw [hi, show c.re=0 from (by unfold c; simp), S.birth]; simp
 rw [←he,spectral S x c h]; refine integral_congr_ae (ae_of_all _ (fun u=>?_)); dsimp only; rw [Complex.ofReal_exp]; apply congrArg Complex.exp; unfold c; push_cast; ring_nf; simp [I_sq] -- tune
local notation "π₀"=> S.orth
private lemma zeroLap(μ':Measure ℝ)[IsFiniteMeasure μ'](h:∀ᵐ u∂μ',0≤u): Tendsto (fun t:ℕ=> ∫u, (Real.exp (-(t:ℝ)*u):ℂ)∂μ') atTop (𝓝 (↑(μ'.real {0}): ℂ)):=by
 let g(t:ℝ):ℂ:= ({0}:Set ℝ).indicator (fun _=>1) t
 rw [show (↑(μ'.real {0}):ℂ)= _ from (show (↑(μ'.real {0}):ℂ)=∫ t,g t ∂μ' from ?_)]
 · refine tendsto_integral_of_dominated_convergence (bound := fun _=> 1) (fun n=>?_) (integrable_const (1:ℝ)) ?_ ?_
   · apply Continuous.aestronglyMeasurable; fun_prop
   · intro n; refine h.mono (fun x t=>?_); rw [Complex.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) t)
   filter_upwards [h] with u p; obtain p|rfl:= lt_or_eq_of_le p; · unfold g; rw [indicator_of_notMem (show u∉({0}:Set ℝ) from p.ne') _]; have hp : Tendsto (fun i:ℕ=> -(i:ℝ)*u) atTop atBot:=(tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop).atBot_mul_const p; let ht:= Real.tendsto_exp_atBot.comp hp; exact (show ofReal 0=0 from rfl) ▸ (Complex.continuous_ofReal.continuousAt.tendsto.comp ht)
   simp [g]
 unfold g; rw [integral_indicator (measurableSet_singleton _), setIntegral_const]; simp

lemma atom_px : (P).region {0} = S.orth:= by
 let Q:=(P).region {0}; let G:=π₀
 have h(x:H): inner ℂ x (G x) = (↑((μ x).real {0}):ℂ):=by
    have k:= tendsto_const_nhds.inner (𝕜:=ℂ) (x:=x) ((S.emerges x).comp (show Tendsto (fun i:ℕ=>(i:ℝ≥0)) atTop atTop from tendsto_natCast_atTop_atTop)) -- signature
    refine tendsto_nhds_unique (f:=fun t:ℕ=> ∫u, (Real.exp (-(t:ℝ)*u):ℂ)∂(μ x)) ?_ (zeroLap _ (mature S x)); simpa only [snow,NNReal.coe_natCast,Function.comp_apply] using k
 refine ContinuousLinearMap.ext (fun i=>LinearMap.congr_fun (show Q.toLinearMap=G.toLinearMap from ?_) i); apply (ext_inner_map ..).1; intro v; apply (starRingEnd ℂ).injective; rw [inner_conj_symm, inner_conj_symm]; change inner ℂ v (Q v)=inner ℂ v (G v); exact ((P).at_pair (measurableSet_singleton _) v).symm.trans (h v).symm
-- spectrum strictly positive indicated by support with u>0. get $μ$ complement ℝ dif. Ɵ measures & projection exactly $Ioi0$. norm split. 
lemma full_size : (μ x).real Set.univ= ‖x‖^2:= by rw [(P).same MeasurableSet.univ,(P).all]; rfl
lemma bright_null : (μ x) (Set.Iio 0)=0:= by
 have h:=mature S x; rw [ae_iff] at h; simpa [Set.Iio] using h
lemma bright_region: (P).region (Set.Iio 0)=0:= by ext1 x; exact ((P).null_pair measurableSet_Iio x).mp (bright_null S x)
lemma realU : (μ x).real (Set.Ioi 0)= ‖x‖^2 - ‖π₀ x‖^2:= by
 have hz: (μ x).real (Set.Iio 0)=0:= by simp [Measure.real,bright_null S x]
 have ha:(μ x).real {0} = ‖π₀ x‖^2:=by rw [(P).same (measurableSet_singleton _), atom_px]
 have H := measureReal_add_measureReal_compl («μ»:= μ x) (s:=Set.Iic 0) measurableSet_Iic
 rw [compl_Iic, full_size] at H
 have he: (μ x).real (Set.Iic 0)= ‖π₀ x‖^2:= by rw [←ha, show Set.Iic (0:ℝ)= _ from Set.Iio_union_right.symm, measureReal_union (by simp) (measurableSet_singleton _), hz,zero_add] -- inspect
 rw [he] at H; exact eq_sub_of_add_eq' H  -- maybe need comm

local notation "W"=> Set.Ioi (0:ℝ)
lemma spotlight : (P).region (Set.Ioi 0) = (1:H.Op) - π₀:=by
 let Q:=(P).region W; let R:=(1:H.Op)-π₀
 refine ContinuousLinearMap.ext (fun i=>LinearMap.congr_fun (show Q.toLinearMap=R.toLinearMap from ?_) i); apply (ext_inner_map ..).1; intro u; apply (starRingEnd ℂ).injective; rw [inner_conj_symm,inner_conj_symm];
 change inner ℂ u (Q u)=inner ℂ u (u-π₀ u); rw [inner_sub_right, inner_self_eq_norm_sq_to_K,show inner ℂ u (Q u)= _ from ((P).at_pair measurableSet_Ioi u).symm,← atom_px,←(P).at_pair (measurableSet_singleton _) u,realU, (P).same (measurableSet_singleton _),atom_px]; push_cast; rfl -- extra
abbrev aboveH := (spectralP S).region (Set.Ioi 0)
local notation "G"=> aboveH S
lemma lively : x ∈ S.ground ↔ G x=0:=by
 rw [show G=_ from spotlight S]; change _ ↔ x-π₀ x=0; rw [sub_eq_zero]; exact S.ground.starProjection_eq_self_iff.symm.trans eq_comm -- namespace order
lemma margin : x∉ S.ground ↔ 0< (μ x).real (Set.Ioi 0):=by
 rw [(P).same measurableSet_Ioi,lively]; exact ⟨fun i=> pow_pos (norm_pos_iff.mpr i) _, fun h i=>ne_of_gt h (by rw [show (P).region W x=0 from i,norm_zero]; simp)⟩
lemma centered (t:ℝ≥0) : E t (π₀ x)=π₀ x:= (S.fixed _).mp ((Submodule.starProjection_apply_mem ..)) _
lemma engaged : S.orth.adjoint = S.orth:= by rw [← atom_px]; exact (P).real (measurableSet_singleton _)
lemma powerS (t:ℝ≥0) : π₀ (E t x)=π₀ x:= by
 apply ext_inner_left ℂ; intro y; calc
    _=inner ℂ (π₀ y) (E t x):= by rw [← ContinuousLinearMap.adjoint_inner_left π₀, engaged]
    _=inner ℂ (π₀ y) x:= by rw [←S.swing,centered] -- may rw wrong
    _=_:= by rw [←engaged S,ContinuousLinearMap.adjoint_inner_left]; rw [engaged S] -- `←engaged S` loops
lemma branch_power(t:ℝ≥0) : Commute (G) (S.E t):=by
 change _*_=_; ext1 x; change G (E t x)=E t (G x); rw [show G=_ from spotlight S]; change E t x-π₀ (E t x)=E t (x-π₀ x); rw [map_sub,centered,powerS]
lemma transit_const (h : x∈S.ground) : ∀ᵐ u ∂(μ x), u=0:=by
 have hx:(μ x) W=0:= ((P).null_pair measurableSet_Ioi x).2 ((lively S x).1 h)
 refine ((mature S x).and (?_ : ∀ᵐ u ∂(μ x), u∉ W)).mono (fun i z=> le_antisymm (le_of_not_gt z.2) z.1); rw [ae_iff]; simpa [Set.Ioi] using hx
lemma mink_invar (t:ℝ) (h:x∈ S.ground) : U t x=x:=by
 apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ);
 · exact (S.life ..).le
 rw [inner_re_symm,←harmonizes]
 rw [show (∫ u:ℝ, _ ∂(μ x))= _ from (show (∫ u:ℝ, Complex.exp ((u:ℂ)*(t:ℂ)*I) ∂(μ x))= ∫u:ℝ,(1:ℂ)∂(μ x) from integral_congr_ae ((transit_const S x h).mono fun u hz=>by simp [hz]))]; rw [integral_const,full_size]; simp -- maybe signature
 rw [← Complex.ofReal_pow,ofReal_re]
-- commutations. `edge` from monoAxis commutes physical travel. use any commutant of unit heat. Doesn't require include `Semigroup` with OTHER dynamics.
lemma coast_of_commute (R:H.Op)(p:Commute (S.E 1) R){z:ℂ}(t:z∈inside) : Commute (S.F z) R:= (S.stare 1).commute_cfcHom (S.stare 1).isStarNormal p (S.roots z)
lemma edge_of_commute (R:H.Op)(p:Commute (S.E 1) R)(t:ℝ) : Commute (S.edge t) R:= by
 change _*_=_; apply DFunLike.coe_injective; apply (S.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _); funext v
 let u:=duration 1+ sideways t; have h: u∈ inside:=OS.Semigroup.length.mpr (by norm_num)
 change U t (R (E 1 v))=R (U t (E 1 v)); rw [show R (E 1 v)=E 1 (R v) from DFunLike.congr_fun p.eq.symm v,S.high,S.high]; exact DFunLike.congr_fun (coast_of_commute S R p h).eq v
lemma branch_arc(t:ℝ):Commute (S.edge t) (G) := edge_of_commute S _ ((branch_power S 1).symm) t
-- thermal correlation preview. no spatial momentum assumption. pack scalar matrix with bounded analytic including real edge.
end YM.Spectral.Alps
open YM.Spectral.Alps
#print axioms snow
#print axioms harmonizes
#print axioms atom_px
#print axioms moment
#print axioms realU
#print axioms spotlight
#print axioms transit_const
#print axioms branch_arc
#print axioms mink_invar
