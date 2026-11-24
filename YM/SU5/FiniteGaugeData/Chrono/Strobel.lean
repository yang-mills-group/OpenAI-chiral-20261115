import YM.SU5.FiniteGaugeData.Chrono.Scarab
import YM.Heat.Duration
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> store Y h i R L a A
local notation "V"=> Vect Y h a 0
local notation "H"=> A.space
section
open scoped NNReal ENNReal
-- auxiliary zero space ONLY to call the abstract time-direction THEOREM in library.
def tempo_aux : OS.Semigroup A.space a where
 E:= rail Y h R L a A
 U _:=1
 eZero:=rail_zero ..
 time t s:= rail_add ..
 shrinks t:= rail_bound ..
 sym t:= (IsSelfAdjoint.of_nonneg (rail_nn Y h R L a A t))
 uZero:= rfl
 space _ _:= by ext1; rfl
 unitary _ _:= rfl
 independent t s:= by ext1; rfl
 continuousE v:= rail_all ..
 continuousU _:= continuous_const
local notation "T"=> tempo_aux Y h R L a A
lemma denseRail (t:ℝ≥0): DenseRange (rail Y h R L a A t):=(T).whole t
lemma injectRail (t:ℝ≥0) (x:A.space)(h':rail Y h R L a A t x=0):x=0:=(T).heat_faithful t x h'
def realAxis : Spectral.Orbit A.space ℝ where
 translation := (tempo_aux Y h R L a A).edge
 origin:= (T).birth
 sends:= (T).send
 unitary:= (T).life
 moves:=(T).cont
-- time component of AUX measure. not claiming actu spacetime! use version from any semigroup for portable.
section
open Spectral Measure -- tune
variable {S':Hilbert}{A':Axis}(F:OS.Semigroup S' A')
def axis_spec : PVM S' ℝ := F.ℚmeasure.route (fun x:E4=>x A') (by fun_prop)
lemma realHeat (z:ℂ)(hz:0≤z.im)(v:S'):
   inner ℂ v (F.edge z.re (F.E z.im.toNNReal v)) = ∫ p, Complex.exp ((↑p:ℂ)*z*Complex.I) ∂(axis_spec F).diagonal v:=by
 rw [show (axis_spec F).diagonal v = Measure.map (fun x:E4=>x A') (F.ℚmeasure.diagonal v) from rfl, integral_map (by fun_prop) (by fun_prop)]
 have he:= F.heat 0 v (z:=z) hz; unfold OS.Semigroup.J OS.Semigroup.ray at he; rw [F.unit.origin] at he; simpa [Boundary.Probe.plane] using he -- simp E4 probe
lemma energyP (v:S'): ((axis_spec F).diagonal v).support ⊆ Set.Ici 0 := support_subset_of_isClosed isClosed_Ici (show ∀ᵐ p:ℝ ∂(axis_spec F).diagonal v,0 ≤ p from (ae_map_iff (f:=fun x:E4=>x A') (by fun_prop) measurableSet_Ici).mpr (F.bright v))
lemma real_fixed (v:S')(u:v∈F.ground)(z:ℝ): F.edge z v=v:=by
 let f:ℂ→S':= fun z=> F.F z v
 let X:= OS.Semigroup.inside
 let d:= OS.Semigroup.duration
 have he: AnalyticOnNhd ℂ f X:=fun z hz=> (ContinuousLinearMap.apply ℂ S'.space v).analyticAt _|>.comp (F.localHeat z hz)
 have hX (t:ℝ≥0)(p:0<t): f (d t)=v:= (congrArg (fun g:S'.Op=>g v) (F.roots_heat p)).trans ((F.fixed v).mp u t)
 have hg:Set.EqOn f (fun _=>v) X:= he.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0 |>.isPreconnected) (z₀:=(d 1:ℂ)) (by exact OS.Semigroup.dur.mpr zero_lt_one) (by -- Args inspect
    intro hn
    have e:Tendsto d (𝓝[>] (1:ℝ≥0)) (𝓝[≠] (d 1)):=by
       apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within; · exact (Complex.continuous_ofReal.comp continuous_subtype_val).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
       filter_upwards [self_mem_nhdsWithin] with i p; exact fun t=> (Set.mem_Ioi.mp p).ne' (Subtype.ext (Complex.ofReal_injective t))
    obtain ⟨i,t,q⟩:= ((e.eventually hn).and self_mem_nhdsWithin).exists; exact t (hX _ (lt_trans zero_lt_one (Set.mem_Ioi.mp q))))
 calc
  _ = F.edge z (F.E 1 v) := congrArg (F.edge z) ((F.fixed v).mp u 1).symm
  _ = f (d 1+ OS.Semigroup.sideways z):= F.high _ _
  _ = _:= hg (OS.Semigroup.length.mpr zero_lt_one)
end
def prism : Spectral.PVM A.space ℝ := axis_spec (tempo_aux Y h R L a A)
theorem ray_status : (realAxis Y h R L a A).Spectrum (prism Y h R L a A) :=by
 intro x b; rw [MeasureTheory.charFun_apply]; have he:= realHeat (T) (b:ℂ) (by simp) x; rw [Complex.ofReal_im, Complex.ofReal_re,Real.toNNReal_zero,(T).eZero] at he; refine (?_ : _= (∫ p, Complex.exp ((↑p:ℂ)*(↑b)*(Complex.I)) ∂(axis_spec (T)).diagonal x)).trans he.symm; apply integral_congr_ae; filter_upwards with t; simp [mul_comm] -- tune charFun namespace
lemma prices_up (v:A.space): ((prism Y h R L a A).diagonal v).support ⊆ Set.Ici 0 := energyP (T) v
lemma lapWick (z:ℂ)(t:0≤z.im)(v:A.space): inner ℂ v ((realAxis Y h R L a A).translation z.re (rail Y h R L a A z.im.toNNReal v)) = ∫ p, Complex.exp ((↑p:ℂ)*z*Complex.I) ∂(prism Y h R L a A).diagonal v := realHeat (T) z t v
-- density observation.Limits for smeared time correlations are represented thereby: ALL V, x. Occupancy/budgets of moving times via WP1; add real interpolation price later.Port. unit... ground
abbrev goldStar := A.paid 1
local notation "Ω"=> goldStar Y h R L a A
@[simp] lemma seed_gold : (G s) 1=(Ω):= by rw [clapper,seedling_one]
lemma gold_norm : ‖Ω‖=1:=by
 rw [← seed_gold Y h 0 R L a A]; apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp; rw [normStore]; change (E 0 (helve Kₜ a 1 1).val).re= _; rw [helve,ice_central,mul_one, identityW,(R.gaugeMatter 0).1]; norm_num
@[simp] lemma seed_stay (z:ℤ) (t:j=a→0≤z): (tock Y h s R L a j A z t) Ω= Ω:=by
 rw [← seed_gold Y h s R L a A,clock_own,show hoist Y h a j z t 1=1 from Subtype.ext (clock_one ..)]
-- identify Ground.Mean.Space not known whether already extremal, statement consensus retaining. 
def foundationE := (tempo_aux Y h R L a A).ground
lemma gold_pays : goldStar Y h R L a A ∈ foundationE Y h R L a A:= by
 have he(n:ℕ):thetaX Λ 0 n=n:=by simp [thetaX,tassel]
 have ht(n:ℕ):rail Y h R L a A n (Ω)=Ω:=by rw [← he, rail_actual,seed_stay]
 have hp:(T).orth (Ω)=(Ω):= tendsto_nhds_unique (((T).emerges Ω).comp (tendsto_natCast_atTop_atTop (R:=ℝ≥0))) (tendsto_const_nhds.congr' (Eventually.of_forall fun k=> (ht k).symm)) -- dims
 rw [← hp]; exact (T).ground.starProjection_apply_mem _
lemma ground_euclid (v:A.space) : v∈ foundationE Y h R L a A↔ ∀ t:ℝ≥0, rail Y h R L a A t v=v:= (T).fixed v
lemma ground_spike (t:ℝ)(v:A.space)(p:v∈foundationE Y h R L a A): (realAxis Y h R L a A).translation t v=v:= real_fixed (T) v p t
-- keep ACTUAL spatial discrete sym through boundary
section
open OS.Semigroup
lemma veers_real (z:ℤ)(t:j=a→0≤z)(m:ℝ): Commute ((realAxis Y h R L a A).translation m) (tock Y h s R L a j A z t):=by
 let P':= tempo_aux Y h R L a A; let x:= tock Y h s R L a j A z t; let v:= P'.F; let w:= OS.Semigroup.duration 1+sideways m
 have he: Commute (P'.E 1) x:= rail_free Y h s R L a j A 1 z t
 have ht:Commute (v w) x:= (P'.stare 1).commute_cfcHom (P'.stare 1).isStarNormal he (P'.roots w)
 change P'.edge m*x=x*P'.edge m; apply DFunLike.coe_injective; apply (P'.whole 1).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
 funext y; change P'.edge m (x (P'.E 1 y))= x (P'.edge m (P'.E 1 y)); rw [show x (P'.E 1 y)=(P'.E 1) (x y) from congrArg (fun T':A.space.Op=> T' y) he.eq.symm,P'.high,P'.high]; exact congrArg (fun T':A.space.Op=> T' y) ht.eq
end
#print axioms prices_up
#print axioms lapWick
end
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
