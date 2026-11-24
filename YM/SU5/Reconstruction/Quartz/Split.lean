import YM.SU5.Reconstruction.Quartz.Glisten
/-!
# Hol price on graph clocks: first spectream pins.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace
open Multiplier Picket CrossedFrame Clasp
variable {K H D:Hilbert}{Z:Type*}[MeasurableSpace Z]
-- notebook crystal economy
noncomputable def glaze (x:ℝ):ℂ:= (Real.sqrt x:ℂ)
lemma glaze_charge (f:Z→ℝ)(v:Measurable f)(q:∀ x, f x≤1) : Tag (glaze ∘ f):=by
 refine ⟨by unfold glaze; fun_prop,1,zero_le_one,?_⟩; intro x; unfold glaze comp; rw [Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact Real.sqrt_le_one.mpr (q x)
omit [MeasurableSpace Z] in
lemma fuse {f:Z→ℝ}(p:∀ x,0≤ f x): (glaze∘f)*(glaze∘f)=(fun x=>(f x:ℂ)):=funext fun i=> by change glaze (f i)*_=_; unfold glaze; erw [← Complex.ofReal_mul, Real.mul_self_sqrt (p _)]
lemma glaze_s (P:PVM K Z) {f:Z→ℝ}(p:Measurable f)(q:∀ x,f x≤1): 0≤ order P (glaze ∘ f):=by
 let g:= Real.sqrt ∘ f; have hm : Measurable g:=by unfold g; fun_prop; 
 let X:= order P (glaze ∘ g); have hv:=order_reads P (glaze_charge g hm (fun x=> Real.sqrt_le_one.mpr (q x)))
 have e:= hv.adjoint.times hv; rw [show star (glaze ∘ g)=glaze ∘ g from (funext fun x=> (by simp [glaze])),fuse (f:=g) (fun x=>Real.sqrt_nonneg _)] at e
 have t:star X*X=order P (glaze∘ f):=e.single (order_reads P (glaze_charge f p q)); rw [←t]; exact star_mul_self_nonneg _
lemma peel_price(P:PVM K Z){U: K.Op} {f:Z→ℝ}(p:Measurable f)(g:∀ x,f x∈ Icc (0:ℝ) 1)(h:Registers P (fun x=> (f x:ℂ)) U):Registers P (glaze ∘ f) (CFC.sqrt U):= by
 let y:= glaze_s P p (fun x=>(g x).2)
 set V:= order P (glaze ∘ f); have e:Registers P (glaze∘ f) V:= order_reads _ (glaze_charge f p (fun x=>(g x).2))
 have w:=e.times e; rw[fuse (fun x=>(g x).1)] at w; rw [CFC.sqrt_unique (w.single h) y]; exact e
variable (C:Clasp K H D)
local notation "A"=> C.angle
local notation "P"=> C.motion
local notation "f"=> C.realF
local notation "I"=> spectrum ℂ C.angle
local notation "Wl"=> peel C.l
local notation "Wr"=> peel C.r
lemma peelL : Registers C.motion (glaze∘ f) (peel C.l):= peel_price P C.measurable_realF C.price C.angle_reads
lemma peelR : Registers C.motion (glaze∘(fun x=>1-C.realF x)) (peel C.r):= by
 unfold peel; rw [C.complement]; exact peel_price P (by fun_prop) (fun x=>by constructor<;> linarith [(price C x).1,(price C x).2]) C.roof_compl
local notation "θ"=> C.crystal
noncomputable def slopeZone (n:ℕ):Set (spectrum ℂ C.angle):={x| |C.crystal x|≤n}
noncomputable def glacier (n:ℕ):K.Op:= C.motion.region (slopeZone C n)
lemma slope_m(n:ℕ):MeasurableSet (slopeZone C n):= measurableSet_le (by fun_prop) measurable_const
lemma grow (n m:ℕ) (p:n≤m): slopeZone C n⊆ slopeZone C m:=fun t h=> show |θ t|≤(m:ℝ) from le_trans h (Nat.cast_le.mpr p)
lemma earth(n:ℕ): Registers C.motion ((slopeZone C n).indicator (1:I→ℂ)) (glacier C n):= Registers.box P (slope_m C n)
lemma glaze_self(n:ℕ): IsSelfAdjoint (glacier C n):= C.motion.real (slope_m C n)
lemma skate (n m:ℕ)(p:n≤m): glacier C n * glacier C m=glacier C n:= calc
 _= C.motion.region (slopeZone C n∩slopeZone C m):= C.motion.joins (slope_m C n) (slope_m C m)
 _ = _:= by rw[inter_eq_left.mpr (grow C n m p)]; rfl
lemma slope_ind(n:ℕ)(x:I): ‖(slopeZone C n).indicator (1:I→ℂ) x‖≤1:=by by_cases h:x∈ slopeZone C n<;> simp[h]
lemma glacier_safe (n:ℕ):‖glacier C n‖≤1 := (earth C n).fare zero_le_one (slope_ind C n)
lemma glaze_shrinks(x:K): Tendsto (fun n:ℕ=> glacier C n x) atTop (𝓝 x):= by
 refine Registers.tends atTop _ _ (Registers.one P) (fun n=>earth C n) x 1 (Eventually.of_forall (fun n=>Eventually.of_forall (slope_ind C n))) (Eventually.of_forall (fun t=>?_))
 apply tendsto_const_nhds.congr'
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop |θ t|)] with n e
 rw [indicator_of_mem (show t∈slopeZone C n from e)]
noncomputable def height (n:ℕ)(x:I):ℝ:=min n (max (- (n:ℝ)) (C.crystal x))
local notation "h" n:max=> height C n
lemma height_m(n:ℕ):Measurable (height C n):= by unfold height; fun_prop
lemma height_edge(n:ℕ)(x:I): |height C n x|≤ n:= by rw [abs_le]; unfold height; exact ⟨le_min (by linarith) (le_max_left ..),min_le_left ..⟩
noncomputable def face (n:ℕ)(x:I):ℂ:= (height C n x:ℂ)
noncomputable def axe(n:ℕ): K.Op:= order P (face C n)
lemma face_audit(n:ℕ): Registers C.motion (face C n) (axe C n):= order_reads P (show Tag (face C n) from
  ⟨Complex.continuous_ofReal.measurable.comp (height_m C n),n,by positivity,fun x=>by simpa only [face,Complex.norm_real,Real.norm_eq_abs] using height_edge C n x⟩)
lemma face_ready(n:ℕ)(x:I)(p:x∈ slopeZone C n):height C n x= C.crystal x:= by
 obtain ⟨a,b⟩:= abs_le.mp (show |θ x|≤n from p); unfold height; rw [max_eq_right a, min_eq_right b]
noncomputable def rise(n:ℕ) (z:ℂ): K.Op:= NormedSpace.exp ((z/2) • axe C n)
noncomputable def rise_tag(n:ℕ)(z:ℂ)(x:I):ℂ:= Complex.exp (z/2 * (height C n x:ℂ))
lemma rising (n:ℕ)(z:ℂ) : Registers P (rise_tag C n z) (Quartz.rise C n z):=(Registers.money ((face_audit C n).scale (z/2))) -- tune
lemma rise_analytic(n:ℕ)(z:ℂ) :DifferentiableAt ℂ (Quartz.rise C n) z:=by
 let g(z : ℂ):= z/2; change DifferentiableAt ℂ ((fun z:ℂ=> NormedSpace.exp (z • axe C n)) ∘ g) z; refine ((hasDerivAt_exp_smul_const (axe C n) (g z)).differentiableAt).comp z (show DifferentiableAt ℂ g z from ?_); unfold g; fun_prop
lemma rise_add (n:ℕ)(z u:ℂ): Quartz.rise C n (z+u)= Quartz.rise C n z* Quartz.rise C n u:=by
 apply (rising C n (z+u)).single; convert ((rising C n z).times (rising C n u)) using 1; ext x; simp only[Pi.mul_apply, rise_tag,← Complex.exp_add]; congr 2; ring
@[simp] lemma rise_neutral(n:ℕ) : Quartz.rise C n 0=1:=by simp [Quartz.rise]
end YM.Quartz
