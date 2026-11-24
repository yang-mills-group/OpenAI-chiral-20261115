import YM.CF.BProof.Release.Hot

/- exact measure. `τ` packed real coordinates input (`x`), below Fares; Haar V remains
(on all b incl dummy), nonsoft measure in Z. `crowd` imposes severe indicators of all
columns simultaneously; see note difference `by Z` via finite indicator equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release.Sky
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Locale hot Law
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}{M:ℕ}(θ κ:ℝ)(y:ℝ){R q w:ℝ}(X:Beam c R Y.short M y) (H:Room Y M)(u:T.Bounds c w R q)(h:θ∈Set.Icc (1/2) 2)
variable (a:Book K P Y κ X)(Z:Finset Y.Col)
-- pay amount (per w)
def soft (b:Y.Col) : Set (Locale.Place Y) := if b∈Z then Set.univ else dry Y κ y b
def fee (b:Y.Col) (x:Via (Roll.Place Y)):= if b∈Z then Day.ticket (trunc y) x else P.ticket (scaleD κ y) (g y) (Locale.A Y y b) x
def cursor (b:Y.Col):=volume.withDensity (fun x=> ENNReal.ofReal (fee P Y κ y Z b x))
def stop (V: House Y)(w: hot.Field Y) : House Y := Law.patch Z V (fun i=> Pub.stamp (g y) (Locale.A Y y i) (w i))
lemma limits : MeasurableSet (Set.univ.pi (soft Y κ y Z)):=MeasurableSet.univ_pi fun i=>by unfold soft; split; exact MeasurableSet.univ; exact Pub.den_m ..
lemma fee_m (b:Y.Col) : Measurable (fee P Y κ y Z b):= by by_cases h:b∈Z; unfold fee; simp_rw [if_pos h]; exact Day.ticket_m _; unfold fee; simp_rw [if_neg h]; exact Pub.ticket_m ..
@[fun_prop] lemma stop_m : Measurable (Function.uncurry (stop Y y Z)):=by
 unfold Function.uncurry stop; apply (patch_m (B:=Locale.Place Y) Z).comp (f:=fun (p: House Y × hot.Field Y)=> (p.1,fun i=>Pub.stamp (g y) (Locale.A Y y i) (p.2 i))) -- before bo hints
 fun_prop
lemma trunc_pos (y:ℝ):0<trunc y:=by unfold trunc hot.radius; exact pow_pos (pow_pos (coin_pos ..) _) _
lemma fee_nn (b:Y.Col) (x:Via (Roll.Place Y)):0≤ fee P Y κ y Z b x:=by unfold fee; split; exact Day.ticket_pos _ x (trunc_pos _); exact Pub.ticket_nn _ _ _ _ (coin_pos ..) _
lemma cursor_on (i:Y.Col)(v:i∈Z): cursor P Y κ y Z i=Day.mark (trunc y) (Roll.Place Y):=by simp_rw [cursor,fee,if_pos v]; rfl -- syntax simp?
lemma cursor_off (i:Y.Col)(v:i∉Z): cursor P Y κ y Z i=P.law (scaleD κ y) (g y) (Locale.A Y y i):= by simp_rw [cursor,fee,if_neg v]; rfl
include a -- H etc not needed
lemma cursors (v: Y.Col) : IsFiniteMeasure (cursor P Y κ y Z v):=by
 by_cases p:v∈ Z; rw [cursor_on _ _ _ _ _ v p]; haveI := Day.prob _ (Roll.Place Y) (trunc_pos y) -- metavar tune
 exact (inferInstance : IsFiniteMeasure (Day.mark (trunc y) (Roll.Place Y)))
 rw [cursor_off _ _ _ _ _ v p]; exact Law.MP.finite (P.arrange (scaleD κ y) (g y) (Locale.A Y y v) K (coin_pos ..) a.d₀ ((scaleA K P Y κ X a).trans a.grant))
lemma mp_stop : MeasurePreserving (Function.uncurry (stop Y y Z)) ((lobby Y).prod (Measure.pi (cursor P Y κ y Z))) ((lobby Y).restrict (Set.univ.pi (soft Y κ y Z))):=by
 haveI:∀ i,IsFiniteMeasure (cursor P Y κ y Z i):= cursors K P Y κ y X a Z; unfold lobby; rw [Measure.restrict_pi_pi]; apply MP.rearrange; · exact fun i=> Pub.stamp_m ..
 · intro i hi; rw [cursor_on _ _ _ _ _ i hi]; exact Day.prob _ _ (trunc_pos _)
 · intro i hi; unfold soft; rw [if_pos hi,Measure.restrict_univ]
 intro i hi; rw [soft,if_neg hi,cursor_off _ _ _ _ _ i hi]; exact P.arrange (scaleD κ y) _ _ K (coin_pos ..) a.d₀ ((scaleA K P Y κ X a).trans a.grant)

omit a
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F][MeasurableSpace F][BorelSpace F][SecondCountableTopology F][CompleteSpace F]
-- no superscript layers. lexicon, pack θ.
def wing (V:House Y)(x:Plan Y):= stop Y y Z V (fun b=>hot.entry Y x b)
def reach (V:House Y)(x:Plan Y):= wing Y y Z V (Beam.drive T θ X Z x)
def bill (x:Plan Y):= ∏ i, fee P Y κ y Z i (hot.entry Y x i)
def chunk (f:House Y → F)(V:House Y):= if bed Y κ y V=Z then f V else 0
lemma chunk_pay (f:House Y→F)(p:Envelope f): Envelope (chunk Y κ y Z f):=by obtain ⟨C,hC⟩:=p.cost; refine ⟨Measurable.ite (berth ..) p.meas measurable_const,C,fun x=> ?_⟩; unfold chunk; split; exact hC _; rw [norm_zero]; exact (norm_nonneg _).trans (hC x)
include a H h u
lemma fare_R (f:House Y→F)(p:Envelope f) :
    (∫ x,chunk Y κ y Z f x ∂lobby Y) = ∫ x, (Beam.ζ T θ X Z).det • (∫ w:Plan Y, bill P Y κ y Z (Beam.drive T θ X Z w) • chunk Y κ y Z f (reach Y T θ y X Z x w)) ∂lobby Y:=by
 haveI:∀ i,IsFiniteMeasure (cursor P Y κ y Z i):= cursors K P Y κ y X a Z; let V:=Measure.pi (cursor P Y κ y Z); let β:=lobby Y
 let S:=Set.univ.pi (soft Y κ y Z); let g:=chunk Y κ y Z f; have hg:Envelope g:=chunk_pay Y κ y Z f p; have he:S.indicator g=g:=by
    ext1 x; by_cases hp:x∈ S; rw [Set.indicator_of_mem hp]; rw [Set.indicator_of_notMem hp]; apply Eq.symm; exact if_neg (fun k=> hp (fun i _=> by change x i∈ soft _ _ _ _ i; unfold soft; split; exact Set.mem_univ _; exact dry_s Y κ y Z x k ‹_›))
 let Q:=Function.uncurry (stop Y y Z); let x:= g ∘ Q; have hh:Envelope x:= Law.pull hg (stop_m ..)
 haveI:IsProbabilityMeasure β:=by unfold β; infer_instance
 haveI:IsFiniteMeasure V:=by unfold V; infer_instance
 have hP:MeasurePreserving Q (β.prod V) (β.restrict S):=mp_stop K P Y κ y X a Z
 have h₁: (∫ w,g w ∂β)=∫ w, ∫ v,g (stop Y y Z w v) ∂V ∂β:=by
    conv_lhs=> rw [← he]
    rw [integral_indicator (limits ..),← apply_pres hP hg.meas]; exact integral_prod x (Law.pay hh)
 change (∫ x,g x ∂β)=_; rw [h₁]; apply integral_congr_ae; apply Eventually.of_forall; intro v; dsimp only
 change (∫ w,g (stop Y y Z v w) ∂Measure.pi (cursor P Y κ y Z)) = _
 unfold cursor; rw [MP.densify (μ:=fun i=>volume) (fee_m P Y κ y Z) (fee_nn P Y κ y Z)]
 let d(w:hot.Field Y):= (∏ i,fee P Y κ y Z i (w i)) • g (stop Y y Z v w)
 let e:=MeasurableEquiv.curry Y.Col (Roll.Place Y) ℝ; let t:= Beam.ζ T θ X Z
 have hd:Measurable d:=(Finset.measurable_prod (f:=fun (i:Y.Col)(w:hot.Field Y)=> fee P Y κ y Z i (w i)) _ (fun i _=> (fee_m ..).comp (measurable_pi_apply i))).smul (hg.meas.comp ((stop_m Y y Z).comp (f:=fun w:hot.Field Y=>(v,w)) (by fun_prop))) -- tune
 have hp:0<t.det:=Beam.bright T θ X Z H u h; change (∫ w:hot.Field Y,d w)= _; rw [← Law.apply_pres (g:=e) MP.volume_curry hd]; change (∫ x:Plan Y,(d ∘ e) x)=_; rw [← Law.apply_pres (MP.lin_stamp t hp) (hd.comp e.measurable),integral_smul_measure, ENNReal.toReal_ofReal hp.le]; rfl
end YM.CF.BProof.Release.Sky
