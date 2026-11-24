import YM.SU5.Selected.Airy.Common

/-! # Parallel flyers: a frequency box used with the SAME `Crest` normalization.
Sharpening the signal to nonzero excited state needs temporal Hankel arguments, after Male,
not one subtraction on a scalar. This file analytic, no new law assumptions. Units radians. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ" => 2*π
abbrev deck : Set ℝ:= Set.Ioc (-π) π
local notation "A" => deck
variable {x:Facet3} (v:FaceL)(w:ℝ)(a:ℤ)(c:x∈grounds)
local notation "V" x:max l:max => tempoL x l
local notation "E" x:max => tempoE x
def arc (x:Bin) : ℂ := -(zen (tough x)) 2 0
lemma arc_lo (x:Bin) : arc x= tough x 2 + -I * tough x 3 := by
 let z := tough x; have h : -(zen z) 2 0=z 2+ -I*z 3:=by
    unfold zen; rw [Matrix.sum_apply]; -- Fin cases
    simp [Axis,SpinIdx,Fin.sum_univ_succ, gammaOp]; ring_nf 
 exact h

def signArc (x:Bin)(l:Cover):= slat x l 2 + -I*slat x l 3 -- W_-+
lemma raw_split : signArc (Ε x w) (ridge (v,a)) = let y:= tempoL x v
    let e:= E y; let g:= smoothZip e 8; let t:=turn w a; let s:ℝ:=2*sol y^8
    (s:ℂ)*(↑(y 2)*g t+biasStamp g t) := by
 unfold signArc slat; rw [ridges]; dsimp only; let y:=tempoL x v; let e:=E y; let u:=turn w a
 simp_rw [node₂,node₃, ←magnitude, biasStamp,smoothZip, weave_tail,Crest.zip]; push_cast; ring
-- local summability all. roar near positive box. Hunt uniform.
include c
lemma stamp (t:w∈A) : HasSum (signArc (Ε x w) ∘ ridge) (arc (Ε x w)):=by
 have hx(k:Axis):= Equiv.hasSum_iff ridge |>.mpr ((spending (banded c w ⟨t.1.le,t.2⟩) (pureV c w) k).of_norm.hasSum)
 rw [arc_lo]; exact (hx 2).add ((hx 3).mul_left _)
-- integral over A. continuous per-slit ALPS; budget initially depends on x. derive piece.
lemma stamp_bound : ∃ u: FaceL×ℤ→ℝ,Summable u∧∀ (w:ℝ),w∈deck →∀ v, ‖signArc (Ε x w) (ridge v)‖ ≤ u v:= by
 -- zero ridge finite slot support. continuity use raw_split
 let f (i:Cover) (w:ℝ):= signArc (Ε x w) i; obtain ⟨C,hC,e⟩:= boundC 2; obtain ⟨B,h',d⟩:=boundC 3
 let s:= Set.Icc (-π) π; have hh(v:FaceL)(z:ℤ): Continuous (f (ridge (v,z))):=by
    unfold f; simp_rw [raw_split];  have hz:0< E (V x v):= lt_of_lt_of_le zero_lt_one (backend v c)
    unfold smoothZip biasStamp turn; fun_prop (disch:= assumption)
 obtain ⟨o,k⟩:= isCompact_Icc.bddAbove_image ((hh 0 0).norm.continuousOn (s:=Set.Icc (-π) π))
 let r(v):= (C+B)*income (ridge v); let g:= r + Pi.single (0,0) (max 0 o :ℝ); have h0 : ridge (0,(0:ℤ))=0:= by funext i; cases i using Fin.lastCases <;> simp [ridge,Ε]
 refine ⟨g,(Equiv.summable_iff ridge|>.mpr (wallet.mul_left (C+B))).add (hasSum_pi_single ..).summable,?_⟩
 intro w l i; by_cases p:i=(0,0);
 · subst i; simp only [g,Pi.add_apply,Pi.single_eq_same]; apply (k (show _∈ (fun w=> ‖f (ridge (0,0)) w‖) '' s from ⟨w,⟨l.1.le,l.2⟩,rfl⟩)).trans; exact (le_max_right ..).trans (le_add_of_nonneg_left (by unfold r; exact mul_nonneg (add_nonneg hC.le h'.le) (income_2 _).le))
 have p':ridge i ≠0:= fun k=> p (ridge.injective (k.trans h0.symm));
 simp only [g,Pi.add_apply,Pi.single_eq_of_ne p,add_zero]; let A':= Ε x w; unfold signArc; refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_neg,Complex.norm_I,one_mul]; unfold r; rw [add_mul]; exact add_le_add (e _ (banded c w ⟨l.1.le,l.2⟩) (pureV c w) (ridge i) p') (d _ (banded c w ⟨l.1.le,l.2⟩) (pureV c w) (ridge i) p')
private lemma continuous_split (v: FaceL×ℤ) : Continuous (fun w=>signArc (Ε x w) (ridge v)):=by
 rcases v with ⟨v,i⟩; simp_rw [raw_split];  have hz:0< E (V x v):= lt_of_lt_of_le zero_lt_one (backend v c)
 unfold smoothZip biasStamp turn; fun_prop (disch:= assumption)
lemma paid_sum : HasSum (fun v=> ∫ t in deck, surge w t*signArc (Ε x t) (ridge v)) (∫ t in deck, surge w t*arc (Ε x t)):=by
 obtain ⟨u,p,h⟩:= stamp_bound c; let μ:=volume.restrict deck
 haveI : IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioc (-π) π)))
 apply hasSum_integral_of_dominated_convergence (fun i _=> u i) ?_ ?_ (Filter.Eventually.of_forall fun _=>p) (integrable_const (μ:=μ) (∑' i,u i))
 · exact (ae_restrict_mem measurableSet_Ioc).mono fun x e=> (stamp x c e).mul_left _
 · intro i; exact (((surge_cont.comp (continuous_const.prodMk continuous_id)).mul (continuous_split c i)).aestronglyMeasurable)
 intro i; filter_upwards [ae_restrict_mem measurableSet_Ioc] with x e; rw [norm_mul,surge_norm,one_mul]; exact h x e i
omit c
-- integral through every lattice shift exactly
private lemma marchBand {α:Type*}[NormedAddCommGroup α][NormedSpace ℝ α](f:ℝ→α)(u:Integrable f): HasSum (fun i:ℤ=> ∫ x in deck,f (turn x i)) (∫ x,f x):=by
 let p(i:ℤ):=Set.Ioc (turn (-π) i) (turn π i); let a:⋃ i:ℤ,p i=(Set.univ: Set ℝ):=by -- binder parentheses
   apply Set.eq_univ_of_forall; intro x; let l:ℝ:=(x- π)/φ; let v:=⌈l⌉; have ht:(0:ℝ)<φ:=by positivity
   refine Set.mem_iUnion.mpr ⟨v,?_⟩; change turn (-π) v < x ∧ x ≤ turn π v
   have h:=Int.le_ceil l; have hx:=Int.ceil_lt_add_one l
   have hz:l*φ=x-π:= div_mul_cancel₀ _ ht.ne'; unfold turn; constructor <;> nlinarith [mul_lt_mul_of_pos_left hx ht, mul_le_mul_of_nonneg_left h ht.le] -- conjunction?
 have e (i:ℤ): ∫ x in deck,f (turn x i)=∫ x in p i,f x:=by
    unfold deck p; rw [←intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos]),← intervalIntegral.integral_of_le (show turn (-π) i ≤ turn π i from add_le_add_left (by linarith [pi_pos]) _)]; exact intervalIntegral.integral_comp_add_right (f:=f) _ -- lemma args
 simp_rw [e]; have hl(i j:ℤ)(h:i<j): turn π i ≤ turn (-π) j:=by unfold turn; have ht: (i:ℝ)+1 ≤ j:=(by exact_mod_cast h); nlinarith [mul_le_mul_of_nonneg_left ht pi_pos.le]
 have hv:Pairwise (Disjoint on p):= fun i j h=> (lt_or_gt_of_ne h).elim (fun h=> Set.Ioc_disjoint_Ioc_of_le (hl i j h)) (fun h=> (Set.Ioc_disjoint_Ioc_of_le (hl j i h)).symm)
 have he:= hasSum_integral_iUnion (s:=p) (μ:=volume) (f:=f) (fun i=> measurableSet_Ioc) hv u.integrableOn; rw [a,Measure.restrict_univ] at he; exact he -- tune
lemma surge_periodic (w s:ℤ)(x:ℝ): surge w (turn x s)=surge w x:=by
 rw [turn,surge_right]; unfold surge; have ht : Complex.I*(((w:ℝ)*(φ*s):ℝ):ℂ)= ((w*s:ℤ):ℂ)*(2*π*Complex.I) := by push_cast; ring
 rw [ht,Complex.exp_int_mul_two_pi_mul_I,mul_one]
include c
lemma gauge_both (v:FaceL)(w:ℤ) :
    let y:= tempoL x v; let e:= tempoE y; let g:= smoothZip e 8; let s:ℝ:=2*sol y^8
    HasSum (fun i:ℤ=>∫ t in deck,surge w t*signArc (Ε x t) (ridge (v,i)))
      ((s:ℂ)*(↑(y 2)*integrated g w+integrated (biasStamp g) w)):=by
 intro y e g s; let h(t:ℝ):= surge w t*(s:ℂ)*(↑(y 2)*g t+biasStamp g t)
 have hp:0<e:= lt_of_lt_of_le zero_lt_one (backend v c); have hx:= surged w (smooth_paid hp 8); have hw:= surged w (bias_paid hp 7) -- order 
 let u(t:ℝ):= surge w t*((s:ℂ)*(↑(y 2)*g t+biasStamp g t));
 have hl(t:ℝ): u t=(s:ℂ)*(↑(y 2)*(surge w t * g t)+surge w t*biasStamp g t):=by unfold u; ring
 have hu: Integrable u:=by rw [funext hl]; exact ((hx.const_mul ((y 2:ℝ):ℂ)).add hw).const_mul _
 have he (i:ℤ)(t:ℝ): u (turn t i)= surge w t*signArc (Ε x t) (ridge (v,i)):=by unfold u; rw [surge_periodic,raw_split]
 have p:=marchBand u hu; simp_rw [he] at p; unfold integrated; convert p using 1 <;> try rfl
 rw [funext hl, integral_const_mul, integral_add (hx.const_mul _) hw, integral_const_mul] -- rw orientation
local notation "tₑ" => tempoE
local notation "sₑ" x:max v:max => 2 * sol (tempoL x v)^8
-- Plus tail e+b. Minus tail -(e-b)
def summer (u:Bool) (w:ℝ) (x:Facet3)(v:FaceL):ℝ:=
 let y:= tempoL x v; let e:= tempoE y; sₑ x v * ((e+(if u then y 2 else - y 2))* sponsor e 8* Real.exp (-e*w))
-- not yet normalized. reciprocal budget.
lemma plus (t:4≤ (a:ℝ)): HasSum (fun v=> (summer true a x v:ℂ)) (∫ x' in deck,surge a x'*arc (Ε x x')):=by
 refine HasSum.prod_fiberwise (paid_sum (a:ℝ) c) (fun v=>?_)
 let z:=E (V x v); have hz: 0< z:= lt_of_lt_of_le zero_lt_one (backend v c)
 have h:= gauge_both c v a; dsimp only at h; unfold z at hz; rw [shifted hz 7 (by norm_num; exact t), lapel hz 8 (by norm_num; exact t)] at h
 convert h using 1
 unfold summer; dsimp only; rw [if_pos rfl]; push_cast; ring
lemma minus (t:4≤(a:ℝ)): HasSum (fun v=> -(summer false a x v:ℂ)) (∫ x' in deck,surge (-a) x'*arc (Ε x x')):=by
 refine HasSum.prod_fiberwise (paid_sum (-a) c) (fun v=>?_)
 let z:=E (V x v); have hz: 0< z:= lt_of_lt_of_le zero_lt_one (backend v c)
 have h:= gauge_both c v (-a); dsimp only at h; unfold z at hz; rw [Int.cast_neg,downhill hz 7 (by norm_num; exact t), trough hz 8 (by norm_num; exact t)] at h
 convert h using 1
 unfold summer; dsimp only; rw [if_neg (by decide)]; push_cast; ring
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms plus
#print axioms minus
