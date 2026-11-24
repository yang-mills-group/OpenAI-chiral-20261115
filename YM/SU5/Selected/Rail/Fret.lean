import YM.SU5.Selected.Airy.Thermal
/-! # All four coordinates apart
Strictly sorted X Y slabs in *every* reflection axis for the **same** component probes requires
more than the high-rank `grounds` theorem. Here establish a kernel outside any stencil in
all axes. Inputs are polynomials with an ARBITRARY number of zero moments. Use AP alias law
of same projectors. Reuse arguments of Airy.Weave, generalised to whole real Brillouin cube.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ" => 2*π
local notation "A" => deck
variable {x:Facet3} (v:FaceL)(w:ℝ)(a:ℤ)
local notation "V" x:max l:max => tempoL x l
local notation "E" x:max => tempoE x
def hill : Set Facet3 := closedBall 0 Real.pi
def Cliff : Set Facet3:= hill \ {0}
variable (c:x∈Cliff)
open Finset
lemma hill_mem {x:Facet3}: x∈hill ↔ ‖x‖≤π:=by simp [hill]
lemma drop (x:ℝ) (h: x∈ Set.Icc (-π) π)(i:ℤ): |x| ≤ |x+ 2*π*i|:=by
 by_cases u:i=0; · simp [u]
 have e:1 ≤ |(i:ℝ)|:=by exact_mod_cast (Int.one_le_abs u)
 have g: |(2*π*i)|≤ |x|+ |x+2*π*i|:= by
    conv_lhs => rw [show 2*π*i= -x+(x+2*π*i) from (by ring)]
    exact (abs_add_le (-x) (x+2*π*i)).trans_eq (by rw [abs_neg])
 have hp:|x|≤π:= abs_le.mpr h; rw [abs_mul,abs_of_pos (by positivity:0<2*π)] at g;
 nlinarith [mul_le_mul_of_nonneg_left e Real.pi_pos.le]
lemma lower_t (x:Facet3)(i:Fin 3): |x i| ≤ E x:=by
 refine le_trans ?_ (Real.sqrt_le_sqrt (Finset.single_le_sum (f:=fun i:Fin 3=> x i^2) (fun i _=> sq_nonneg _) (mem_univ i))); rw [Real.sqrt_sq_eq_abs]
lemma hillv (t:x∈hill)(i:Fin 3): x i ∈ Set.Icc (-π) π:=abs_le.mp ((norm_le_pi_norm x i).trans (hill_mem.mp t))
lemma least (t:x∈hill): ‖x‖ ≤ E (V x v):=(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i=> (drop (x i) (hillv t i) (v i)).trans (lower_t (tempoL x v) i) -- v local
include c
lemma born_e: 0<E (V x v):= (norm_pos_iff.mpr (show x≠0 from c.2)).trans_le (least v c.1)
-- replace all cabin. sign positive.
lemma hillB (w:ℝ)(h:w∈ Set.Icc (-π) π): Bound π (Ε x w) := by
 apply (pi_norm_le_iff_of_nonneg pi_pos.le).mpr; intro i; cases i using Fin.lastCases with
 | last=> exact (node₃ x w).symm ▸ (abs_le.mpr h) -- motive issue
 | cast i=> rw [nodeV]; exact abs_le.mpr (hillv c.1 i)
lemma powerV(w:ℝ): Ε x w ≠ (0:Bin):= fun h=> c.2 (show x=0 from funext (fun i=> (nodeV x w i).symm.trans (congrFun h i.castSucc)))
lemma stamp (t:w∈A) : HasSum (signArc (Ε x w) ∘ ridge) (arc (Ε x w)):=by
 have hx(k:Axis):= Equiv.hasSum_iff ridge |>.mpr ((spending (hillB c w ⟨t.1.le,t.2⟩) (powerV c w) k).of_norm.hasSum)
 rw [arc_lo]; exact (hx 2).add ((hx 3).mul_left _)
-- integral over A. continuous per-slit ALPS; budget initially depends on x. derive piece.
lemma stamp_bound : ∃ u: FaceL×ℤ→ℝ,Summable u∧∀ (w:ℝ),w∈deck →∀ v, ‖signArc (Ε x w) (ridge v)‖ ≤ u v:= by
 -- zero ridge finite slot support. continuity use raw_split
 let f (i:Cover) (w:ℝ):= signArc (Ε x w) i; obtain ⟨C,hC,e⟩:= boundC 2; obtain ⟨B,h',d⟩:=boundC 3
 let s:= Set.Icc (-π) π; have hh(v:FaceL)(z:ℤ): Continuous (f (ridge (v,z))):=by
    unfold f; simp_rw [raw_split];  have hz:0< E (V x v):= born_e v c
    unfold smoothZip biasStamp turn; fun_prop (disch:= assumption)
 obtain ⟨o,k⟩:= isCompact_Icc.bddAbove_image ((hh 0 0).norm.continuousOn (s:=Set.Icc (-π) π))
 let r(v):= (C+B)*income (ridge v); let g:= r + Pi.single (0,0) (max 0 o :ℝ); have h0 : ridge (0,(0:ℤ))=0:= by funext i; cases i using Fin.lastCases <;> simp [ridge,Ε]
 refine ⟨g,(Equiv.summable_iff ridge|>.mpr (wallet.mul_left (C+B))).add (hasSum_pi_single ..).summable,?_⟩
 intro w l i; by_cases p:i=(0,0);
 · subst i; simp only [g,Pi.add_apply,Pi.single_eq_same]; apply (k (show _∈ (fun w=> ‖f (ridge (0,0)) w‖) '' s from ⟨w,⟨l.1.le,l.2⟩,rfl⟩)).trans; exact (le_max_right ..).trans (le_add_of_nonneg_left (by unfold r; exact mul_nonneg (add_nonneg hC.le h'.le) (income_2 _).le))
 have p':ridge i ≠0:= fun k=> p (ridge.injective (k.trans h0.symm));
 simp only [g,Pi.add_apply,Pi.single_eq_of_ne p,add_zero]; let A':= Ε x w; unfold signArc; refine (norm_add_le ..).trans ?_; rw [norm_mul,norm_neg,Complex.norm_I,one_mul]; unfold r; rw [add_mul]; exact add_le_add (e _ (hillB c w ⟨l.1.le,l.2⟩) (powerV c w) (ridge i) p') (d _ (hillB c w ⟨l.1.le,l.2⟩) (powerV c w) (ridge i) p')
private lemma continuous_split (v: FaceL×ℤ) : Continuous (fun w=>signArc (Ε x w) (ridge v)):=by
 rcases v with ⟨v,i⟩; simp_rw [raw_split];  have hz:0< E (V x v):= born_e v c
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
include c
lemma gauge_both (v:FaceL)(w:ℤ) :
    let y:= tempoL x v; let e:= tempoE y; let g:= smoothZip e 8; let s:ℝ:=2*sol y^8
    HasSum (fun i:ℤ=>∫ t in deck,surge w t*signArc (Ε x t) (ridge (v,i)))
      ((s:ℂ)*(↑(y 2)*integrated g w+integrated (biasStamp g) w)):=by
 intro y e g s; let h(t:ℝ):= surge w t*(s:ℂ)*(↑(y 2)*g t+biasStamp g t)
 have hp:0<e:= born_e v c; have hx:= surged w (smooth_paid hp 8); have hw:= surged w (bias_paid hp 7) -- order 
 let u(t:ℝ):= surge w t*((s:ℂ)*(↑(y 2)*g t+biasStamp g t));
 have hl(t:ℝ): u t=(s:ℂ)*(↑(y 2)*(surge w t * g t)+surge w t*biasStamp g t):=by unfold u; ring
 have hu: Integrable u:=by rw [funext hl]; exact ((hx.const_mul ((y 2:ℝ):ℂ)).add hw).const_mul _
 have he (i:ℤ)(t:ℝ): u (turn t i)= surge w t*signArc (Ε x t) (ridge (v,i)):=by unfold u; rw [surge_periodic,raw_split]
 have p:=marchBand u hu; simp_rw [he] at p; unfold integrated; convert p using 1 <;> try rfl
 rw [funext hl, integral_const_mul, integral_add (hx.const_mul _) hw, integral_const_mul] -- rw orientation


lemma plus (t:4≤ (a:ℝ)): HasSum (fun v=> (summer true a x v:ℂ)) (∫ x' in deck,surge a x'*arc (Ε x x')):=by
 refine HasSum.prod_fiberwise (paid_sum (a:ℝ) c) (fun v=>?_)
 let z:=E (V x v); have hz: 0< z:= born_e v c
 have h:= gauge_both c v a; dsimp only at h; unfold z at hz; rw [shifted hz 7 (by norm_num; exact t), lapel hz 8 (by norm_num; exact t)] at h
 convert h using 1
 unfold summer; dsimp only; rw [if_pos rfl]; push_cast; ring
lemma haunts (w:ℕ)(p:w≥4): HasSum (fun v=> (summer true w x v:ℂ)) (thru x w):=by simpa only [thru, Int.cast_natCast] using (Rail.plus (w:ℤ) c (by exact_mod_cast p))
lemma pret (k:ℕ): 0 ≤ summer true k x v:=by
 unfold summer; dsimp only; rw [if_pos rfl];
 let z:=V x v; let A':=E z; have hz:0<A':=born_e v c; have ht:= weight_pos hz; have h:0 ≤ A'+z 2:=by linarith [(neg_le_abs (z 2)).trans (lower_t z 2)]
 change 0 ≤ 2*sol z^8 * ((A'+_)*_*_); unfold sponsor; positivity
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms haunts
#print axioms pret
#print axioms least
