import YM.SU5.Selected.Airy.Thermal
import Mathlib.Analysis.Fourier.AddCircle
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
abbrev roundC:=AddCircle (2*π)
lemma piRank : 0<φ:=mul_pos (by norm_num) pi_pos
local instance : Fact (0<φ):= ⟨piRank⟩
abbrev td:= Set.Icc (-π) π
lemma td_ioc : -π+φ=π:=by ring
lemma dancer {X:Type*} [TopologicalSpace X] [CompactSpace X][T2Space X]{V:Type*} [TopologicalSpace V](f:X→ roundC→V)(e:Continuous (fun k:X×td=> f k.1 ((k.2.val:ℝ):roundC))): Continuous (uncurry f):=by
 let g : X×td→ X×roundC:= fun k=> (k.1,((k.2.val:ℝ):roundC))
 have h : Continuous g:= continuous_fst.prodMk ((AddCircle.continuous_mk' _).comp (continuous_subtype_val.comp continuous_snd))
 have hp:Surjective g:=by
    rintro ⟨x,y⟩; let v:=AddCircle.equivIoc (2 * π) (-π) y; have hx:v.val ∈td:=by unfold td; nth_rewrite 2 [←td_ioc]; exact Set.Ioc_subset_Icc_self v.2 -- syntax
    exact ⟨(x,⟨v.val,hx⟩), Prod.ext rfl AddCircle.coe_equivIoc⟩ -- tune
 haveI:CompactSpace td:=isCompact_iff_compactSpace.mp isCompact_Icc
 exact ((h.isClosedMap.isQuotientMap h hp).continuous_iff).mpr e -- name

lemma seam (x:Facet3) : Periodic (fun w=> tough (Ε x w)) (2 * π):=by
 intro i; simpa only [turn,Int.cast_one,mul_one] using regimeT x i 1
def walls (x:Facet3)(w:roundC): Momentum:= (seam x).lift w
@[simp] lemma walls_apply (x:Facet3)(w:ℝ): walls x (w:roundC)=tough (Ε x w):= rfl -- Quot reduction
lemma walls_walk : Continuous (fun k:grounds × roundC=> walls k.1.val k.2):=by
 haveI:CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
 apply dancer (fun k:grounds=> walls k.val)
 simp_rw [walls_apply]; let f: grounds × td→ Facet3 ×ℝ:= fun x=> (x.1.val,x.2.val)
 change Continuous ((tough ∘ joinBin) ∘ f)
 have hf: ContinuousOn f Set.univ:= (show Continuous f from ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).continuousOn
 exact continuousOn_univ.mp (thermalV.comp hf (show Set.MapsTo f Set.univ foyer from fun {x} _=> ⟨x.1.2,x.2.2⟩))

def slopeG(x:Facet3)(w:roundC):ℂ:=-(zen (walls x w)) 2 0
lemma slope_coe(x:Facet3)(w:ℝ): slopeG x (w:roundC)=arc (Ε x w):=rfl
lemma walksA (x:Facet3)(c:x∈grounds) : Continuous (slopeG x):=by
 let g: roundC → grounds × roundC:= fun w=> (⟨x,c⟩,w); have hg: Continuous g:= continuous_const.prodMk continuous_id; have h:Continuous (walls x):=by change Continuous ((fun k: grounds ×roundC=> walls k.1.val k.2) ∘ g); exact walls_walk.comp hg
 unfold slopeG zen; simp_rw [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]; fun_prop
lemma soldier (w:ℤ)(t:ℝ) : fourier w (t:roundC)= surge w t:=by
 rw [fourier_coe_apply]; unfold surge; push_cast; congr 1; field_simp [Complex.ofReal_ne_zero.mpr pi_pos.ne']
lemma printed (w:ℤ)(x:Facet3): fourierCoeff (slopeG x) w=(↑(φ⁻¹:ℝ):ℂ)*thru x (-w):=by -- notation φ⁻¹ parses?
 rw [fourierCoeff_eq_intervalIntegral _ _ (-π),td_ioc,intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos])]; simp_rw [soldier,slope_coe,smul_eq_mul]; rw [one_div,Complex.real_smul]; rfl
-- decays uniform each x. power or exp
local notation "ρ" => Real.exp (-1)
lemma high_steps (u:Bool)(x:Facet3)(c:x∈grounds)(p:ℕ) : ‖knee x u (4+p)‖ ≤ ‖knee x u 4‖* ρ^p:=by
 let A(v:FaceL)(p:ℕ):= summer u p x v; have hv (v:FaceL)(p:ℕ):0≤ (A v p:ℂ):= RCLike.ofReal_nonneg.mpr (funding x v u p c).le
 have h (p:ℕ)(e:p≥4) : 0≤ knee x u p:= hasSum_le (f:=fun _:FaceL=> (0:ℂ)) (fun i=> hv i p) hasSum_zero (spring x u p e c) -- name
 have hp: knee x u (4+p) ≤ knee x u 4 * ((ρ^p:ℝ):ℂ) :=by
   apply hasSum_le _ (spring x u (4+p) (by omega) c) ((spring x u 4 (by norm_num) c).mul_right _); intro v; rw [step_b, ←Complex.ofReal_mul]; apply RCLike.ofReal_le_ofReal.mpr; apply mul_le_mul_of_nonneg_left _ (funding x v u 4 c).le; apply pow_le_pow_left₀ (Real.exp_pos _).le _ p; exact Real.exp_le_exp.mpr (neg_le_neg (backend v c))
 apply (RCLike.ofReal_le_ofReal (K:=ℂ)).mp; change (↑‖knee x u (4+p)‖:ℂ) ≤ ↑(‖knee x u 4‖ * ρ^p); rw [Complex.ofReal_mul,←Complex.eq_coe_norm_of_nonneg (h (4+p) (by omega)), ← Complex.eq_coe_norm_of_nonneg (h 4 (by omega))]; exact hp
lemma budget_leg (u:Bool): ∃ C:ℝ,0<C∧∀ x∈grounds,∀ p:ℕ, ‖knee x u p‖ ≤ C*ρ^p:=by
 let W(v:ℕ)(x:Facet3):= ‖knee x u v‖* (ρ^v)⁻¹
 have he:(∀ v:ℕ, ∃ B:ℝ,∀ x∈grounds,W v x≤B):=fun v=> by
    obtain ⟨B,k⟩:= groundsCompact.bddAbove_image (((legs u v).norm).mul (continuousOn_const (c:= ((ρ^v)⁻¹)))) -- param
    exact ⟨B,fun x hx=>k (Set.mem_image_of_mem _ hx)⟩
 choose b h using he; let B:=1+(∑ i∈ range 5,max 0 (b i)); have hx:(0:ℝ)≤ ∑ i∈range 5, max 0 (b i):= sum_nonneg (fun i _=> le_max_left ..); have hp(v:ℕ)(e:v≤4)(x:Facet3)(p:x∈grounds) : ‖knee x u v‖≤ B * ρ^v := by
    apply (div_le_iff₀ (pow_pos (exp_pos (-1)) v)).mp
    rw [div_eq_mul_inv]; refine (h v x p).trans ((le_max_right 0 _).trans ?_); exact (single_le_sum (f:=fun i=> max 0 (b i)) (fun i _=> le_max_left _ _) (mem_range.mpr (by omega : v<5))).trans (le_add_of_nonneg_left (by norm_num))
 refine ⟨B,show 0<B from (by unfold B; positivity), fun x e v=> ?_⟩; by_cases z:v≤4; · exact hp v z x e
 obtain ⟨p,rfl⟩:= Nat.exists_eq_add_of_le (show 4≤ v by omega)
 rw [pow_add,←mul_assoc]; exact (high_steps u x e p).trans (mul_le_mul_of_nonneg_right (hp 4 (by omega) x e) (by positivity))
lemma budget_neg : ∃ C:ℝ,0<C∧∀ x∈grounds,∀ w:ℤ, ‖thru x w‖ ≤ C * ρ^w.natAbs:=by
 obtain ⟨C,hC,d⟩:= budget_leg true; obtain ⟨B,hB,b⟩:=budget_leg false; refine ⟨max C B,hC.trans_le (le_max_left ..),fun x k i=>?_⟩
 rcases le_total 0 i with h|h
 · specialize d x k i.natAbs; simp only [knee,if_true,Int.natCast_natAbs,h,abs_of_nonneg] at d; exact d.trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
 specialize b x k i.natAbs; simp only [knee,Bool.false_eq_true, ↓reduceIte, Int.natCast_natAbs,abs_of_nonpos h,norm_neg,neg_neg] at b; exact b.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
def embark (x:Facet3)(w:ℤ):=fourierCoeff (slopeG x) w
lemma dominates : ∃ C:ℝ,0<C∧∀ x∈grounds,∀ w:ℤ,‖embark x w‖ ≤ C * ρ^w.natAbs :=by
 obtain ⟨C,p,h⟩:= budget_neg; refine ⟨φ⁻¹ * C,by positivity,fun x e i=>?_⟩; rw [embark,printed,norm_mul,Complex.norm_of_nonneg (by positivity),mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); simpa using h x e (-i)
lemma bleeds {r:ℝ}(p: 0≤r)(v:r<1) : Summable (fun i:ℤ=> r^i.natAbs):=by
 exact Summable.of_nat_of_neg (by simpa only [Int.natAbs_natCast] using summable_geometric_of_lt_one p v) (by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using summable_geometric_of_lt_one p v)
lemma die : ρ< 1:= Real.exp_lt_one_iff.mpr (by norm_num)
lemma paint {x:Facet3}(p:x∈grounds)(w:roundC): HasSum (fun i:ℤ=> embark x i * fourier i w) (slopeG x w):=by
 obtain ⟨C,_,h⟩:= dominates; have hp:= (Summable.of_norm (Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (h x p) ((bleeds (Real.exp_pos _).le die).mul_left C))); exact has_pointwise_sum_fourier_series_of_summable (f:=⟨_,walksA x p⟩) hp w
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms walksA
#print axioms printed
#print axioms dominates
#print axioms paint
