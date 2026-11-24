import YM.CF.BProof.Pods.Motion

/- local weight spending of bad/clean indicators under excited (finite) measures,
retaining uniform-state constraint of paid. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods.Brick.Act
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden Pricing Contour
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "B_"=> Block Y m
local notation "G_"=> SU.group
variable (p:Solid y Y.short g.count.val)(b:Block Y m)(a t s:ℝ)
abbrev visit:= (prep Y g y p).ν b
abbrev costL (d:ℕ):ℝ:=2*10^(d^3)
lemma adh (S:Set (PadTotal Y g b)): (visit Y g y p b).real S≤2*(lawTotal Y g y b).real S:=by
 letI:= probTotal Y g y p.h; let u:=lawTotal Y g y b; let V:=(baseC Y g y b)ᶜ; have hp: (u.restrict V) S ≤ u S:= Measure.restrict_le_self S; simp only [visit,exc_def,reject,adj, measureReal_def,Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]; apply mul_le_mul _ (ENNReal.toReal_mono (measure_ne_top (lawTotal Y g y b) S) hp) ENNReal.toReal_nonneg (by norm_num); have hw: (1:ℝ)/2 ≤ (copper Y g y b).toReal:= site_bill Y g y b p; exact le_trans (inv_anti₀ (by norm_num) hw) (by norm_num) -- tune
lemma bulk_cost : (visit Y g y p b).real Set.univ≤costL g.count.val:=by
 apply (adh Y g y p b _).trans; apply mul_le_mul_of_nonneg_left _ (by norm_num); nth_rw 1 [show Set.univ= (Set.univ:Set (PadBits Y g b)) ×ˢ (Set.univ:Set (PadHall Y g b)) from Set.univ_prod_univ.symm]; -- tune
 haveI p':= probHall Y g y p.h b; haveI: IsFiniteMeasure (lawHall Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; haveI : SigmaFinite (lawHall Y g y b):= IsFiniteMeasure.toSigmaFinite _; haveI: SFinite (lawHall Y g y b):= instSFiniteOfSigmaFinite; unfold lawTotal milk; rw [measureReal_prod_prod, probReal_univ (μ:=lawHall Y g y b),mul_one]; exact relic_bill Y g b
-- peak debt
abbrev Fog(b:B_):Set (PadTotal Y g b):= Set.univ ×ˢ wake Y g b (pureTube Y g y b)ᶜ
lemma fog_m : MeasurableSet (Fog Y g y b):= MeasurableSet.univ.prod (wake_m Y g b _ ((pure_m ..).compl))
lemma billF : (visit Y g y p b).real (Fog Y g y b) ≤ costL g.count.val*cool Y g y:=by
 apply (adh Y g y p b _).trans; haveI p':= probHall Y g y p.h b; haveI: IsFiniteMeasure (lawHall Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; haveI : SigmaFinite (lawHall Y g y b):= IsFiniteMeasure.toSigmaFinite _; haveI: SFinite (lawHall Y g y b):= instSFiniteOfSigmaFinite
 unfold Fog lawTotal milk; rw [measureReal_prod_prod, wake_price Y g y p.h]; unfold costL; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul (relic_bill ..) (chill Y g y b p.v) measureReal_nonneg (by positivity)) (by norm_num)
def earnTag (x:PadTotal Y g b):Prop := ∃ i:Fin 5,x.1=virgin Y g b i
lemma earn_m : MeasurableSet {x|earnTag Y g b x}:= measurable_fst (Set.Countable.measurableSet (Set.to_countable {x|∃ i:Fin 5,x= virgin Y g b i}))
lemma earn_cost : (visit Y g y p b).real {x|earnTag Y g b x} ≤ 10:= by
 apply (adh Y g y p b _).trans; haveI p':= probHall Y g y p.h b; haveI: IsFiniteMeasure (lawHall Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; haveI : SigmaFinite (lawHall Y g y b):= IsFiniteMeasure.toSigmaFinite _; haveI: SFinite (lawHall Y g y b):= instSFiniteOfSigmaFinite
 let S:= ⋃ i:Fin 5,({virgin Y g b i}:Set _); unfold lawTotal milk; rw [show {x|earnTag Y g b x}= S×ˢ Set.univ from ?_,measureReal_prod_prod,relic,probReal_univ,mul_one]; swap; · ext i; simp [earnTag,S,eq_comm]
 have hx:= measureReal_iUnion_fintype_le (μ:= (Measure.count:Measure (PadBits Y g b))) (fun i:Fin 5=>({virgin Y g b i}:Set _)); have hg: Measure.count.real S≤5:=by simpa only [measureReal_def,Measure.count_singleton,sum_const, card_univ, Fintype.card_fin, ENNReal.toReal_one, nsmul_eq_mul, Nat.cast_ofNat,mul_one] using hx
 linarith
-- bad payment, choose exactly mode discount when severe. Suppress severity considered only block.
def sniff (x:PadTotal Y g b):= if SevereTag Y g b x then a-t else a
def prud (x:PadTotal Y g b) := if Fac Y g y b x then Real.exp (sniff Y g b a t x) else 0
def spare(x:PadTotal Y g b):= if earnTag Y g b x then Real.exp (-s) else 0
lemma sniffs_m : Envelope (sniff Y g b a t):= Envelope.piece (severe_m ..) (Envelope.const _) (Envelope.const _)
lemma prud_m : Envelope (prud Y g y b a t):= Envelope.piece (fac_m ..) ((sniffs_m Y g b a t).exp) (Envelope.const _)
lemma spare_m : Envelope (spare Y g b s):= Envelope.piece (earn_m ..) (Envelope.const _) (Envelope.const _)
lemma prud_p (x:PadTotal Y g b):0≤ prud Y g y b a t x:=by unfold prud; split; exact (Real.exp_pos _).le; exact le_rfl
lemma spare_p(x:PadTotal Y g b):0≤spare Y g b s x:=by unfold spare; split; exact (Real.exp_pos _).le; exact le_rfl
abbrev pocket(d:ℕ)(a t L:ℝ):=costL d*(Real.exp (a-t)+L*Real.exp a)
lemma prud_est : (∫ x,prud Y g y b a t x ∂visit Y g y p b) ≤ pocket g.count.val a t (cool Y g y):=by
 let w:=visit Y g y p b; letI: IsFiniteMeasure w:= (Contour.Pot.fin (prep Y g y p) b); let T:=Fog Y g y b; let f:=T.indicator (fun _=>Real.exp a); let c:= Real.exp (a-t); have hc(x:PadTotal Y g b):0≤f x:=by apply Set.indicator_nonneg (fun x _=> (Real.exp_pos _).le) -- tune
 have he(x):prud Y g y b a t x≤ c+f x:=by
    unfold prud sniff; split; next hp=>
       split; exact le_add_of_nonneg_right (hc _); rename_i v; rw [show f x =Real.exp a from Set.indicator_of_mem (show x∈T from ⟨Set.mem_univ _, Set.mem_univ _, hp.resolve_left v,Set.mem_univ _⟩) _]; exact le_add_of_nonneg_left (Real.exp_pos _).le
    exact add_nonneg (Real.exp_pos _).le (hc _)
 apply le_trans (integral_mono (Law.pay (ν:=w) (prud_m ..)) ((integrable_const _).add ((integrable_const _).indicator (fog_m Y g y b))) he); simp only [Pi.add_apply]; rw [integral_add (integrable_const _) ((integrable_const _).indicator (fog_m Y g y b)), integral_const,integral_indicator_const _ (fog_m Y g y b)]; simp_rw [smul_eq_mul]; unfold pocket; rw [mul_add,←mul_assoc]; -- tune sizes
 apply add_le_add; exact mul_le_mul_of_nonneg_right (bulk_cost Y g y p b) (Real.exp_pos _).le; exact mul_le_mul_of_nonneg_right (billF Y g y p b) (Real.exp_pos _).le
lemma spare_est : (∫ x,spare Y g b s x ∂visit Y g y p b) ≤ 10 * Real.exp (-s):=by
 let S : Set (PadTotal Y g b):={x|earnTag Y g b x}; rw [show spare Y g b s=S.indicator (fun _=> Real.exp (-s)) from funext fun x=>by by_cases h:x∈S; rw [Set.indicator_of_mem h]; exact if_pos h;
                                                                                                                                                       rw [Set.indicator_of_notMem h]; exact if_neg h, integral_indicator_const _ (earn_m Y g b),smul_eq_mul]; exact mul_le_mul_of_nonneg_right (earn_cost Y g y p b) (Real.exp_pos _).le
end YM.CF.BProof.Pods.Brick.Act
