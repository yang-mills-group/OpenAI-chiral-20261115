import YM.CF.BProof.Pods.Camp
import YM.CF.BProof.Pricing.Ease
import YM.CF.BProof.Pods.Polar

/- strike probability lower and rawbad tail. columns ≤ L_c^3 at each Λ block. density
count normalization kept exactly. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Pods.Brick
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden Pricing
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "s"=> More N
local notation "B"=> Block Y m
local notation "G"=> SU.group
variable (h:xi y≤1)(b:Block Y m)
abbrev Ports:= Fiber (hide Y g)
lemma seats : Fintype.card (Ports Y g b)≤ g.count.val^3:=by
 convert! height Y g b; exact Fintype.card_subtype _ -- tune
abbrev Static:= ∀ i:B,PadTotal Y g i
def virgin (k:Fin 5) : PadBits Y g b:= (fun _=>k,fun _=> false)
abbrev pureTube : Set (PadTube Y g b):= Set.univ.pi (fun _=>(Day.peak (rawQ y))ᶜ)
abbrev wake(T: Set (PadTube Y g b)): Set (PadHall Y g b):= Set.univ ×ˢ (T ×ˢ Set.univ)
def baseC : Set (PadTotal Y g b):= {virgin Y g b 0} ×ˢ wake Y g b (pureTube Y g y b)
lemma pure_m : MeasurableSet (pureTube Y g y b):= MeasurableSet.univ_pi (fun i=> (Day.peak_m _).compl)
lemma wake_m(T: Set (PadTube Y g b))(p:MeasurableSet T) :MeasurableSet (wake Y g b T):= MeasurableSet.univ.prod (p.prod MeasurableSet.univ)
lemma base_m : MeasurableSet (baseC Y g y b):= (measurableSet_singleton _).prod (wake_m _ _ _ _ (pure_m ..))
-- weight of counting variables in excited part. Any even? no.
lemma relic : lawBits Y g b=Measure.count:=by
 apply Measure.ext_of_singleton; intro i; unfold lawBits milk; conv_lhs=> rw [show {i}={i.1} ×ˢ ({i.2} : Set (PadBit Y g b)) from (by rw [Set.singleton_prod_singleton])]
 rw [Measure.prod_prod]; -- singleton product def?
 simp only [lawKey,lawBit, Measure.count_singleton]; unfold pool; erw [count_pi (X:=fun _: Ports Y g b=> Fin 5), count_pi (X:=fun _ : Ports Y g b=> Bool)]; simp
lemma relic_bill: (lawBits Y g b).real Set.univ≤(10:ℝ)^ (g.count.val^3):=by
 rw [relic Y g b,cost_measure]; unfold PadKey PadBit Pad; rw [Fintype.card_prod]; simp only [Fintype.card_bool,Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow, Nat.cast_ofNat]; rw [← mul_pow,show (5:ℝ)* 2=10 from by norm_num]; exact pow_le_pow_right₀ (by norm_num) (seats Y g b)
abbrev cool := raw_bill Y.short y * (g.count.val^3:ℕ)
lemma chill (v:1≤hot.trunc y): (lawTube Y g y b).real (pureTube Y g y b)ᶜ ≤ cool Y g y:= by
 let T':=hot.trunc y; let μ:=lawTube Y g y b; let T:= Roll.Place Y; let w:=Day.mark T' T; let P:=Day.peak (I:=T) (rawQ y); let U:= PadTube Y g b
 have he:(pureTube Y g y b)ᶜ=⋃ i:Ports Y g b,Function.eval i ⁻¹' P:=by ext x; simp [pureTube, P, Set.mem_pi, Function.eval] -- tune family eval inferred?
 let R:=raw_bill Y.short y
 haveI: IsProbabilityMeasure w:=Day.prob _ _ (one_pos.trans_le v)
 letI: IsProbabilityMeasure (Day.mark T' T):= ‹IsProbabilityMeasure w›
 have hh: w.real P≤R:=Day.tariff _ _ v -- args?
 rw [he]; have hs(i:Ports Y g b):μ.real (Function.eval i ⁻¹' P)=w.real P:=by
    have hf:MeasurePreserving (Function.eval i) μ w:= measurePreserving_eval (fun _=>w) i; rw [measureReal_def,measureReal_def,hf.measure_preimage (Day.peak_m _).nullMeasurableSet]
 apply le_trans (measureReal_iUnion_fintype_le (μ:=μ) _) -- tune takes summable
 change ∑ i: Ports Y g b,μ.real (Function.eval i ⁻¹' P) ≤ _; simp_rw [hs]; rw [Finset.sum_const,card_univ,nsmul_eq_mul]; unfold cool; rw [mul_comm (raw_bill Y.short y)]; apply mul_le_mul (Nat.cast_le.mpr (seats Y g b)) hh measureReal_nonneg (by positivity)
-- possibly orientation
structure Solid (y:ℝ)(d k:ℕ): Prop where
  h : xi y≤1
  v : 1≤hot.trunc y
  price : raw_bill d y * (k^3:ℕ) ≤ 1/2
include h
lemma wake_price (T:Set (PadTube Y g b)) : (lawHall Y g y b).real (wake Y g b T)=(lawTube Y g y b).real T:=by
 letI:=probStream Y g y h; letI:=probBook Y g y h; letI PStream: IsFiniteMeasure (lawStream Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; letI PStream1:SigmaFinite (lawStream Y g y b):= IsFiniteMeasure.toSigmaFinite _; letI PStream2: SFinite (lawStream Y g y b):= instSFiniteOfSigmaFinite; letI PBook: IsFiniteMeasure (lawBook Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; letI PBook1:SigmaFinite (lawBook Y g y b):= IsFiniteMeasure.toSigmaFinite _; letI PBook2: SFinite (lawBook Y g y b):= instSFiniteOfSigmaFinite; unfold lawHall wake milk; rw [measureReal_prod_prod,probReal_univ,one_mul]; unfold lawStream milk; rw [measureReal_prod_prod,probReal_univ,mul_one]
def copper := siteP _ (lawTotal Y g y) (baseC Y g y)
lemma siteP_def : (copper Y g y b).toReal= (lawTube Y g y b).real (pureTube Y g y b):=by
 letI ph:= probHall Y g y h; letI pv(i:B): IsFiniteMeasure (lawHall Y g y i):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; letI ps(i:B):SigmaFinite (lawHall Y g y i):= IsFiniteMeasure.toSigmaFinite _; letI PHall: IsFiniteMeasure (lawHall Y g y b):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _; letI PHall1:SigmaFinite (lawHall Y g y b):= IsFiniteMeasure.toSigmaFinite _; letI PHall2: SFinite (lawHall Y g y b):= instSFiniteOfSigmaFinite
 change (lawTotal Y g y b).real _=_; unfold lawTotal milk baseC; rw [measureReal_prod_prod,relic,wake_price _ _ _ h]; simp [measureReal_def]
omit h
variable (k:Solid y Y.short g.count.val)
include k
lemma site_bill : (1:ℝ)/2 ≤ (copper Y g y b).toReal := by
 rw [siteP_def _ _ _ k.h]; have ht:=(chill Y g y b k.v).trans k.price; rw [measureReal_compl (pure_m Y g y b),probReal_univ] at ht; linarith
lemma dawning : Dayway _ (lawTotal Y g y) (baseC Y g y) := fun i=> ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le (by norm_num) (site_bill _ _ _ i k))|>.1
end YM.CF.BProof.Pods.Brick
