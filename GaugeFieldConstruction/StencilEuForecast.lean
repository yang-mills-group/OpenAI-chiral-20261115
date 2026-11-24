import GaugeFieldConstruction.StencilForecast
import GaugeFieldConstruction.CloverSymmetryCovariant
import GaugeFieldConstruction.LucySphereL
/-!
# The labelled gauge symmetry information and full Eu Wick comparison for K/Jx.
 This file: J-vector. K price from its already witnessed Eu derivative formula.
 -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 14000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Ember Ember.Volumetric Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Boundary Finset Mink RawBank Cell FirstPackMars CloverRule
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff InnerProductSpace Classical
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable (U:SO)
local notation "κ" => parcelMars U.val
lemma rateLegE_st (i:Axis)(m:IdWitPV):ledger All three U (SpinSlot3 m i)=∑ j:Axis, (κ j i) • SpinSlot3 m j:=by
 let k(j:Axis):UF three:=(DeckF three).issue (ket j); let y:=Tag All three U
 have e:rhoF three U (k i)=∑ j:Axis,(κ j i) • k j:=by
    let A₀: (Axis →₀ ℂ) →ₗ[ℂ] UF three := (DeckF three).issue
    unfold k rhoF; rw [Angles.bOut]; change A₀ (Cell.bill U.val.val (ket i))= ∑ j:Axis, (κ j i) • A₀ (ket j); rw [Cell.bill,on_ket,map_sum]; simp_rw [map_smul]
 have t(w:UF three): y (FslotPV three m w)= FslotPV three m (rhoF three U w):=by
    letI : Subsingleton (UG three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
    letI : Subsingleton (UX three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
    apply Prod.ext; · rfl
    apply Prod.ext; · exact Subsingleton.elim ..
    refine Prod.ext (funext fun i=>?_) (funext fun i=>Subsingleton.elim ..)
    unfold y; rw [takeF, riseInPV, riseInPV]; change rhoF three U (if m=i then _ else 0)=_; split_ifs <;> simp
 change y (FslotPV three m (k i)) = _
 rw [t,e,map_sum]; simp_rw [map_smul]; rfl
lemma rateOneE_st : ledger All three U (one three)=one three:=by
    letI : Subsingleton (UG three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
    letI : Subsingleton (UX three):= inferInstanceAs (Subsingleton ↥(⊥:Submodule ℂ _))
    apply Prod.ext; · rfl
    apply Prod.ext; · exact Subsingleton.elim ..
    refine Prod.ext (funext fun i=>?_) (funext fun i=>Subsingleton.elim ..)
    change rhoF three U 0=0; simp
noncomputable def InkEForecast_st (R:Matrix Axis Axis ℂ):Module.End ℂ CogPV:= 1 + ∑ i:Axis,∑ j:Axis,(R j i - (if j=i then 1 else 0)) • WorkHPV i j
lemma rateClock_st : ledger All three U= InkEForecast_st (parcelMars U.val):=by
 apply lectPV
 · unfold InkEForecast_st; simp only [LinearMap.add_apply, LinearMap.sum_apply,LinearMap.smul_apply, WorkOnePV]; simp [rateOneE_st]
 intro m i; rw [rateLegE_st]; unfold InkEForecast_st; symm
 simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply, WorkPortPV, Module.End.one_apply]; rw [sum_eq_single i]
 · simp only[ite_true, sub_smul, sum_sub_distrib]; rw [show (∑ x: Axis,(if x=i then (1:ℂ) else 0) • SpinSlot3 m x)=SpinSlot3 m i from ?_]; abel
   rw [sum_eq_single i]; simp; · intro _ _ p; rw[if_neg p,zero_smul];
   simp
 · intro a _ p; simp [p]
 simp
lemma euVector_st (V:Axis →CogPV)(i:Axis)(H:looksVectorSt V): ledger All three U (V i)= ∑ j:Axis, (parcelMars U.val j i) • V j:=by
 rw [rateClock_st]; unfold InkEForecast_st; simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply, WorkVector_st _ H, Module.End.one_apply]; rw [sum_eq_single i]
 · simp only[ite_true, sub_smul, sum_sub_distrib]; rw [show (∑ x: Axis,(if x=i then (1:ℂ) else 0) • V x)=V i from ?_]; abel
   rw [sum_eq_single i]; simp; · intro _ _ p; rw[if_neg p,zero_smul];
   simp
 · intro a _ p; simp [p]
 simp
lemma coin_E_st (F:FreeName three)(x:CogPV) : F.c (ledger All three U x)= ledger All three U (F.c x):=by
 have H(a b:Axis)(x):F.c (FlagPV a b x)=FlagPV a b (F.c x):=by rw [FlagPV,LinearMap.sub_apply,LinearMap.sub_apply,map_sub,F.h]; rfl
 have V(i:Axis)(x): F.c (IronPV i x)=IronPV i (F.c x):=by simp only [IronPV,LinearMap.smul_apply,Module.End.mul_apply,map_smul,H]
 have payApplyPV(u:Bool)(K: Module.End ℂ CogPV)(x:CogPV): (pay u K) x=pay u (K x):=by cases u<;> rfl
 have G(i j:Axis)(x) : F.c (WorkHPV i j x)=WorkHPV i j (F.c x):=by
    simp only [WorkHPV,payApplyPV,Module.End.mul_apply]; cases ((Count.sw i j).flip i) <;>simp only [pay_false,pay_true,map_neg,F.h,V]
 rw [rateClock_st]; unfold InkEForecast_st; simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,map_sum,map_add,map_smul,G]; rfl
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat} (p:Ticket u C)
lemma arcE_st (x: CogPV) : compassPiMars p U (LowIncPV x)=LowIncPV (ledger All three U x):=by
 let F:=p.path.caller three; let A:=p.path.caller four
 have H(x:CogPV):A.c (LowIncPV x)= LowIncPV (F.c x):=by apply Calibration.inject four; rw [p.path.flight, LowFivePV,LowFivePV,p.path.flight]
 obtain ⟨z,rfl⟩:= F.c.surjective x; rw [← H z]; change compassPiMars _ _ (payFrame p _)=_; rw[journeyCharge, CloverSymmetry.lowCost]; change A.c _= _; rw [H,←coin_E_st]
#print axioms arcE_st
#print axioms rateClock_st
end YM.GaugeFieldConstruction.Stage
end
