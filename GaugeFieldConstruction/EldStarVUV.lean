import GaugeFieldConstruction.StyriaRel.YM.Fields.Spectrum
import GaugeFieldConstruction.VertigoΛL
/-!
 # Smeared spacelike price lies wholly in strictly-positive-energy ODDS
 -/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary
open MeasureTheory Set Filter Function Mink Spectral Complex
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {D:Register G} {S:Table D} {W:Surface S} (R: Wightman S) {s:S.RealSpin}{K:S.Rotation} (h:R.Realizes (W:=W) K s)
local notation "Ω" => R.operators.vacuum
local notation "Ol" => R.momentum
section
variable {P:Hilbert} (π:PVM P E4) {T:Set E4}
lemma PasLeavesVU (U:MeasurableSet T)(x:P)(e:π.region T x=0): π.region Tᶜ x=x:=by
 let y:= x-π.region Tᶜ x
 have h:π.region T y=0:=by rw [show y=_ from rfl,map_sub,e,← ContinuousLinearMap.comp_apply,π.joins U U.compl,inter_compl_self, π.none]; simp -- tune
 have ht:π.region Tᶜ y=0:= by rw [show y=_ from rfl,map_sub,π.idempotent U.compl]; exact sub_self ..
 have hp:π.diagonal y Set.univ=0:=by rw [← Set.union_compl_self T]; exact measure_union_null ((π.null_pair U _).2 h) ((π.null_pair U.compl _).2 ht)
 have ht:π.region univ y=0 :=(π.null_pair MeasurableSet.univ _).1 hp; rw [π.all] at ht; exact Eq.symm (sub_eq_zero.mp (show y=0 from ht))
end
include h
lemma HomeSectorVU (x:R.operators.H)(e:(Ol).region ({0}:Set E4) x=x): ∃ a:ℂ,a • Ω=x:=by
 apply h.unique
 intro y
 have m:MeasurableSet ({0}:Set E4):= measurableSet_singleton _
 have hp:∀ᵐ z∂(Ol).diagonal x, z=(0:E4):=by
    apply ae_iff.mpr; rw [show {a:E4|¬a=0}= ({0}:Set E4)ᶜ from rfl]
    apply ((Ol).null_pair m.compl _).2; conv_lhs => arg 2; rw [← e]
    rw [← ContinuousLinearMap.comp_apply,(Ol).joins m.compl m,compl_inter_self,(Ol).none]; rfl
 have hc: inner ℂ x (R.action.orbit.translation y x)= inner ℂ x x:=by
    rw [←h.spectral x y,show inner ℂ x x= charFun ((Ol).diagonal x) 0 from ?_, charFun_apply,charFun_apply]; exact integral_congr_ae (hp.mono (by rintro _ rfl; simp)) -- tune
    rw [h.spectral x 0,R.action.orbit.origin]; rfl
 have he:inner ℂ (R.action.orbit.translation y x) x= inner ℂ x x:=(inner_conj_symm _ x).symm.trans ((congrArg (starRingEnd ℂ) hc).trans (inner_conj_symm ..))
 apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp; rw [inner_sub_left,inner_sub_right,inner_sub_right,hc,he]; rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K, R.action.orbit.unitary]; ring
lemma VacuumδVU: (Ol).diagonal Ω= Measure.dirac 0:=by
 apply Measure.ext_of_charFun; ext1 y; rw [h.spectral, charFun_dirac]
 change inner ℂ Ω (R.action.V _ Ω)=_; rw [h.covariance.vacuum, inner_self_eq_norm_sq_to_K,h.total.norm]; simp
lemma FairStarVU (x: R.operators.H): (Ol).region {0} x = (inner ℂ Ω x) • Ω:=by
 let m:MeasurableSet ({0}:Set E4):= measurableSet_singleton _
 have he:(Ol).region {0} Ω=Ω:= by
    have ht:(Ol).region ({0}:Set E4)ᶜ Ω=0:=by apply ((Ol).null_pair m.compl _).1; rw [VacuumδVU R h]; simp -- tune
    simpa only [compl_compl] using PasLeavesVU Ol m.compl Ω ht
 obtain ⟨c,hc⟩:=HomeSectorVU R h _ ((Ol).idempotent m x)
 have hp:inner ℂ Ω x = inner ℂ Ω ((Ol).region ({0}:Set E4) x):=by
    conv_lhs => arg 2; rw [← he, ← (Ol).real m]
    rw [ContinuousLinearMap.adjoint_inner_left]
 rw [hp,←hc,inner_smul_right,inner_self_eq_norm_sq_to_K,h.total.norm]; simp
abbrev FlameVUV :Set E4:= {p|0<time p}
omit h in
lemma FuelExhaustVU : ({0}:Set E4)ᶜ∩FlameVUVᶜ⊆coneᶜ:=by
 intro p h u; have hz:‖spatial p‖≤ time p:= u; have hp:time p≤0:=le_of_not_gt h.2; have H:=norm_nonneg (spatial p)
 have hv:spatial p=0:= norm_le_zero_iff.mp (hz.trans hp); have hT:time p=0:= le_antisymm hp (H.trans hz); have ht: spatial (0:E4)=0:=rfl
 apply h.1; rw [← position_eta p,hv,hT,←ht]; exact position_eta 0 -- tune rewriting p in goals
lemma FullHeatVU (x:R.operators.H) (p:(Ol).region ({0}:Set E4) x=0):(Ol).region FlameVUV x=x:=by
 let m:MeasurableSet ({0}:Set E4):=measurableSet_singleton _; have a:MeasurableSet FlameVUV:=by exact (isOpen_lt (f:=fun _:E4=>(0:ℝ)) (g:=time) continuous_const (by fun_prop)).measurableSet
 have ht:(Ol).diagonal x coneᶜ=0:= by
    apply ((Ol).null_pair Mink.closed_cone.isOpen_compl.measurableSet _).2; rw [h.forward]; rfl
 have he:(Ol).region FlameVUVᶜ x=0:=by
    apply ((Ol).null_pair a.compl _).1
    refine measure_mono_null (t:=({0}:Set E4) ∪ (({0}:Set E4)ᶜ∩FlameVUVᶜ)) ?_ (measure_union_null (((Ol).null_pair m _).2 p) (measure_mono_null FuelExhaustVU ht))
    intro z v; by_cases e:z∈ ({0}:Set E4); exact Or.inl e; exact Or.inr ⟨e,v⟩
 simpa only[compl_compl] using PasLeavesVU Ol a.compl x he
abbrev ElanΛVU(x:R.operators.H):R.operators.H:=x - (inner ℂ Ω x) • Ω
lemma departureVU(x:R.operators.H): (Ol).region ({0}:Set E4) (ElanΛVU R x)=0:=by rw[ElanΛVU,map_sub,map_smul,FairStarVU R h, FairStarVU R h,inner_self_eq_norm_sq_to_K,h.total.norm]; simp
lemma levitatesVU(x:R.operators.H): (Ol).region FlameVUV (ElanΛVU R x)=ElanΛVU R x:= FullHeatVU R h _ (departureVU R h _)
#print axioms FairStarVU
#print axioms levitatesVU
end YM.NSF.Boundary
end
