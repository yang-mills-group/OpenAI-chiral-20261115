import YM.SU5.Voyager.Ripen
import Mathlib.Analysis.Analytic.Order
import Mathlib.MeasureTheory.Topology
/-! # every ray determines; 
 almost every position after cut has positive charge if ONE mark paid in a convex open room. -/
set_option autoImplicit false
noncomputable section
namespace YM.Caino
open Function Filter Set Metric NormedSpace Bornology Complex
open MeasureTheory Measure Boundary.Probe Boundary
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X]
variable (f:X→ℝ)(p x:X) (S:Set X)(h:IsOpen S)(c:Convex ℝ S)(q:p∈S)(mf:Measurable f)
variable (s: ∀ x∈S,∀ d:X, AnalyticAt ℝ (fun z:ℝ=> f (x+z • d)) 0)
local notation "y[" x "," r "]" => (p+(r:ℝ) • x)
include h c q s
lemma berry_path (p':f p≠0): ∀ᵐ t:ℝ, y[x,t]∈S→ f y[x,t]≠0:=by
 let y:ℝ→X:=fun t=>y[x,t]; let U:=y ⁻¹' S; let g:=f ∘ y; have hx : IsOpen U:=h.preimage (by unfold y; fun_prop); have ht:0∈U:=by change y 0∈ S; unfold y; simpa using q
 have hp:Convex ℝ U:=by
    intro a ha b hb u v p' v' t; change y _ ∈ S
    rw [show y (u • a+v • b)=u • y a+v • y b from (by unfold y; rw [smul_add,smul_add,smul_smul,smul_smul, add_smul]; simp only [smul_eq_mul]; have ht:= add_smul u v p; rw [t, one_smul] at ht; calc
      _ = (u • p+v • p) + ((u*a) • x+(v*b) • x) := congrArg (·+_) ht
      _ = _:= by abel)]; exact c ha hb p' v' t
 have hu:AnalyticOnNhd ℝ g U:=by
    intro z hz; let v:X:=y z; have hw:=s v hz x; let T:=fun q:ℝ=> q-z
    let w(t:ℝ):= f (v+t • x); have ht:AnalyticAt ℝ w (T z):= by rw [show T z=0 from sub_self _]; exact hw
    rw [show g=w∘T from (funext fun i=> by unfold g w v y T comp; simp only [sub_smul]; congr 1; abel)]; exact ht.comp (analyticAt_id.sub analyticAt_const)
 have hw:g 0≠0:=by change f (p+(0:ℝ) • x)≠0; simpa using p'
 have hv:g ⁻¹' {0}ᶜ∈ Filter.codiscreteWithin U:=hu.preimage_zero_mem_codiscreteWithin hw ht ⟨⟨0,ht⟩,hp.isPreconnected⟩
 exact (ae_restrict_iff' hx.measurableSet).1 (ae_restrict_le_codiscreteWithin (μ:=(volume:Measure ℝ)) hx.measurableSet hv) -- tune
include mf
lemma bloom_room (p':f p≠0): ∀ᵐ x∂(volume.restrict S), f x≠0:=by
 let Y(x:X)(t:ℝ):= y[x,t]; let P(x:X)(t:ℝ):Prop:= Y x t∈ S→ f (Y x t) ≠0
 have hw:∀ᵐ (t:ℝ),∀ᵐ x:X,P x t:= (ae_ae_comm ?_).1 (ae_of_all (α:=X) volume fun x=>berry_path f p x S h c q s p'); swap; ·
    let g: X ×ℝ→X:=uncurry Y; have hu:Continuous g:= continuous_const.add (continuous_snd.smul continuous_fst); exact MeasurableSet.imp (hu.measurable h.measurableSet) ((measurableSet_singleton (0:ℝ)).compl |> (mf.comp hu.measurable)) -- lemma
 obtain ⟨t,p₀,v⟩:= (hw.and (show ∀ᵐ t:ℝ, t≠0 from (by rw [ae_iff]; simp))).exists
 let W(x:X):= t⁻¹ • (x-p)
 have H:QuasiMeasurePreserving W volume volume := (quasiMeasurePreserving_smul (volume:Measure X) (inv_ne_zero v)).comp (show QuasiMeasurePreserving (fun x:X=> x-p) volume volume from (by simpa [sub_eq_add_neg] using (measurePreserving_add_right volume (-p)).quasiMeasurePreserving)) -- x-p definitional?
 apply (ae_restrict_iff' h.measurableSet).2; refine (H.ae p₀).mono ?_; intro x u w; have ht:Y (W x) t=x:=by unfold Y W; rw [smul_smul,mul_inv_cancel₀ v,one_smul]; abel
 rw [← ht]; exact u (ht.symm ▸ w)
omit h c q mf s
namespace Furnished
variable {μ:Measure X}{W:X→ℝ}(H:Furnished μ W)(t:∀ x∈ S,0<W x)
local notation "ρ"=> H.portrait
include H t
lemma blooming (h:IsOpen S) (c:Convex ℝ S)(b:μ S≠0): volume.restrict S ≪ μ.restrict S:=by
 rw [H.portLoc _ h.measurableSet t]; by_cases g:∃x∈ S,ρ x≠0
 · obtain ⟨p,u,v⟩:=g
   apply withDensity_absolutelyContinuous' (by have ht:= H.portrait_m; fun_prop)
   exact (bloom_room (ρ) p S h c u H.portrait_m (fun x hx d=> H.lush x d (t x hx)) v).mono fun x y=> ne_of_gt (ENNReal.ofReal_pos.mpr ((H.port_p x).lt_of_ne (Ne.symm y))) -- order args
 push Not at g; refine False.elim (b ?_); rw [← Measure.restrict_eq_zero,H.portLoc _ h.measurableSet t]; unfold chisels; refine (withDensity_eq_zero_iff ?_).2 ?_ -- tune
 · have ht:=H.portrait_m; fun_prop
 · filter_upwards [ae_restrict_mem (μ:=volume) h.measurableSet] with x hx; change ENNReal.ofReal (ρ x)=0; rw [g x hx]; simp
lemma allRoom (h:IsOpen S): μ.restrict S ≪ volume:= by rw [H.portLoc _ h.measurableSet t]; exact (withDensity_absolutelyContinuous ..).trans Measure.restrict_le_self.absolutelyContinuous -- tune
end Furnished
end YM.Caino
#print axioms YM.Caino.Furnished.blooming
#print axioms YM.Caino.Furnished.allRoom
