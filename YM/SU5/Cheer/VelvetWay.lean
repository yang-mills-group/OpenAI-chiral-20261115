import YM.SU5.Cheer.Flank
/-! # All timelike points reached. No parallel shell hits at operator-square scale. -/
set_option autoImplicit false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.Cheer
open Function Metric Set Filter Complex GaussianFourier MeasureTheory Measure Mink
open scoped Real Topology NNReal ENNReal InnerProductSpace BigOperators
local notation "η"=> (volume : Measure SpinP)
local notation "ξ"=> (volume : Measure SpinTrack)
variable (u v:SpinTrack)
lemma apex_cost : 0 ≤ time (apex u):= by rw [pierT]; exact add_nonneg (bill_p _) (bill_p _)
lemma apex_light : m (apex u)=0:=by unfold m; rw [pierT,pierS,rates,raw_u,raw_v,raw_q]; simp only [pearl_value,mul_re,mul_im,star_def,conj_re,conj_im]; ring
lemma duet_mass : m (Prom (u,v)) = 4* bill (u.1*v.2 - u.2*v.1):= by
 unfold m Prom; rw [Mink.clock_add,Mink.rest_add,pierT,pierT,pierS,pierS,rates]; simp only [PiLp.add_apply,raw_u,raw_v,raw_q,pearl_value,mul_re,mul_im,star_def,conj_re,conj_im,sub_re,sub_im]; ring
lemma lived : Prom (u,v) ∈ cone:= (cone_self _).mpr ⟨by rw [Prom,Mink.clock_add]; exact add_nonneg (apex_cost _) (apex_cost _),by rw [duet_mass]; exact mul_nonneg (by norm_num) (bill_p _)⟩
lemma vaulted (h:u.1*v.2 ≠ u.2*v.1): Prom (u,v)∈inside:= by
 have hp:0<m (Prom (u,v)):= by rw [duet_mass]; exact mul_pos (by norm_num) (bill_vis (sub_ne_zero.mpr h))
 have he: ‖spatial (Prom (u,v))‖ ≤ time _:= lived u v
 exact (show ‖spatial (Prom (u,v))‖ < time _ from lt_of_le_of_ne he fun x=>by unfold m at hp; rw [x,sub_self] at hp; exact lt_irrefl _ hp)
variable (r s:Pasture)
local notation "φ"=> footpath
private lemma ae_spin (x:ℂ): ∀ᵐ v ∂η,v≠x:= by exact (Set.countable_singleton _).ae_notMem _
private lemma ae_road : ∀ᵐ v ∂ξ,v.1≠0:=by
 refine (ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_const |>.isOpen_compl |>.measurableSet)).mpr ?_
 exact (ae_spin 0).mono fun i h=>ae_of_all _ fun _=> h
lemma way : (ξ) ≪ φ r:= withDensity_absolutelyContinuous' (crest_cont r |>.measurable.aemeasurable) (ae_road.mono fun i h=> (ENNReal.ofReal_pos.mpr (open_road r i h)).ne')
instance : (φ r).IsOpenPosMeasure where
 open_pos _ h hn:= fun e=> hn.elim (fun x hx=>(h.measure_ne_zero (μ:=ξ) ⟨x,hx⟩) (way r e)) -- tune
private lemma ae_cross (x:SpinTrack) (h:x.1≠0): ∀ᵐ y ∂ ξ,x.1*y.2≠x.2*y.1:= by
 refine (ae_prod_iff_ae_ae (isClosed_eq (by fun_prop) (by fun_prop)|>.isOpen_compl |>.measurableSet)).mpr (ae_of_all _ fun f=>?_)
 refine (ae_spin (x.1 ⁻¹ *(x.2*f))).mono (fun v H hp=>?_)
 apply H; change x.1*v=x.2*f at hp; rw [← hp,← mul_assoc,inv_mul_cancel₀ h,one_mul]
lemma strictly : ∀ᵐ x ∂ moving r s, x∈ inside:=by
 unfold moving; refine (ae_map_iff prom_cont.measurable.aemeasurable (show MeasurableSet {u|u∈inside} from open_inside.measurableSet)).mpr ?_
 refine (ae_prod_iff_ae_ae ((open_inside.preimage prom_cont).measurableSet)).mpr ?_
 exact (show ∀ᵐ v∂ footpath r,v.1≠0 from (withDensity_absolutelyContinuous (ξ) (crest r)).ae_le ae_road).mono fun i h => (withDensity_absolutelyContinuous (ξ) (crest s)).ae_le ((ae_cross i h).mono fun j k=> vaulted i j k) -- tune
-- Cholesky
local notation "Au" p:max=> spatial p 0
local notation "Av" p:max=> spatial p 1
local notation "Aq" p:max=> spatial p 2
lemma cholesky {p:E4} (h:p ∈ inside): ∃ x, Prom x=p:=by
 obtain ⟨hy,hm⟩:= (strict_self p).mp h; let t:= time p; let a:= Au p; let b:= Av p; let z:= Aq p
 have hd:t^2> a^2+b^2+z^2:= by rw [m,rates] at hm; exact sub_pos.mp hm
 have ht:0<t:=hy; let c:= (t+z)/2; have hc:0<c:=by unfold c; nlinarith [sq_nonneg a,sq_nonneg b]
 let r:=Real.sqrt c; have hr:0<r:=Real.sqrt_pos.mpr hc; have he:r^2=c:= Real.sq_sqrt hc.le
 let u:SpinP:=r; let v:SpinP:= ⟨a/(2*r), b/(2*r)⟩; have hu:bill u=c:=by rw [pearl_value]; simp only [u,ofReal_re,ofReal_im]; simpa using he
 have hv: bill v=(a^2+b^2)/(4*c):=by rw [pearl_value]; dsimp only [v]; rw [← he]; ring -- tune
 let x:= (t-z)/2-bill v; have hx:0 < x:=by
    refine sub_pos.mpr ?_; rw [hv]; apply (div_lt_iff₀ (by positivity : 0<4*c)).mpr; unfold c; nlinarith
 let w:SpinP:=Real.sqrt x; have hw:bill w=x:=by simp [pearl_value,w,Real.sq_sqrt hx.le]
 refine ⟨((u,v),(0,w)), ext_by ?_ ?_⟩
 · unfold Prom; rw [Mink.rest_add,pierS,pierS]; ext i; fin_cases i
   · change shoal (u,v) 0+shoal (0,w) 0=a; rw [raw_u,raw_u]; simp [u,v,mul_re]; field_simp
   · change shoal (u,v) 1+shoal (0,w) 1=b; rw [raw_v,raw_v]; simp [u,v,mul_im]; field_simp
   · change shoal (u,v) 2+shoal (0,w) 2=z; rw [raw_q,raw_q]; dsimp only; rw [hu,hw]; have hz:bill 0=0:=by simp [bill]
     rw [hz]; unfold x c; ring
 unfold Prom; rw [clock_add,pierT,pierT]; simp only [hu,hw]; have hz:bill 0=0:=by simp [bill]
 change c+bill v + (bill 0+x)= t; rw [hz]; unfold x c; ring
lemma all_inside {S:Set E4}(h:IsOpen S)(v:(inside∩S).Nonempty):0< moving r s S:= by
 rw [moving, Measure.map_apply prom_cont.measurable h.measurableSet]; obtain ⟨p,hp,z⟩:=v; obtain ⟨w,rfl⟩:= cholesky hp
 exact (h.preimage prom_cont).measure_pos _ ⟨w,z⟩
lemma moving_ne : moving r s≠0:= by
 have t:= all_inside r s isOpen_univ ⟨position 0 1,(by simp [inside]), mem_univ _⟩; intro w; rw [w] at t; simp at t
end YM.Cheer
#print axioms YM.Cheer.all_inside
#print axioms YM.Cheer.strictly
