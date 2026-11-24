import GaugeFieldConstruction.XangoQc
/-!
# Payment for generalized contour with shape height. Secular J all admissible
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8200
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Hulse
open Calibration Raw Cauchy LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Salam
open Floor Sailing Module
open scoped Topology BigOperators ContDiff Classical
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
local notation "l"=> UV five
variable {n : ℕ} {S:City} (Y:AreaQc S) (Z:∀ v:UV five,(∀ w (p:Foil),S.spot (other w) front v p.p=0)→v=0)
variable (N:NickleQc)(T:Bills)(J:placard (UV five))(H:∀ n (x:Fin n→l), Conserves (S.armed J x))(a:JetBillQc T) (m:ℕ)(L:Axis→ E4→ℝ)(p:∀ n:ℕ,TwistQc (T (n+1) 0) m L)(w:ℕ→ℝ)
variable (q:Tendsto (fun i=> (N.e i)^(3+m)*w i) atTop (𝓝 0))
variable {X:Type*}[AddCommGroup X][Module ℂ X](g:X→ₗ[ℂ] l)(A:l)
variable (R:∀ i j:Axis, BloomQc Y g A (J i j) w N)
noncomputable def CostSaleQc (r s:Axis)(i:InkQc)(x:E4)(n:ℕ):ℂ:= ArmentQc L r s x • BillQc Y i.toHintQc A (J r s) (N.e n • x)
include p H
lemma CathQc (i:InkQc)(x:ℕ)(h:RespectQc i.f (dockScaleQc (N.e x) (N.positive x)))(t:∀ y:E4,AnnulusQc (N.e x) y→∀ t∈tsupport i.f,LensQc y t∈conf (i.n+2)): HarvestQc S A J T i=
   ∑ r:Axis,∑ s:Axis,(N.e x)^(3+m) • ∫ z:E4, CostSaleQc Y N J L A r s i z x:=by
 unfold HarvestQc; rw [← ShadowQc i.h h _ (H _ _)]; apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _; rw [armed,tagged_cost,Y.price]; exact DonorsQc i.h _ h (p _) (DayQc Y i.toHintQc A (J r s)) (Y.reg ..) t -- tune
omit H
lemma ValidCostQc (i:InkQc)(x:ℕ)(t:∀ y:E4,AnnulusQc (N.e x) y→∀ t∈tsupport i.f,LensQc y t∈conf (i.n+2))(r s:Axis): Integrable (fun z:E4=>CostSaleQc Y N J L A r s i z x):=ShopsIntQc (N.positive x) (p _) (DayQc Y i.toHintQc A (J r s)) (Y.reg ..) t r s
include R q
lemma RevenueQc (I: Finset InkQc)(v: InkQc→ℂ)(K:∀ Q:X,∑ i∈I,v i* PenQc S g Q i=0) (r s:Axis) : Tendsto (fun n:ℕ=> ∑ i∈I,v i*((N.e n)^(3+m) • ∫ z:E4, CostSaleQc Y N J L A r s i z n)) atTop (𝓝 0):=by
 let E:= ArmentQc L r s; have hE:Integrable E:= (( (p 0).expense s).mul (b_sm _ DokiQc.d _).continuous).integrable_of_hasCompactSupport (HasCompactSupport.mul_left (show HasCompactSupport _ from (DokiQc.LED r).c)) -- tune
 obtain ⟨V,h,W⟩:=(R r s).fee I InkQc.toHintQc v K
 let C (I':ℕ):= N.e I'^(3+m); have h0(n):0 < C n:= pow_pos (N.positive n) _
 have hd(n:ℕ): (N.e n)^(3+m)= C n:= rfl
 refine squeeze_zero_norm' ?_ (show Tendsto (fun i=> (∫ y:E4, ‖E y‖) * V * (C i*w i)) atTop (𝓝 0) from (by simpa only[mul_zero] using q.const_mul ((∫ y:E4, ‖E y‖)*V)))
 filter_upwards [W, (eventually_all_finset I).mpr (fun i _=> fillAnnQc i.f N.e N.positive N.small)] with j u t
 let L (i:InkQc)(x:E4):=CostSaleQc Y N J L A r s i x j
 change ‖∑ i∈I,v i*((C j) • ∫ x,L i x)‖ ≤ _
 have wP(i:InkQc)(k:i∈I): Integrable (fun x:E4=>v i*L i x):=(ValidCostQc Y N T J m _ p A i j (t i k) r s).const_mul _
 let U (x:E4):= ∑ i∈I, v i*L i x
 have hU: Integrable U:= integrable_finsetSum _ (fun i k=> wP i k)
 have p(i:InkQc)(a:ℂ): v i*(C j • a)= C j • (v i*a):=mul_smul_comm ..
 simp_rw[p,← Finset.smul_sum, ← integral_const_mul]; rw [← integral_finsetSum _ wP,norm_smul]; rw [Real.norm_eq_abs,abs_of_nonneg (h0 _).le]
 let f(x:E4):= ∑ i∈I,v i*BillQc Y i.toHintQc A (J r s) (N.e j • x)
 have hΙ (x:E4): U x= E x • f x:=by
    unfold U L CostSaleQc f; rw[Finset.smul_sum]; apply Finset.sum_congr rfl; intro i k; exact mul_smul_comm ..
 have he :‖(∫ x,U x)‖ ≤ ∫ x:E4, ‖E x‖*(V*w j):=by
    apply (norm_integral_le_integral_norm _).trans; apply integral_mono_ae hU.norm (hE.norm.mul_const _); filter_upwards [PackfreeQc] with x z; rw [hΙ,norm_smul]
    by_cases r0:x∈tsupport E
    · apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); apply u (N.e j • x) (LevelQc _ (faultQc ?_) _ (N.positive j)) (GuildSmQc x z _ (N.positive _).ne'); apply cone _ _; exact tsupport_mul_subset_right r0
    rw[image_eq_zero_of_notMem_tsupport r0]; simp
 rw [integral_mul_const] at he; exact (mul_le_mul_of_nonneg_left he (h0 _).le).trans_eq (by ring)
include H a Z
lemma VentureQc [Module.Finite ℂ X](u:Injective g):∃ F:X, Reaches S J T A (g F):=by
 obtain ⟨F,h⟩:=prismDoseQc (PenQc S g) (PenSeenQc S Z g u) (HarvestQc S A J T) (fun I b W=>by
    let f(i:Axis)(j:Axis)(s:ℕ):=∑ x∈I,b x*((N.e s)^(3+m) • ∫ z:E4,CostSaleQc Y N J L A i j x z s)
    have h:Tendsto (fun x:ℕ=>∑ i:Axis,∑ j:Axis,f i j x) atTop (𝓝 0):= by simpa only [Finset.sum_const_zero] using! (tendsto_finsetSum Finset.univ (fun i _=> tendsto_finsetSum Finset.univ (fun j _=> RevenueQc Y N T J m L p w q g A R I b W i j)))
    apply tendsto_nhds_unique tendsto_const_nhds (h.congr' ?_); filter_upwards [(eventually_all_finset I).mpr (fun i _=> fillAnnQc i.f N.e N.positive N.small),(eventually_all_finset I).mpr (fun i _=> RespLateQc i.f N.e N.positive N.small)] with i p' v
    unfold f; refine Eq.trans (b:=∑ x∈I,b x*(∑ r:Axis,∑ s:Axis,(N.e i)^(3+m) • ∫ y:E4, CostSaleQc Y N J L A r s x y i)) ?_ (Finset.sum_congr rfl ?_); swap
    · exact fun x k=> (congr_arg (b x * ·) (CathQc Y N T J H m L p A x i (v x k) (p' x k))).symm
    simp_rw [Finset.mul_sum]; rw [Finset.sum_comm (s:=I) (t:=Finset.univ)]; apply Finset.sum_congr rfl; intro j _; rw[Finset.sum_comm])
 exact ⟨F,reachPayQc S T J A (g F) a (fun t=>h t)⟩
#print axioms VentureQc
end YM.GaugeFieldConstruction.Ember.Hulse
