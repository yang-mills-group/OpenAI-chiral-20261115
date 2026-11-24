import YM.SU5.Reconstruction.AllGrades.Concert
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
open Reed (Fine think)
open Fock Pastry Tenant
namespace Garret
/-! Port Crescendo and Score: actual Odd expenditure. -/
section chemistry
variable (n k₀:ℕ→ℕ)
variable (S:Finset Cover)
local notation "N"=> (tent Y H)
local notation "W" s:max=> wingspan Λ l s
local notation "ν" t:max=> tagWord S (t:Odds S).val
local notation "R" i:max=>torchBlock Y H s (n i) (k₀ i) S
local notation "χ"=> flavor (W S) N

-- record the resulting election for COHERENCE use, all levels and widths
structure Tenure : Prop where
 prices(S:Finset Cover)(s:ℕ)(ε:ℝ):0< ε →∀ᶠ r:ℕ in atTop,∀ (t:Odds S)(q:Odds (W S)) (m:ℕ),r≤ m→∀ j,r≤ j→∀v:Purse S,(∀y, ‖v.val y‖≤1)→ ∀x:PairsC,
   let G(i:ℕ):=flavor (W S) N (torchBlock Y H s (n i) (k₀ i) S (note N v.val (tagWord S t.val))) q x
   dist (G m) (G j)< ε

lemma acquireT (h:Tendsto n atTop atTop)(g:∀s,∀ᶠ i:ℕ in atTop,legalAt Y s (n i) (k₀ i)):∃ f:ℕ→ℕ, StrictMono f∧ Tenure Y H (n ∘ f) (k₀ ∘ f):=by obtain ⟨f,p,q⟩:=optionO Y H n k₀ h g; exact ⟨f,p,⟨q⟩⟩

variable (D:Tenure Y H n k₀)
include D
lemma Tenure.cauchy_unit(ε:ℝ)(h:0<ε): ∀ᶠ r:ℕ in atTop,
 ∀ (m:ℕ), r≤ m→∀ i,r≤ i→∀ F:Family (tent Y H),InTest N true S true F→ pay F 1→ pay ((R m) F-(R i) F) ε:=by
 let Cj:ℝ:= (Fintype.card (Odds (W S)))
 let C₀:ℝ:=(Fintype.card (Odds S))
 have hC:0≤ Cj:=by unfold Cj; positivity
 have h₁:0≤ C₀:=by unfold C₀; positivity
 let e:= ε/((C₀+1)*(Cj+1)); have he:0<e:=by unfold e; positivity
 filter_upwards [D.prices S s e he] with r p m u i v F hf hx
 let G:=fun j:Odds S=> (⟨flavor S N F j, flavor_paid S N F j⟩:Purse S)
 have hz:F= ∑ j:Odds S,note N (G j).val (tagWord S j.val):=flavor_pays S N hf
 let t(j:Odds S):= note N (G j).val (tagWord S j.val)
 have hp(j:Odds S): InTest N true S true (t j):= atomO Y H S j _
 have ht(q): (R q) F= ∑ j:Odds S,(R q) (t j):=by rw [hz,sum_planGr Y H s (n q) (k₀ q) _ _ (fun j _=> hp j)]
 have hm(j:Odds S): pay ((R m) (t j)-(R i) (t j)) (Cj*e):= by
    refine flavor_rate (W S) N (InTest.subOp (tBook ..) (tBook ..)) (fun q x=> ?_)
    rw [flavor_sub (W S) N (tBook ..) (tBook ..),←dist_eq_norm]; exact (p j q m u i v _ (fun x=> pay_flavor S N hf hx j x) _).le
 intro z x
 rw [ht m,ht i,←sum_sub_distrib]; simp_rw [Finset.sum_apply]; refine ((norm_sum_le ..).trans (sum_le_sum fun i _=>hm i ..)).trans ?_
 rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change C₀*(Cj*e) ≤ _
 have hw: (C₀+1)*(Cj+1)*e=ε:=mul_div_cancel₀ ε (by positivity)
 nlinarith [mul_nonneg hC he.le,mul_nonneg h₁ he.le]

lemma Tenure.cauchy_prices(ε:ℝ)(h:0<ε): ∀ᶠ r:ℕ in atTop,
 ∀ (m:ℕ), r≤ m→∀ i,r≤ i→∀ F:Family (tent Y H),InTest N true S true F→∀ C:ℝ, pay F C→ pay ((R m) F-(R i) F) (ε*C):=by
 filter_upwards [D.cauchy_unit Y H s n k₀ S ε h] with r p m u i v F hf C hx
 rcases (pay_nonneg hx).eq_or_lt with e | e
 · have hw:F=0:=by
      funext n x; exact norm_eq_zero.mp (le_antisymm ((hx n x).trans e.ge) (norm_nonneg _))
   have he(j): (R j) (0:Family N)=0:=by simpa only [zero_smul] using scale_planGr Y H s (n j) (k₀ j) (S:=S) InTest.zero (0:ℂ)
   rw [hw,he,he,sub_self,←e,mul_zero]; exact fun _ _=> norm_zero.le
 let a:ℂ:= (C:ℂ)⁻¹; have ha:‖a‖=C⁻¹:=by unfold a; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg e.le]
 have hC: pay (a • F) 1:= by rw [←inv_mul_cancel₀ e.ne', ←ha]; exact pay_scale hx a
 intro n' x; have hp:=p m u i v _ (InTest.smul a hf) hC n' x
 simp only [scale_planGr Y H s (n m) (k₀ m) hf a, scale_planGr Y H s (n i) (k₀ i) hf a,←smul_sub,Pi.smul_apply,norm_smul,ha] at hp
 rw [mul_comm,← div_eq_mul_inv, div_le_iff₀ e] at hp; exact hp

-- Borel local-test closure can reconstruct the limiting Family from its
-- periodic operators determined on just one host sphere. Here we do directly
-- via annotation fees to ensure boundedness, Borel etc., and prove sup Cauchy
-- transfer, not just convergence layer-by-layer.
lemma Tenure.reaches {F:Family (tent Y H)}(hf:InTest N true S true F):∃ T:Family (tent Y H), InTest N true (W S) true T ∧
 ∀ ε:ℝ,0<ε→∀ᶠ r:ℕ in atTop,pay ((R r) F-T) ε:=by
 obtain ⟨C,h⟩:= Journey.valuation Y H hf; have hx : pay F C:= h; have hc:=pay_nonneg hx
 let z:= fun (q:Odds (W S))(x:PairsC) r=>flavor (W S) N ((R r) F) q x
 have h'(r): InTest N true (W S) true ((R r) F):=tBook Y H s (n r) (k₀ r) S F
 have hp(ε:ℝ)(p:0<ε):∀ᶠ r:ℕ in atTop,∀ m, r≤ m→∀ i, r≤ i→∀ q x,dist (z q x m) (z q x i)< ε:=by
    filter_upwards [D.cauchy_prices Y H s n k₀ S (ε/(C+1)) (by positivity)] with r P m u i v t x
    rw [dist_eq_norm]; unfold z; rw [←flavor_sub (W S) N (h' _) (h' _)]
    apply lt_of_le_of_lt (pay_flavor (W S) N (InTest.subOp (h' _) (h' _)) (P m u i v F hf C hx) t x)
    have he:ε/(C+1)*(C+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith [div_pos p (show 0<C+1 from by positivity)]
 have he(q x): CauchySeq (z q x):=Metric.cauchySeq_iff.mpr fun ε p=> by obtain ⟨r,v⟩:= (hp ε p).exists; exact ⟨r,fun i a k b=>v _ a _ b ..⟩
 choose Z HZ using fun (q:Odds (W S)) x=>cauchySeq_tendsto_of_complete (he q x)
 have hZ(ε:ℝ)(p:0<ε):∀ᶠ r:ℕ in atTop,∀ t x, dist (z t x r) (Z t x) ≤ ε:=by
    filter_upwards [hp ε p] with r P t x
    apply le_of_tendsto (tendsto_const_nhds.dist (HZ t x)); exact (eventually_ge_atTop r).mono fun i t'=> (P _ (le_refl r) _ t' t x).le
 have hv(t):Coeff true (W S) (Z t):=by
    obtain ⟨r,p⟩:= (hZ 1 zero_lt_one).exists; obtain ⟨B,e⟩:= (flavor_paid (W S) N ((R r) F) t).env.cost
    refine ⟨by simp,⟨measurable_of_tendsto_metrizable (fun r=> (flavor_paid (W S) N ((R r) F) t).env.meas) (tendsto_pi_nhds.mpr (fun i=> HZ t i)),B+1,fun x=>?_⟩,?_⟩
    · have hp:(‖Z t x‖-‖z t x r‖)≤1:= (norm_sub_norm_le (Z t x) (z t x r)).trans (by rw [←dist_eq_norm,dist_comm]; exact p t x)
      specialize e x; change ‖z t x r‖≤B at e; linarith
    intro x y p q; exact tendsto_nhds_unique_of_eventuallyEq (HZ t x) (HZ t y) (Eventually.of_forall fun r=> (flavor_paid (W S) N ((R r) F) t).locus _ _ p q)
 let a(t):Purse (W S):= ⟨Z t,hv t⟩
 refine ⟨composeO (W S) N a,compO_test ..,fun ε p=>?_⟩
 let d:ℝ:= Fintype.card (Odds (W S)); have hd:0≤d:=by unfold d; positivity
 let δ:= ε/(d+1)
 have e:0<δ:=by unfold δ; positivity
 filter_upwards [hZ δ e] with r P t x
 have h₁:(R r) F= _:= flavor_pays (W S) N (h' r)
 rw [h₁]; unfold composeO; rw [←Finset.sum_sub_distrib]; simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>δ) ?_).trans ?_)
 · intro i _; simp_rw [Pi.sub_apply,note_v,←sub_smul]; rw [norm_smul]; refine (mul_le_of_le_one_right (norm_nonneg _) (chorus_size ..)).trans ?_
   rw [←dist_eq_norm]; exact P i _
 rw [sum_const,card_univ,nsmul_eq_mul]; change d*δ≤_; have hd':(d+1)*δ=ε:=mul_div_cancel₀ ε (by positivity); nlinarith

/-- Pull for supported arguments; leave on all others zero, since this is not
an extension to arbitrary nonsupported families on the cover. -/
noncomputable def chooseTape (F:Family (tent Y H)):Family (tent Y H) := if h:InTest (tent Y H) true S true F then (Tenure.reaches Y H s n k₀ S D h).choose else 0
lemma pinsTape (F:Family (tent Y H)): InTest N true (W S) true (chooseTape Y H s n k₀ S D F) := by
 unfold chooseTape; split
 next v=>exact (Tenure.reaches Y H s n k₀ S D v).choose_spec.1
 next=>exact InTest.zero
lemma sendsTape (F:Family (tent Y H))(x:InTest N true S true F)(ε:ℝ)(h:0< ε): ∀ᶠ r:ℕ in atTop,pay ((R r) F-chooseTape Y H s n k₀ S D F) ε:=by rw [chooseTape,dif_pos x]; exact (Tenure.reaches Y H s n k₀ S D x).choose_spec.2 ε h
lemma Tenure.outfits(ε:ℝ)(h:0<ε):∀ᶠ r:ℕ in atTop, ∀ F:Family (tent Y H), InTest N true S true F→∀ C:ℝ,pay F C→ pay ((R r) F-chooseTape Y H s n k₀ S D F) (ε*C):=by
 obtain ⟨r,p⟩:= (D.cauchy_prices Y H s n k₀ S ε h).exists
 filter_upwards [eventually_ge_atTop r] with j a F b C c u x
 let T:= chooseTape Y H s n k₀ S D F; let Z(i:ℕ):=(R i) F u x
 have ht:Tendsto Z atTop (𝓝 (T u x)):=Metric.tendsto_nhds.mpr fun δ e=> ((sendsTape Y H s n k₀ S D F b _ (half_pos e)).mono fun r v=>by rw [dist_eq_norm]; exact (v u x).trans_lt (by linarith))
 apply le_of_tendsto (((tendsto_const_nhds (x:=Z j)).sub ht).norm)
 exact (eventually_ge_atTop r).mono fun i t=>p j a i t F b C c u x

end chemistry

section operator
variable (n k₀ : ℕ→ℕ)(D:Tenure Y H n k₀)
variable (S:Finset Cover)
local notation "T" F:max=> chooseTape Y H s n k₀ S D F
local notation "b" i:max F:max=> torchBlock Y H s (n i) (k₀ i) S F
local notation "W₀" => wingspan Λ l
local notation "Z₀"=>tent Y H

variable {F G:Family (tent Y H)}
include D
lemma ev_tape (x:InTest K true S true F)(m: Side)(v:Fields ((K).c m)):
 Tendsto (fun i:ℕ=> (b i F) m v) atTop (𝓝 ((T F) m v)):=Metric.tendsto_nhds.mpr fun ε p=> ((sendsTape Y H s n k₀ S D F x _ (half_pos p)).mono fun y v0=>by rw [dist_eq_norm]; exact (v0 m v).trans_lt (by linarith))
/-- uniformly bounded operations on the entire S; may vary input with the
read. Thresholds on i. -/
lemma doc_funded: ∃ A:ℝ, 0<A ∧ ∀ᶠ i:ℕ in atTop, ∀ (F:Family (tent Y H)),InTest K true S true F →∀ y:ℝ, pay F y → pay (T F) (A*y) ∧ pay (b i F) (A*y):=by
 -- by output_doc fleet budget for a fixed stage OR on arbitrary spectrum.
 -- uniform Op cost on transfer for all i via unit input decomposition and
 -- treating ineligible corner zero.
 let J:=Σ r:ℕ,Purse S × Odds (W₀ S)
 -- just use cauchy/outfits to reduce to cost of one eligible point; there even easier finite env? prove via menu for whole Ω.
 let I₀:={j:J//admittedStage Y H s n k₀ S j.1∧∀ x:PairsC,‖j.2.1.val x‖ ≤ 1}
 have he(t:I₀): legalAt Y s (n t.val.1) (k₀ t.val.1):=t.property.1.1
 have ht(t:I₀): Tivoli (W₀ S) ((K).c (momentm Y (n t.val.1) (s+1))):=t.property.1.2
 have hs(v:Odds S):= (output_doc Y H s S _ _ he v ht (fun j=>j.val.2.1) zero_le_one (fun i=> i.property.2) (fun i=>i.val.2.2)).budget
 choose l L ll using hs
 let A₀:=∑ v:Odds S,l v * Fintype.card (Odds (W₀ S)); have ha:0≤A₀:=sum_nonneg (fun i _=> mul_nonneg (L i) (by positivity))
 let A:= A₀+1; have hA:0<A:=by unfold A; positivity
 have hr(i:ℕ)(F:Family (tent Y H))(x:InTest K true S true F)(f:pay F 1): pay (b i F) A:=by
    let J(v:Odds S):= (⟨flavor S K F v,flavor_paid S K F v⟩:Purse S); let H'(v:Odds S)(j:Purse S):= note K j.val (tagWord S v.val)
    have hu(v):InTest K true S true (H' v (J v)):=atomO Y H S v _
    have hv:F=∑ v:Odds S,H' v (J v):= flavor_pays S K x
    have hw(v):pay (b i (H' v (J v))) (l v*Fintype.card (Odds (W₀ S))):=by
       rw [mul_comm]; refine flavor_rate (W₀ S) K (tBook ..) (fun j z=> ?_)
       have hz:∀ x, ‖(J v).val x‖≤1:=pay_flavor S K x f v
       by_cases p:admittedStage Y H s n k₀ S i
       · let idx:I₀:= ⟨⟨i,J v,j⟩,p,hz⟩; exact ll v idx z
       unfold H'; rw [torch_none Y H s n k₀ S v p (J v),flavor_zero,Pi.zero_apply,norm_zero]; exact L v
    intro m v; nth_rw 1 [hv,sum_planGr Y H s (n i) (k₀ i) (S:=S) univ (fun j=>H' j (J j)) (fun i _=>hu _)] -- S implicit!
    simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (fun j _=> hw j ..)).trans ?_); change A₀≤A; unfold A; linarith
 -- scale to any common y
 have hp(i:ℕ)(F:Family (tent Y H))(x:InTest K true S true F)(y:ℝ)(f:pay F y):pay (b i F) (A*y):=by
    rcases (pay_nonneg f).eq_or_lt with e | e
    · have hw:F=0:=by
         funext n x; exact norm_eq_zero.mp (le_antisymm ((f n x).trans e.ge) (norm_nonneg _))
      have he: (b i (0:Family K))=0:=by simpa only [zero_smul] using scale_planGr Y H s (n i) (k₀ i) (S:=S) InTest.zero (0:ℂ)
      rw [hw,he,←e,mul_zero]; exact fun _ _=> norm_zero.le
    let c:ℂ:= (y:ℂ)⁻¹; have hc:‖c‖=y⁻¹:=by unfold c; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg e.le]
    have hC: pay (c • F) 1:= by rw [←inv_mul_cancel₀ e.ne', ←hc]; exact pay_scale f c
    intro t u; have h:=hr i _ (InTest.smul c x) hC t u
    simp only [scale_planGr Y H s (n i) (k₀ i) x c,Pi.smul_apply,norm_smul,hc,mul_comm y⁻¹,←div_eq_mul_inv] at h
    exact (div_le_iff₀ e).mp h
 exact ⟨A,hA,Eventually.of_forall (fun i F x y f=>⟨fun m u=> le_of_tendsto (ev_tape Y H s n k₀ D S x m u).norm (Eventually.of_forall fun i=> hp i F x y f m u),hp i F x y f⟩)⟩

end operator
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.Tenure.outfits
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.doc_funded
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.acquireT
