import YM.SU5.FiniteGaugeData.Tower.Colophon
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
/-!
# Operator convergence across tori

Topology on the local transfer: uniform sup operation on all upper
periods/coefficient evaluations, simultaneously on the unit ball of all
lower test marks (nonseparable). No unselected TV claim.
-/
section chemistry
variable (n k₀:ℕ→ℕ)
variable (S:Finset Cover)
local notation "N"=> (tent Y H)
local notation "W" s:max=> wingspan Λ l s
local notation "ν" t:max=> tagWord S (t:Evens S).val
local notation "R" i:max=>block Y H s (n i) (k₀ i) S
local notation "χ"=> banner (W S) N

-- record the resulting election for COHERENCE use, all levels and widths
structure Cresc : Prop where
 prices(S:Finset Cover)(s:ℕ)(ε:ℝ):0< ε →∀ᶠ r:ℕ in atTop,∀ (t:Evens S)(q:Evens (W S)) (m:ℕ),r≤ m→∀ j,r≤ j→∀v:Purse S,(∀y, ‖v.val y‖≤1)→ ∀x:PairsC,
   let G(i:ℕ):=banner (W S) N (block Y H s (n i) (k₀ i) S (note N v.val (tagWord S t.val))) q x
   dist (G m) (G j)< ε

lemma perform (h:Tendsto n atTop atTop)(g:∀s,∀ᶠ i:ℕ in atTop,legalAt Y s (n i) (k₀ i)):∃ f:ℕ→ℕ, StrictMono f∧ Cresc Y H (n ∘ f) (k₀ ∘ f):=by obtain ⟨f,p,q⟩:=voted Y H n k₀ h g; exact ⟨f,p,⟨q⟩⟩

variable (D:Cresc Y H n k₀)
include D
lemma Cresc.cauchy_unit(ε:ℝ)(h:0<ε): ∀ᶠ r:ℕ in atTop,
 ∀ (m:ℕ), r≤ m→∀ i,r≤ i→∀ F:Family (tent Y H),InTest N true S false F→ pay F 1→ pay ((R m) F-(R i) F) ε:=by
 let Cj:ℝ:= (Fintype.card (Evens (W S)))
 let C₀:ℝ:=(Fintype.card (Evens S))
 have hC:0≤ Cj:=by unfold Cj; positivity
 have h₁:0≤ C₀:=by unfold C₀; positivity
 let e:= ε/((C₀+1)*(Cj+1)); have he:0<e:=by unfold e; positivity
 filter_upwards [D.prices S s e he] with r p m u i v F hf hx
 let G:=fun j:Evens S=> (⟨banner S N F j, banner_paid S N F j⟩:Purse S)
 have hz:F= ∑ j:Evens S,note N (G j).val (tagWord S j.val):=banner_pays S N hf
 let t(j:Evens S):= note N (G j).val (tagWord S j.val)
 have hp(j:Evens S): InTest N true S false (t j):= atoms_test Y H S j _
 have ht(q): (R q) F= ∑ j:Evens S,(R q) (t j):=by rw [hz,sum_scheme Y H s (n q) (k₀ q) _ _ (fun j _=> hp j)]
 have hm(j:Evens S): pay ((R m) (t j)-(R i) (t j)) (Cj*e):= by
    refine banner_rate (W S) N (InTest.subOp (booked ..) (booked ..)) (fun q x=> ?_)
    rw [banner_sub (W S) N (booked ..) (booked ..),←dist_eq_norm]; exact (p j q m u i v _ (fun x=> pay_banner S N hf hx j x) _).le
 intro z x
 rw [ht m,ht i,←sum_sub_distrib]; simp_rw [Finset.sum_apply]; refine ((norm_sum_le ..).trans (sum_le_sum fun i _=>hm i ..)).trans ?_
 rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change C₀*(Cj*e) ≤ _
 have hw: (C₀+1)*(Cj+1)*e=ε:=mul_div_cancel₀ ε (by positivity)
 nlinarith [mul_nonneg hC he.le,mul_nonneg h₁ he.le]

lemma Cresc.cauchy_prices(ε:ℝ)(h:0<ε): ∀ᶠ r:ℕ in atTop,
 ∀ (m:ℕ), r≤ m→∀ i,r≤ i→∀ F:Family (tent Y H),InTest N true S false F→∀ C:ℝ, pay F C→ pay ((R m) F-(R i) F) (ε*C):=by
 filter_upwards [D.cauchy_unit Y H s n k₀ S ε h] with r p m u i v F hf C hx
 rcases (pay_nonneg hx).eq_or_lt with e | e
 · have hw:F=0:=by
      funext n x; exact norm_eq_zero.mp (le_antisymm ((hx n x).trans e.ge) (norm_nonneg _))
   have he(j): (R j) (0:Family N)=0:=by simpa only [zero_smul] using scale_scheme Y H s (n j) (k₀ j) (S:=S) InTest.one (0:ℂ)
   rw [hw,he,he,sub_self,←e,mul_zero]; exact fun _ _=> norm_zero.le
 let a:ℂ:= (C:ℂ)⁻¹; have ha:‖a‖=C⁻¹:=by unfold a; rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg e.le]
 have hC: pay (a • F) 1:= by rw [←inv_mul_cancel₀ e.ne', ←ha]; exact pay_scale hx a
 intro n' x; have hp:=p m u i v _ (InTest.smul a hf) hC n' x
 simp only [scale_scheme Y H s (n m) (k₀ m) hf a, scale_scheme Y H s (n i) (k₀ i) hf a,←smul_sub,Pi.smul_apply,norm_smul,ha] at hp
 rw [mul_comm,← div_eq_mul_inv, div_le_iff₀ e] at hp; exact hp

-- Borel local-test closure can reconstruct the limiting Family from its
-- periodic operators determined on just one host sphere. Here we do directly
-- via annotation fees to ensure boundedness, Borel etc., and prove sup Cauchy
-- transfer, not just convergence layer-by-layer.
lemma Cresc.reaches {F:Family (tent Y H)}(hf:InTest N true S false F):∃ T:Family (tent Y H), InTest N true (W S) false T ∧
 ∀ ε:ℝ,0<ε→∀ᶠ r:ℕ in atTop,pay ((R r) F-T) ε:=by
 obtain ⟨C,h⟩:= Journey.valuation Y H hf; have hx : pay F C:= h; have hc:=pay_nonneg hx
 let z:= fun (q:Evens (W S))(x:PairsC) r=>banner (W S) N ((R r) F) q x
 have h'(r): InTest N true (W S) false ((R r) F):=booked Y H s (n r) (k₀ r) S F
 have hp(ε:ℝ)(p:0<ε):∀ᶠ r:ℕ in atTop,∀ m, r≤ m→∀ i, r≤ i→∀ q x,dist (z q x m) (z q x i)< ε:=by
    filter_upwards [D.cauchy_prices Y H s n k₀ S (ε/(C+1)) (by positivity)] with r P m u i v t x
    rw [dist_eq_norm]; unfold z; rw [←banner_sub (W S) N (h' _) (h' _)]
    apply lt_of_le_of_lt (pay_banner (W S) N (InTest.subOp (h' _) (h' _)) (P m u i v F hf C hx) t x)
    have he:ε/(C+1)*(C+1)=ε:=div_mul_cancel₀ _ (by positivity); nlinarith [div_pos p (show 0<C+1 from by positivity)]
 have he(q x): CauchySeq (z q x):=Metric.cauchySeq_iff.mpr fun ε p=> by obtain ⟨r,v⟩:= (hp ε p).exists; exact ⟨r,fun i a k b=>v _ a _ b ..⟩
 choose Z HZ using fun (q:Evens (W S)) x=>cauchySeq_tendsto_of_complete (he q x)
 have hZ(ε:ℝ)(p:0<ε):∀ᶠ r:ℕ in atTop,∀ t x, dist (z t x r) (Z t x) ≤ ε:=by
    filter_upwards [hp ε p] with r P t x
    apply le_of_tendsto (tendsto_const_nhds.dist (HZ t x)); exact (eventually_ge_atTop r).mono fun i t'=> (P _ (le_refl r) _ t' t x).le
 have hv(t):Coeff true (W S) (Z t):=by
    obtain ⟨r,p⟩:= (hZ 1 zero_lt_one).exists; obtain ⟨B,e⟩:= (banner_paid (W S) N ((R r) F) t).env.cost
    refine ⟨by simp,⟨measurable_of_tendsto_metrizable (fun r=> (banner_paid (W S) N ((R r) F) t).env.meas) (tendsto_pi_nhds.mpr (fun i=> HZ t i)),B+1,fun x=>?_⟩,?_⟩
    · have hp:(‖Z t x‖-‖z t x r‖)≤1:= (norm_sub_norm_le (Z t x) (z t x r)).trans (by rw [←dist_eq_norm,dist_comm]; exact p t x)
      specialize e x; change ‖z t x r‖≤B at e; linarith
    intro x y p q; exact tendsto_nhds_unique_of_eventuallyEq (HZ t x) (HZ t y) (Eventually.of_forall fun r=> (banner_paid (W S) N ((R r) F) t).locus _ _ p q)
 let a(t):Purse (W S):= ⟨Z t,hv t⟩
 refine ⟨compose (W S) N a,comp_test ..,fun ε p=>?_⟩
 let d:ℝ:= Fintype.card (Evens (W S)); have hd:0≤d:=by unfold d; positivity
 let δ:= ε/(d+1)
 have e:0<δ:=by unfold δ; positivity
 filter_upwards [hZ δ e] with r P t x
 have h₁:(R r) F= _:= banner_pays (W S) N (h' r)
 rw [h₁]; unfold compose; rw [←Finset.sum_sub_distrib]; simp_rw [Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>δ) ?_).trans ?_)
 · intro i _; simp_rw [Pi.sub_apply,note_v,←sub_smul]; rw [norm_smul]; refine (mul_le_of_le_one_right (norm_nonneg _) (chorus_size ..)).trans ?_
   rw [←dist_eq_norm]; exact P i _
 rw [sum_const,card_univ,nsmul_eq_mul]; change d*δ≤_; have hd':(d+1)*δ=ε:=mul_div_cancel₀ ε (by positivity); nlinarith

/-- Pull for supported arguments; leave on all others zero, since this is not
an extension to arbitrary nonsupported families on the cover. -/
noncomputable def destined (F:Family (tent Y H)):Family (tent Y H) := if h:InTest (tent Y H) true S false F then (Cresc.reaches Y H s n k₀ S D h).choose else 0
lemma attaches (F:Family (tent Y H)): InTest N true (W S) false (destined Y H s n k₀ S D F) := by
 unfold destined; split
 next v=>exact (Cresc.reaches Y H s n k₀ S D v).choose_spec.1
 next=>exact InTest.zero
lemma integrates (F:Family (tent Y H))(x:InTest N true S false F)(ε:ℝ)(h:0< ε): ∀ᶠ r:ℕ in atTop,pay ((R r) F-destined Y H s n k₀ S D F) ε:=by rw [destined,dif_pos x]; exact (Cresc.reaches Y H s n k₀ S D x).choose_spec.2 ε h
lemma Cresc.outfits(ε:ℝ)(h:0<ε):∀ᶠ r:ℕ in atTop, ∀ F:Family (tent Y H), InTest N true S false F→∀ C:ℝ,pay F C→ pay ((R r) F-destined Y H s n k₀ S D F) (ε*C):=by
 obtain ⟨r,p⟩:= (D.cauchy_prices Y H s n k₀ S ε h).exists
 filter_upwards [eventually_ge_atTop r] with j a F b C c u x
 let T:= destined Y H s n k₀ S D F; let Z(i:ℕ):=(R i) F u x
 have ht:Tendsto Z atTop (𝓝 (T u x)):=Metric.tendsto_nhds.mpr fun δ e=> ((integrates Y H s n k₀ S D F b _ (half_pos e)).mono fun r v=>by rw [dist_eq_norm]; exact (v u x).trans_lt (by linarith))
 apply le_of_tendsto (((tendsto_const_nhds (x:=Z j)).sub ht).norm)
 exact (eventually_ge_atTop r).mono fun i t=>p j a i t F b C c u x

end chemistry
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Cresc.outfits
