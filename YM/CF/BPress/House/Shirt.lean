import YM.CF.BPress.House.Gloves
import YM.CF.BPress.Contour.Bumps
/- default vs excited. Same-pivot carve $Trainer = ∏ p ...$ . -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open RG Wilson Push.SectorMeasure MeasureTheory Measure LocalH Lattice Cube Bands Locale Wealth Net Grid Finset Function SU Mag Branch Port Weave Vesper Skye Hazel Reserve Filter Env
open scoped Classical Topology BigOperators YM.CF.BPress.Vesper ENNReal
variable {N:Side}{B:BandWidth}(A:Bands (More N) B)(R:Hangar (More N)) (y:ℝ)
variable (E: Seal (BlockY A R))
abbrev areaR : ℕ:=Fintype.card (BlockY A R)
def wool := (paysP (B:=B) R y)^(areaR A R)
def brass (i:BlockY A R):Set (Realm B N R):= if i∈E then (brisk R y)ᶜ else brisk R y
abbrev Ward:= Set.univ.pi (brass A R y E)
def innings (v:Choir A R):=univ.filter (fun i=> excite R y (v i))
lemma inning_eq (v:Choir A R) : v∈ Ward A R y E ↔ E=innings A R y v:=by
 rw [Ward,Set.mem_univ_pi,Finset.ext_iff]; refine forall_congr' fun i=>?_ ; by_cases h:i∈E <;> simp [h,brass,innings,excite] -- ext tune
lemma wardopen : MeasurableSet (Ward A R y E):= MeasurableSet.univ_pi fun i=> by unfold brass; split; exact (brisk_meas ..).compl; exact brisk_meas ..
abbrev exciting(i:BlockY A R):Measure (Realm B N R):= hotM R y
abbrev defaulting(i:BlockY A R):Measure (Realm B N R):= coldM R y -- unused
abbrev Century:= Contour.century (defaulting A R y) (exciting A R y) E
theorem ticketC : Century A R y E = ENNReal.ofReal ((paysP (B:=B) R y)⁻¹)^(areaR A R) • (trainer A R y).restrict (Ward A R y E):=by
 let K:= ENNReal.ofReal ((paysP (B:=B) R y)⁻¹); let T:= Training R B y; let P(i):= brass A R y E i; let u:= Contour.attend (defaulting A R y) (exciting A R y) E; have he(i): u i= K • T.restrict (P i):=by unfold u P brass Contour.attend; split <;> rfl
 haveI : ∀ i,IsFiniteMeasure (u i):=by intro i; unfold u Contour.attend; split <;> infer_instance
 haveI : IsFiniteMeasure T:=inferInstanceAs (IsFiniteMeasure (Training R B y)); change Measure.pi u = K^_ • (Measure.pi fun _=>T).restrict (Set.univ.pi P)
 rw [restrict_pi_pi (μ:=fun _=>T)]; apply Measure.pi_eq; intro s h; rw [Measure.smul_apply, Measure.pi_pi]; simp_rw [he,Measure.smul_apply,smul_eq_mul, prod_mul_distrib,prod_const, card_univ]; rfl -- tune
lemma payC (h:0<paysP (B:=B) R y) : (trainer A R y).restrict (Ward A R y E)= ENNReal.ofReal (wool A R y) • Century A R y E:=by
 rw [ticketC, smul_smul,wool, ←ENNReal.ofReal_pow (inv_pos.mpr h).le, ← ENNReal.ofReal_mul (pow_nonneg h.le _),←mul_pow, mul_inv_cancel₀ h.ne',one_pow,ENNReal.ofReal_one,one_smul]
-- ae. no $Fast$ requirement for barrel on knell.
def Precinct (p:mState N A):Prop := ToneNoise y p.2.2.1 ∧ Barrel A y p.2.1.1
def Potions (p:Choir A R):Prop:= Precinct A y (read A R p) ∧ p∈Ward A R y E
lemma ticket_ae : ∀ᵐ x∂ museum A y, Precinct A y x:=by
 let M:= museum A y; let μ:= count (Old A); let K:=knell A y; let S:=paleB y N; let P:=K.prod S
 refine Eventually.and ?_ ?_; · suffices Q:∀ᵐ x∂paleB y N,ToneNoise y x.1 from (quasiMeasurePreserving_snd (μ:=μ) (ν:=P)).tendsto_ae ((quasiMeasurePreserving_snd (μ:=K)).tendsto_ae Q); unfold paleB; refine quasiMeasurePreserving_fst.tendsto_ae (show ∀ᵐ x∂ Law.chain (Law.noise group (xi y)) (Link (More N)), ToneNoise y x from ?_); refine ae_all_iff.mpr fun i=>?_ ; exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Link (More N)=> Law.noise group (xi y)) (α:=fun _=> SU.E) (i:=i)).eventually (Law.noise_ae (G:=group) _)
 exact (quasiMeasurePreserving_snd (μ:=μ) (ν:=P)).tendsto_ae ((quasiMeasurePreserving_fst (μ:=K) (ν:=S)).tendsto_ae (barrel_ae A y)) -- tune P shadow
lemma potions (u:Fast y) : ∀ᵐ i∂ Century A R y E, Potions A R y E i:=by rw [ticketC]; exact Measure.ae_smul_measure ((ae_restrict_of_ae ((recipe A R u).quasiMeasurePreserving.tendsto_ae (ticket_ae A y))).and (ae_restrict_mem (wardopen ..))) _ -- tune projections
lemma regions (f:Choir A R→ℂ)(g:Envelope f)(h:0<paysP (B:=B) R y): (∫ x,f x∂trainer A R y)= wool A R y • ∑ E,∫ x,f x∂Century A R y E:=by
 let W:= Ward A R y; let V:= trainer A R y; let w:=wool A R y; have he(E): (∫ i,(W E).indicator f i∂V)= w • ∫ i,f i∂Century A R y E:=by
    rw [integral_indicator (wardopen ..)]; unfold V; rw [payC A R y E h,integral_smul_measure, ENNReal.toReal_ofReal (show 0≤wool A R y from pow_nonneg h.le _)]
 rw [Finset.smul_sum]; change _ = ∑ E:Seal (BlockY A R), w • ∫ x,f x∂Century A R y E; refine Eq.trans ?_ ((integral_finsetSum (univ:Finset (Seal (BlockY A R))) (fun i _=> show Integrable ((W i).indicator f) V from ((integrableX g (trainer A R y)).indicator (wardopen ..)))).trans (sum_congr rfl (show ∀ i∈ (univ:Finset _), (∫ u, (W i).indicator f u∂V)= _ from fun i _=> he i)))
 apply integral_congr_ae; apply Eventually.of_forall; intro x; simp only [W,Set.indicator, inning_eq,sum_ite_eq',mem_univ, ite_true] -- tune not prime
end YM.CF.BPress.House
