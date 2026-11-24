import YM.SU5.FiniteGaugeData.Drachma.GammaM
import YM.SU5.FiniteGaugeData.Drachma.Pocket
import YM.CF.Corne.Vest
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 16000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Filter Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch
open Pressure Pressure.Tube Stores AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching PatchReads
open CF.Newt CF.Neige CF.Char Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad Work.F03
open SectorNext.Vacuum.FlatTree Next.SectorChange.Rows Push.SectorMeasure
open scoped Topology ContDiff BigOperators Matrix Classical InnerProductSpace Kronecker Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge} {S:StepData c f} {T:Tube G S}{p:Clip} {a A σ C Λ x:ℝ} {P Q:Bed}
local notation "λ₀" => S.kernel.penalty
variable (F : Forest S.ratio)
open CF.Forge CF.Appel CF.Reine CF.Corne CF.Cay Toffee Tame Sector
namespace Tokens
local notation "G5" => CF.SU.group
local notation "Δ" => Fintype.card
abbrev dozer (G:Gauge):ℝ:= Δ G.ColorIndex
abbrev ser (c:Side):ℝ:=Δ (Site c)
variable {R:ChartRatio G5}{β w ε:ℝ} {q:Clip} {a' A':ℝ}
def angular(f:Side)(R:ChartRatio G)(P:Bed)(β:ℝ):=3*ser f * coinV R β-dozer G/2* Real.log (chassis P f)
variable {T:Tube G5 S}(M:Monk G5 S)
abbrev billA (M:Monk G5 S)(T:Tube G5 S)(R:ChartRatio G5)(x w β:ℝ):= Real.log (prefactor S G5 β * (shotM R w β)^Δ M.park.Free) + arcD T x M
local notation "κ" => S.kernel.penalty
lemma entity_f(M: Monk G S): Δ M.park.Free= 3*Δ (Site f)+Δ (Site c):=by
 have h:= count_clear M.park; rw [Fintype.card_prod _ Axis] at h; have p: Δ Axis=4:=rfl; rw [p] at h; omega
lemma basis_bill (e:Floor P T.high f a A)(d:Floor Q q c a' A')(hp:0<a)(hq:0<a') (V:Matrix (LT f) (LT c) ℝ)(h:Inputs S V (P.metric.acts f) (Q.metric.acts c))(ht:T.up.Bounds T.high σ C Λ)(j:Attached P T.up)(u:S.patch.Branches S.kernel G5)(p:Bid.Sworn P f G5)(hs:LocalRatio R)(hw:0 < w)(htm: fray T.high σ C x<1)(hβ:0<β):
 angular f R P β- angular c R Q β -
   ((3*ser f+ser c)*(dozer G5 *Real.log (1 + fray T.high σ C x)- Real.log (point G5 w))+4*ser c* (Real.log (S.penaltyZ β G5)-(coinV R β-dozer G5/2*Real.log κ)))≤ billA M T R x w β:=by
 let κ':=M.park; let A:=M.k; let dG:=dozer G5; let v:=coinV R β; let μ:= fray T.high σ C x; let φ:= Real.log (jazz κ' P).det 
 have ht':= h; have hx:=fumes κ' h e.symmetric.1; have hz:= fumes_p κ' h e d hp hq
 have hl:φ= Real.log (chassis P f)+ (4*ser c)*Real.log κ - Real.log (chassis Q c):=by
    apply eq_sub_of_add_eq; have he':= congr_arg Real.log hx; rw [Real.log_mul (chassis_p e hp).ne' (pow_pos S.kernel.penalty_pos _|>.ne'),Real.log_mul hz.ne' (chassis_p d hq).ne', Real.log_pow, down_card] at he'; push_cast at he'; unfold φ ser; linarith only [he']
 have hh:= (strata M.park ht u e j p M.k hz htm).2.1; rw [Fintype.card_prod,entity_f M] at hh; push_cast at hh; unfold velo gearGG amigo at hh
 rw [det_submatrix_equiv_self] at hh; have ha : -(dG/2*φ+(3*ser f+ser c)*dG*Real.log (1+μ)) ≤ arcD T x M:=by
    unfold arcD; -- inspect kist definition
    change _≤ -(1/2:ℝ)*Real.log (baseX T x (bareStores S) M.park M.k 1).det; unfold dG φ κ' μ dozer ser; linarith only [hh]
 have hW:= point_p (G:=G5) hw; let s:= Next.SectorChange.spare R β; have ht:0<s:= spare_pos R hs hβ; let b:= Real.log (S.penaltyZ β G5)
 have hm: Real.log (prefactor S G5 β * (shotM R w β)^Δ M.park.Free) = -(4*ser c) * b + (3*ser f+ser c) * (v+ Real.log (point G5 w)):=by
    change Real.log (prefactor S G5 β * (s*point G5 w)^ Δ M.park.Free)=_; rw [Real.log_mul (prefactor_pos ..|>.ne') (by positivity), Real.log_pow, Real.log_mul ht.ne' hW.ne', prefactor, Real.log_pow, Real.log_inv, entity_f M, show Δ (Bond c)=Δ (Site c)*4 from (Fintype.card_prod ..).trans (by rfl)]; push_cast; unfold ser; dsimp only [s,v,coinV,b]; ring
 unfold angular billA; rw [hm]; rw [hl] at ha; dsimp only [v,dG,b,μ] at *; linarith only [ha]

-- three budgets independently: monitor x, actual β at this request, height w of truncated Gaussian from this same cylinder shop. large means with L,K,p,kernel fixed already.
lemma capsule (K:KernelChoices)(R:ChartRatio G5)(hs:LocalRatio R)(k:ℝ)(hk:0<k) (p:Clip)(σ C:ℝ)(hσ:0<σ):∃ t:ℝ,0<t ∧∀ {x β w:ℝ}, t≤x→t≤ w→t≤β →∀{P Q:Bed}{c f:Side}{S:StepData c f}{T:Tube G5 S},S.patch.Branches S.kernel G5→ ∀ M:Monk G5 S,T.high=p → S.kernel=K→∀{q:Clip} {a' A' a A Λ:ℝ},Floor P T.high f a A →Floor Q q c a' A'→0<a→0<a'→ ∀{V:Matrix (LT f) (LT c) ℝ},Inputs S V (P.metric.acts f) (Q.metric.acts c)→Attached P T.up→ T.up.Bounds T.high σ C Λ → Bid.Sworn P f G5 → angular f R P β - angular c R Q β- k*ser f ≤ billA M T R x w β:=by
 let ε:= k/12; have he:0<ε:=by positivity
 have ht:Tendsto (fun x=> dozer G5*Real.log (1+fray p σ C x)) atTop (𝓝 0):= by simpa using! (((tendsto_const_nhds (x:= (1:ℝ))).add (fray_F G5 σ hσ p C)).log (by norm_num)).const_mul (dozer G5)
 obtain ⟨t,hh⟩:=eventually_atTop.mp ((eventually_gt_atTop (1:ℝ)).and ((((noiseTag (K:=K) R hs ε he).and (ht.eventually (gt_mem_nhds he))).and ((report G5).eventually (lt_mem_nhds (neg_lt_zero.mpr he)))).and ((fray_F G5 σ hσ p C).eventually (gt_mem_nhds zero_lt_one))))
 refine ⟨t, zero_lt_one.trans (hh t le_rfl).1,?_⟩; intro x β w h1 h2 h3 P Q c f S T e M hm hz q a' A' a A Λ u v hg hU V i wX hv hC
 obtain ⟨-,⟨⟨-,hx⟩,-⟩,u'⟩:=hh x h1
 obtain ⟨ht,⟨-,hr⟩,-⟩:= hh w h2
 obtain ⟨ht',⟨⟨hb,-⟩,-⟩,-⟩:=hh β h3
 apply le_trans _ (basis_bill M u v hg hU V i hv wX e hC hs (zero_lt_one.trans ht) (hm.symm ▸ u') (zero_lt_one.trans ht'))
 rw [hm,hz]; have hz':= (abs_le.mp (hb c f S hz)).2; have hp:0≤ ser f:=Nat.cast_nonneg _; have hy:0 ≤ ser c:=Nat.cast_nonneg _; have H: ser c ≤ ser f:= Nat.cast_le.mpr (Fintype.card_le_of_injective S.ratio.embed (HasLeftInverse.injective ⟨_,S.ratio.embed_parent⟩)) -- tune
 apply sub_le_sub_left; change _ ≤ k*ser f; calc
    _ ≤ (3*ser f+ser c)*(ε- -ε)+ 4*ser c* ε:= add_le_add (mul_le_mul_of_nonneg_left (sub_le_sub hx.le hr.le) (by positivity)) (mul_le_mul_of_nonneg_left hz' (by positivity))
    _ ≤ (3*ser f+ser f)*(ε- -ε)+ 4*ser f* ε:=by gcongr; linarith
    _ = _:=by unfold ε; ring
end Tokens
end YM.SU5.FiniteGaugeData.Drachma
