import SatinThinSegno

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
-- cost delivering of estimator. project P.f chosen globally and Ring as admissible from that f. For those parameters no conditioning on window marks. 
variable {b:ℝ}{δ:ℕ→ℝ}{κ:ℕ→ℕ}(K:lender A C f r v δ b κ P)(p:Plans j X f P)
local notation "τ" s:max=> P.flume j X s p
local notation "λξ" s:max i:max=>sharpCost P s i
local notation "πx" s:max=> frameOne (P.clockPlate f s X)
local notation "νx" s:max=> (P.visitOne s (P.clockPlate f s X)).val
local notation "Uξ"=> P.clockPlate f v X
local notation "X₀"=>P.vivid j f r v b (τ v) (τ r)
lemma illuminated {b z:ℝ}(p:f≤r)(q:r≤v)(g:Ferry P.run v (aK i) (bK i))(h:P.freightT v i (P.bookT i f r v (z*b) X)= gapMark Y (aK i) (bK i) b z p q (P.rootAt f (aK i) X)):
 P.freightT v i (P.planeCost j (P.bookT i f r v (z*b) X) (P.bookT i f r v (z*b) X))= P.wakes j f (aK i) (bK i) X p q b z:=by
 rw [P.shine ..,freightT,planeCost,(distribute_arith Y H v (aK i) _ _ 0).2.1,(distribute_arith Y H v (aK i) _ 0 0).2.2.2.2]; unfold freightT at h; rw [h]; exact g.depth; exact g.enters -- .. ambiguity
-- bound absolutely independent i along history
lemma field_train_price (f r v:ℕ) :∃ U:ℝ,∀ᶠ i in atTop,∀ b:ℝ, P.cradle r v b→ pay (P.bookT i f r v b X) U:=by
 let h:= P.projection.history; let u(v):= P.visitOne v (P.clockPlate f v X); let S(v):=frameOne (P.clockPlate f v X); have he(v):InTest W true (S v) false (u v).val:=P.basesT; obtain ⟨U,p⟩:= Journey.valuation Y H (he v); obtain ⟨T,q⟩:=Journey.valuation Y H (he r); obtain ⟨A,p',e⟩:= fares Y H r h (S r) (v-r);
 let V':ℝ:=2*fareMax L (v-r); let z:= zoomM L^(r-f); refine ⟨‖(z:ℂ)‖*(V'*U+A*T),?_⟩; filter_upwards [e 1 zero_lt_one] with i t b hb; let T':= P.coastT r v i (S r) ((u r).val); apply pay_scale (z:= (z:ℂ)) (pay_sub (A:=V'*U) ?_ (show pay T' (A*T) from (t _ (he r) T q).2.1)); have hp: 0≤U:= Tower.pay_nonneg («F»:=(u v).val) p; intro a V
 exact (pay_scale (show pay ((u v).val) U from p) (b:ℂ) a V).trans (mul_le_mul_of_nonneg_right ((le_of_eq (show ‖(b:ℂ)‖=|b| by simp [Real.norm_eq_abs])).trans hb.1) hp)
include K p
lemma erg_count (G:P.repeatBill (twiceT X j) f)(O:P.NightCop): ∀ᶠ i in atTop, ‖P.voter j i f r v X (δ i)‖ ≤ 3*owedF P.par f A 2:=by
 let D:= P.bookT; obtain ⟨B,hb⟩:=P.field_train_price X f r v; have he:=P.history.finance v; have hf:= K.treasury.price.le; have hx:= K.treasury.step
 filter_upwards [hb, K.pays, K.treasury.room, he, P.plan_clock (A:=A) (C:=C) j X p hf hx G O (B*B), P.touring_fee X hf hx] with i q g h s c f'
 obtain ⟨v',z,t,x,b,p'⟩:= g.2; let w:= D i f r v (δ i) X; let W':= P.planeCost j w w; let I':= P.nomadic i; let K':= P.engine i; let E:=P.wakes j f (P.nomadic i) (P.engine i) X hf hx v' z
 have hv: P.freightT v i W'= E:=by unfold W' w D E; rw [p']; exact P.illuminated j X hf hx s (f' ..)
 have hP:pay w B:= q _ g.1; change ‖Journey.compass Y I' K' v (P.freightT v i W')‖ ≤_; rw [hv]; exact c v' z t h.2 b (by change ∀ x:Fields (side Y I' v), ‖E x‖≤_; rw [←hv]; exact P.plotted_cost W' (show pay W' (B*B) from pay_mul (pay_flips W hP j 0) hP) i)
lemma vision (G:P.repeatBill (twiceT X j) f)(O:P.NightCop): ‖X₀‖^2≤3*owedF P.par f A 2:=by
 let Z:= X₀; have ht:= (P.thread_count j X K p).norm
 have hz: ‖inner ℂ Z Z‖≤3*owedF P.par f A 2:= le_of_tendsto ht (K.earn.tendsto_atTop.eventually (P.erg_count j X K p G O)); rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hz; exact hz
omit K p
local notation "Φ"=> P.history.circuit
variable (q:r ≤ v)
abbrev cameo (b:ℝ)(_hf:f ≤ r)(q:r≤v) (g:Plans j X f P): P.Vox j v:= (↑(zoomM P.par.R.L^(r-f)):ℂ) • ((b:ℂ) • P.flume j X v g-Raise P.run P.large P.history.circuit j 0 false r v q (P.flume j X r g))
variable (hf:f≤r)
include p
lemma into_vivid : P.piece j v (P.cameo j X b hf q p)= X₀:=by
 let a(s:ℕ):= arrows Y H P.law Φ j 0 false (P.room j) s; unfold cameo; change a v _= _; rw [map_smul,map_sub,map_smul, show (a v) (Raise ..)=(a r) (τ r) from join_actor Y H P.law Φ j 0 false (P.room j) r v q _]; rfl
-- election: lower valued in P.L^2(P.pillars...) compare.
abbrev compared_state (K':ℝ)(x:P.Spectrum0 j):= (P.stateVox j x v (P.cameo j X K' hf q p))
lemma state_moving (u:ℝ)(x:P.Spectrum0 j): P.compared_state j X p q hf u x= (↑(zoomM P.par.R.L^(r-f)):ℂ) • ((u:ℂ) • P.stateVox j x v (τ v)- P.stateVox j x r (τ r)):=by
 unfold compared_state cameo; let a:= P.stateVoxLinear j x v; change a _= (↑(zoomM L^(r-f)):ℂ) • ((u:ℂ) • a _- _); rw [map_smul,map_sub,map_smul]; rw [show a _= _ from (show a (Raise Y H Φ j 0 false r v q (τ r))= P.stateVox j x r (τ r) from P.refine_vox j x r v q _)]; try rfl
omit p
lemma heartfelt (y:P.Vox j v): (∫ x:P.Spectrum0 j,‖P.stateVox j x v y‖^2∂(P.pillars j))=‖P.piece j v y‖^2:=by
 let S:=P.voxTest j v y; let T:=P.reflectTest j S*S; let U:= P.reading j v T; apply Complex.ofReal_injective
 refine ((integral_ofReal (𝕜:=ℂ) («μ»:=P.pillars j) (f:=fun x=>‖P.stateVox j x v y‖^2)).symm.trans ?_); change (∫ x:P.Spectrum0 j, ((‖P.stateVox j x v y‖^2:ℝ):ℂ) ∂(P.pillars j))=_; rw [Complex.ofReal_pow]; change _=(((‖P.piece j v y‖:ℝ):ℂ))^2; rw [← show inner ℂ (P.piece j v y) (P.piece j v y)=((↑‖P.piece j v y‖):ℂ)^2 from inner_self_eq_norm_sq_to_K _, P.seed_pairing]
 have he(x:P.Spectrum0 j): ((‖P.stateVox j x v y‖^2:ℝ):ℂ)= P.chi j x U:=by rw [Complex.ofReal_pow,← show inner ℂ (P.stateVox j x v y) (P.stateVox j x v y)=((↑‖P.stateVox j x v y‖):ℂ)^2 from inner_self_eq_norm_sq_to_K _]; exact P.gram_at j x v y y
 simp_rw [he]; exact (P.recovery j U).trans (P.occupied j v T)
lemma state_cont_cost (y:P.Vox j v): Continuous (fun x:P.Spectrum0 j=> ‖P.stateVox j x v y‖^2):=by
 let T:= P.voxTest j v y; let Q':= P.reading j v (P.reflectTest j T*T); have he(x:P.Spectrum0 j): ‖P.stateVox j x v y‖^2= ‖P.chi j x Q'‖:=by change _= ‖P.singleState j v x (P.reflectTest j (P.voxTest j v y)*P.voxTest j v y)‖; rw [← P.gram_at, inner_self_eq_norm_sq_to_K, norm_pow,RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
 simp_rw [he]; exact (P.chi_joint j Q').norm
include K
include p
lemma caucus (G:P.repeatBill (twiceT X j) f)(O:P.NightCop): (∫ x:P.Spectrum0 j, ‖P.compared_state j X p q hf b x‖^2∂(P.pillars j))≤3*owedF P.par f A 2:=by
 unfold compared_state; rw [P.heartfelt,P.into_vivid]; exact P.vision j X K p G O
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.caucus
