import YM.SU5.FiniteGaugeData.Signal.Attestation
/-! # Keep THIS witness below same-state limit.

One lease for first Loom & orbit in matched law, spend supporting Price on LEGACY paths
and nested limits. `Effect` intrinsic mean promise at native scale for this state, not
saying yet that it's more than a function of vacuum in continuation or that it extends to
translation-covariant final continuum. Width effects? Uniform actual native width INCLUDING
chosen level, for all s high enough. May pick s before doing any proving.
 -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Ovation
variable {P:Preparation}{k' d q r Ul b kd l':ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l'))(H:Real.exp 1 ≤ P.x){g C Ω z a:ℝ}
variable {i k:ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E':ℕ→Buffered.Family (tent Y H)→ℂ}
local notation "Λ"=> tent Y H
variable (s:ℕ){o: Cover}
local notation "U★"=> (SculptureBirth P g k')
local notation "Ur"=> (high P Ul d)
local notation "ν₀" n:max=> momentm Y n s
local notation "C₀" n:max=> side Y n s
local notation "Z'"=> (gaugePrice P (Course.fullTariff P g))
local notation "S★"=> selection o r k'
local notation "a★"=> atomPay (selection o r k').toList
local notation "V★"=> castle (nodeC o) (high P Ul d+4)
local notation "T·" l:max=> apart (nodeC o) Ul l
variable {Q:Playhouse P l'}(W:Traced Y H i k I E' Q)
variable {S T:Finset Cover} {L:List Cover}
lemma afterThaw (z a:ℝ)(u:0<a)(v:0<z): ∀ᶠ d0:ℕ in atTop,∀ n:ℕ,∀ t:(Y.voyage n).kick ≤ d0,Ferry Y s n d0∧ ∀ f,Envelope f→ (∀ i, ‖f i‖ ≤ a) → ‖Journey.listen Y H n d0 s f - collector Y H n d0 t s f‖ ≤ z :=by
 filter_upwards [ferry_all Y s,Y.UV.tendsto_atTop.eventually (LocalLimit.Donor.shrinks (C:=P.C) (τ:=Y.τ) (T:=Y.meter) s P.b (div_pos v u))] with d p q n t
 refine ⟨p n t, fun f x y=>?_⟩; refine (awaken Y H s (p n t) f x).trans ?_; apply (mul_le_mul (q _ ((Y.voyage n).domain d t)) (show Afterglow.cash (deltaL Y H n s) f ≤ a from ?_) (cash_nonneg ..) (div_pos v u).le).trans_eq (div_mul_cancel₀ _ u.ne') -- tune
 unfold Afterglow.cash; exact (integral_mono_of_nonneg (Eventually.of_forall fun i=>norm_nonneg _) (integrable_const a) (Eventually.of_forall fun i=>y _)).trans_eq (by simp)
include W
/-- closure cost hull for all hot readings. Enough to keep norm sizes on THIS
fixed s and support & comparison meter and one course; no claim about diagonal with
s changing or mixed embeddings. -/
theorem supplied (S:Finset Cover)(z a:ℝ)(u:0<a)(v:0<z) : ∀ᶠ n:ℕ in atTop,∀ᶠ d0:ℕ in atTop,(Y.voyage (i n)).kick ≤ k d0 ∧ ∀ t:(Y.voyage (i n)).kick ≤ k d0,∀ f:Buffered.Family (tent Y H), InTest (tent Y H) true S false f→(∀ x,‖f (momentm Y (i n) s) x‖≤a)→ ‖collector Y H (i n) (k d0) t s (f (momentm Y (i n) s)) - E' s f‖ ≤ z:=by
 let E:= meter_time; have hv:z/2>0:=half_pos v; let L:=W.own.pick.grow_k
 have he:Tendsto (fun i:ℕ=> Meter i*a) atTop (𝓝 0):=by simpa only [zero_mul] using meter_time.mul_const a
 filter_upwards [W.crimson S s,he.eventually (ge_mem_nhds hv)] with n f t; let q:=i n
 filter_upwards [cadence Y k L q,L.tendsto_atTop.eventually_ge_atTop ((Y.voyage q).kick),L.tendsto_atTop.eventually (afterThaw Y H s _ _ u hv)] with d0 h p ht
 refine ⟨p,fun p' F V u=>?_⟩; let X:= collector Y H q (k d0) p' s (F (momentm Y q s)); let x:=sharp Y H s q (k d0) F
 apply (norm_sub_le_norm_sub_add_norm_sub X x (E' s F)).trans; have hb: ‖x-E' s F‖≤ z/2:=((f.2 F V _ u).2 d0 h).trans t; rw [norm_sub_rev X]; have hy: ‖x-X‖≤ z/2:= (ht (i n) p').2 _ (V.support _).env u; linarith
private def monoBound (C:ℝ) (v:List Cover):= (max 1 C⁻¹)^v.length
variable (R:Reservation P g C k') (P1: squareWidth r k'≤Ul) (R0:∀ᶠ n': Side in atTop,Even n'.val→ Cinema P n' o r k' Ul d g C Ω z)
variable (P2: (SculptureBirth P g k')^ (r^4)* magnified (tent Y H) (gaugePrice P (Course.fullTariff P g)) (2*(Escalator.high P Ul d+4))≤1/8) (P3:0<z)
include R P1 R0 P2 P3 W
lemma advertised : ∀ᶠ s:ℕ in atTop,∀ l:SU.Slot,∃ i:List Cover,i.Sublist (selection o r k').toList ∧ i≠[] ∧ ∃ f:junior (tent Y H), Effect (tent Y H) l (apart (nodeC o) Ul S★) V★ i f ∧ (a★/2 < ‖E' s f.val‖) ∧ ∀ m:Side,∀ i', ‖f.val m i'‖ ≤ Concord.count (V★)*monoBound C (S★).toList:=by
 let T:=V★; let L:= (selection o r k').toList; let a:=atomPay L; let X:=monoBound C L; have hz:0<a/2:=half_pos (atom_pos L); have hp: 1 ≤ max 1 C⁻¹:=le_max_left ..; have he:0 ≤ C⁻¹:= (inv_pos_of_pos R.cap).le
 have hX:1≤X:= one_le_pow₀ hp; have ht(i:List Cover)(h:i.Sublist L): C⁻¹^i.length≤ X := (pow_le_pow_left₀ he (le_max_right ..) _).trans (pow_le_pow_right₀ hp h.length_le)
 filter_upwards [recorded Y H R P1 R0 P2 P3] with s p l; obtain ⟨n,f,t⟩:= ((W.own.pick.grow_i.tendsto_atTop.eventually p).and (supplied Y H s W T _ _ (zero_lt_one.trans_le hX) hz)).exists
 obtain ⟨j,h,u⟩:= (t.and (W.own.pick.grow_k.tendsto_atTop.eventually f)).exists
 obtain ⟨v,hv,w,x,pxc,px,py,pz⟩:= u.2.2 h.1 l; refine ⟨v,hv,w,x,pxc,?_,fun m r=> (pz m r).trans (mul_le_mul_of_nonneg_left (ht v hv) (Concord.count_nonneg _))⟩; let y:=collector Y H (i n) (k j) h.1 s (x.val (momentm Y (i n) s))
 have hu':‖y-E' s x.val‖≤ a/2:= h.2 h.1 x.val pxc.opera fun b=>(py b).trans (ht v hv)
 change a<‖y‖ at px; change a/2 < _; linarith only [hu', px, norm_sub_norm_le y (E' s x.val)]

-- assembly size-contained certificate existential
omit R P1 R0 P2 P3 W
def Shelter (T S:Finset Cover)(J:List Cover):Prop:= (∀ x∈ S,nodeC x∈T) ∧ (∀ x∈J,nodeC x∈T)∧J.Nodup∧ (∀ x∈J,x∉S)
-- Lβ intentionally not negative vs plane. GoodSet b₀ centers? use chosen λ meter with plane3 ℤ.
structure MixedMean (C a:ℝ)(K:Calibration)(T S:Finset Cover)(J:List Cover)(E:ℕ→Buffered.Family K→ℂ) : Prop where
 pose : starboard 3 0 K.ℓ T
 house : Shelter T S J
 cost : 0<C
 gain : 0<a
 earn : ∀ᶠ s:ℕ in atTop,∀ l:SU.Slot,∃ i:List Cover,i.Sublist J ∧ i≠[] ∧ ∃ f:junior K, Effect K l S T i f ∧ a < ‖E s f.val‖∧ ∀ m:Side,∀ x, ‖f.val m x‖ ≤ C
include R W
lemma leased : ∃ T S: Finset Cover,∃ J:List Cover,∃ c a:ℝ, MixedMean c a (tent Y H) T S J E':=by
 obtain ⟨r,Ul,d,o,Ω,z,a,u,t,h,w,h1⟩:= purchases (tent Y H) P R; let T:=(castle (nodeC o) (Escalator.high P Ul d+4)); let Q:=selection o r k'; let L:= Q.toList; let S:= apart (nodeC o) Ul Q; let x:=atomPay L; have hy:0<x/2:=half_pos (atom_pos _); let Y':=Concord.count ((castle (nodeC o) (Escalator.high P Ul d+4)))*monoBound C L
 refine ⟨T,S,L,max 1 Y',x/2,h,⟨fun i p=>?_,fun i p=>?_, nodup_toList Q, fun i t v=> (mem_sdiff.mp v).2 (mem_toList.mp t)⟩, zero_lt_one.trans_le (le_max_left ..),hy,?_⟩ -- constructor annotate
 · exact tower (nodeC o) (show Ul≤ Escalator.high P Ul d+4 by unfold Escalator.high; omega) ((inside_b ..).1 (mem_sdiff.mp p).1)
 · exact tower _ (t.trans (show Ul≤ Escalator.high P Ul d+4 by unfold Escalator.high; omega)) (book o r k' _ (mem_toList.mp p))
 apply (advertised Y H W R t h1 w u).mono; intro s g l; obtain ⟨i,v,w,f,z,hx,e'⟩:=g l; exact ⟨i,v,w,f,z,hx,fun t b=>(e' t b).trans (le_max_right ..)⟩
end Ovation
end YM.CF.Signal
#print axioms YM.CF.Signal.Ovation.leased
