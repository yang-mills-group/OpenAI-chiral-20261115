import YM.SU5.FiniteGaugeData.Reliance.Sleeves
import YM.SU5.FiniteGaugeData.Reliance.Candela
import YM.SU5.FiniteGaugeData.Marked.Journey.Wake
import YM.SU5.FiniteGaugeData.Concord.Today
/-! # Keep weighted bills (and local sizes and actual pigment) under limit.

 At resolution s, even early periods if width bill and kick + sufficient k etc.
 Reflection uses heat member to accomplish this bound (not Built around later pos-state)
 then Y's **actual** transfer. Uniform across all stencils at the chosen s,
card and native widths. Especially on final E_s independent of card (absorb δ), stage even.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Reliance
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
open Afterglow Afterglow.Sound Afterglow.Satin Afterglow.Journey
open Py Py.Rate LocalLimit Preparation FullBill
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (PQ:Cashbox Λ)(s:ℕ) {n d:ℕ} {i k:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Concord.Playhouse Λ l}
local notation "K"=> tent Y H
local notation "S'"=> Universum.slope Λ s
local notation "αt" n:max=> momentm Y n s
local notation "ν" n:max=> (tent Y H).c (αt n)
local notation "ηt" n:max=> side Y n s
local notation "Z"=> (Y.passing PQ).choose

section
variable (n d)

def grossC := |Universum.surcharge Λ + (Y.passing PQ).choose| * (4*(Λ.block.val:ℝ))^4
lemma gross_nn : 0 ≤ grossC Y PQ:=by unfold grossC; positivity
include H PQ
lemma ceremony (n:ℕ) : Real.exp ((Universum.surcharge Λ+(Z))*sites (Λ.Ctor (Y.ir n) s)) ≤ Real.exp (grossC Y PQ*((momentm Y n s).val:ℝ)^4) := by
 apply Real.exp_monotone; apply (mul_le_mul_of_nonneg_right (le_abs_self _) (show 0 ≤ sites _ from by unfold sites; positivity)).trans_eq; unfold grossC sites Preparation.Ctor cell CSide More momentm; push_cast; ring_nf
omit H PQ

private lemma periodCost {A:Calibration}{m n:Side}{D C:ℝ} (e:A.c m = n)(X : Mark n→ℂ)(p:0 ≤ D)(t:∀ (S:Support (More n))(f:Mark n)(c:ℝ), Apt C c S f→c≥0→ ‖X f‖ ≤ c*Real.exp (D*(m.val:ℝ)^4)) : Gross («K»:=A) m (fun i=>X (show Mark n from e ▸ i)) C D:=by
 subst n; refine ⟨p,fun {f S c} v _=> t S f c v (apt_pos v)⟩ -- notation K conflict

include H PQ
theorem march (s:ℕ) : ∀ᶠ k in atTop, s<buoy (Y.ivory k) ∧∀ n:ℕ,∀ p:(Y.voyage n).kick ≤ k,
    Ferry Y s n k ∧ Gross («K»:=tent Y H) (momentm Y n s) (collector Y H n k p s) (Universum.slope Λ s) (grossC Y PQ):=by
 filter_upwards [(Y.passing PQ).choose_spec.2.2 s, ferry_all Y s] with k v t
 refine ⟨v.1,fun n p=>⟨t n p,periodCost (m:=momentm Y n s) (A:=tent Y H) (terrain Y H (Y.ir n) s) (solder Y n k p s) (gross_nn ..) (fun S f c p' h=> ?_)⟩⟩
 let V:= ((Y.voyage n).Q k p).carnival ((Y.voyage n).funds)
 exact (Universum.tender Λ s V PQ v.1.le (v.2 n p) f p').trans (mul_le_mul_of_nonneg_left (ceremony Y H PQ s n) h)
end

variable {c:ℝ} (m r:ℕ)
local notation "zM"=> magnified K (grossC Y PQ) m

include PQ

/-- if card not bounded by input, absorb it via extra parameter v (diam gives one elsewhere).
At all such chassis supports, aperture may go to 0, **for each** j.
-/
theorem blockPrice (v:ℕ)(ε:ℝ)(p:0<ε) : ∀ᶠ d in atTop,∀ n:ℕ,∀ u:(Y.voyage n).kick ≤ d,
      Ferry Y s n d ∧ ∀ (c:ℝ)(T:Support (More ((tent Y H).c (momentm Y n s))))(f:Mark ((tent Y H).c (momentm Y n s))), Apt (Universum.slope Λ s) c T f→ (∀ i, rest K (momentm Y n s) T i m)→ AtSupport false T f → T.card≤v→
      ‖collector Y H n d u s f‖≤ c*magnified (tent Y H) (grossC Y PQ) m ∧ ‖listen Y H n d s f‖ ≤ c*(magnified (tent Y H) (grossC Y PQ) m+ε):=by
 let t:= Real.exp (posted (Universum.slope Λ s) v); have ht:0 < t:= Real.exp_pos _
 filter_upwards [march Y H PQ s,Y.UV.tendsto_atTop.eventually (LocalLimit.Donor.shrinks (T:=Y.meter) (C:=Λ.C) (τ:=Y.τ) s Λ.b (div_pos p ht))] with d h j n u
 obtain ⟨v,r⟩:=h.2 n u -- shadow v
 refine ⟨v,fun c T f p' t' a b=>?_⟩
 let x:= listen Y H n d s f; let y:= collector Y H n d u s f
 have he: ‖y‖ ≤ c*zM:= shelter (boxprice Y H n d u s v.fire v.enters) r t' p' a
 have hc: 0 ≤ c:= apt_pos p'
 let l:= deltaL Y H n s
 have hv:cash l f ≤ c*t:= by apply (integral_mono_of_nonneg (Eventually.of_forall fun i=> (norm_nonneg (f (drawn l i)))) (integrable_const (c*t)) (Eventually.of_forall fun i=> apt_cap (Universum.slope_n Λ s PQ).le p' _ b (drawn l i))).trans_eq; simp
 have hk:‖x-y‖ ≤ c*ε:= by
    apply (awaken Y H s v f a.env).trans; exact (mul_le_mul (j _ ((Y.voyage n).domain d u)) hv (cash_nonneg l f) (div_pos p ht).le).trans_eq (by field_simp <;> ring)
 refine ⟨he,?_⟩; change ‖x‖ ≤ c*(zM+ε); linarith [norm_sub_norm_le x y]
variable (W: Concord.Traced Y H i k F E P)
include W

-- in particular every UV row with through-local constraints, every final germ.
lemma by_city (n:ℕ) {x:Concord.junior K} {T:Support (More ((tent Y H).c (momentm Y n s)))}(p:Apt (Universum.slope Λ s) c T (x.val (αt n))) (u:∀ i, rest K (momentm Y n s) T i m) (t:AtSupport false T (x.val (αt n))):
    ‖F s x.val n‖ ≤ c*magnified K (grossC Y PQ) m := by
 let W0:= magnified K (grossC Y PQ) m; have he : Tendsto (fun j:ℕ=>c*(W0+Concord.Meter j)) atTop (𝓝 (c*W0)):= by simpa using ((tendsto_const_nhds (x:=W0)).add Concord.meter_time|>.const_mul c)
 apply ge_of_tendsto he; apply Eventually.of_forall; intro j
 apply le_of_tendsto ((W.own.together s x.val x.property).inner n).norm
 refine (W.own.pick.grow_k.tendsto_atTop.eventually (p:=fun k=> ‖sharp Y H s n k x.val‖ ≤ c*(W0+Concord.Meter j)) ?_); filter_upwards [blockPrice Y H PQ s m T.card (Concord.Meter j) (Concord.meter_p _),eventually_ge_atTop ((Y.voyage n).kick)] with k f l
 exact (f n l).2 _ T _ p u t le_rfl|>.2

lemma aftermath {x:Concord.junior K}(h:∀ᶠ j in atTop,∃ (T:Support (More ((tent Y H).c (momentm Y (i j) s)))),
    Apt (Universum.slope Λ s) c T (x.val (momentm Y (i j) s)) ∧ (∀ a, rest K (momentm Y (i j) s) T a m) ∧ AtSupport false T (x.val (momentm Y (i j) s))) : ‖E s x.val‖ ≤ c*magnified K (grossC Y PQ) m :=by
 apply le_of_tendsto (W.own.together s x.val x.property).periods.norm
 filter_upwards [h] with n v; obtain ⟨T,v,t,p⟩:= v; exact by_city Y H PQ s m W (i n) v t p

omit PQ W

def occupy (S:Finset Cover)(m:ℕ) := ∀ i:Axis,∃ b:ℤ,∀ x∈S,b ≤ x i∧ x i ≤ b+m
lemma resting {S:Finset Cover}(p:occupy S m)(n:Side)(A:Calibration)(i:Axis):rest A n (region S (A.c n)) i m:=by
 obtain ⟨b,u⟩:=p i; refine ⟨b,fun x t=>?_⟩; obtain ⟨x,k,rfl⟩:= mem_image.mp t; exact ⟨x i,(u x k).1, (u x k).2,rfl⟩
include PQ W
/-- As family of true Palettes. Width costs include size of physical buffer at THIS level. No change
to E; this is a new estimate on E for application. -/
theorem stamped (S:Finset Cover){x:Concord.junior K}(p:x∈ Concord.club (tent Y H) S)(h:occupy S m)
    (v:∀ᶠ n:Side in atTop,Apt (Universum.slope Λ s) c (region S ((tent Y H).c n)) (x.val n)): ‖E s x.val‖ ≤ c*magnified (tent Y H) (grossC Y PQ) m:= by
 apply aftermath Y H PQ s m W; filter_upwards [((momentum Y s).comp W.own.pick.grow_i.tendsto_atTop).eventually v] with n u; exact ⟨_,u,resting m h _ (tent Y H), (show InTest K true S false x.val from p).support _⟩

lemma stamped_sup {S:Finset Cover}{x:Concord.junior K}(p:x∈ Concord.club (tent Y H) S)(h:occupy S m)
    (v:∀ᶠ n:Side in atTop,∀ i, ‖x.val n i‖ ≤ c): ‖E s x.val‖ ≤ c*magnified (tent Y H) (grossC Y PQ) m:= stamped Y H PQ s m W S p h (v.mono fun n z=> apt_base _ (Universum.slope_n Λ s PQ).le ((norm_nonneg _).trans (z (1,1))) z)
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.blockPrice
#print axioms YM.CF.Buffered.Reliance.stamped
