import YM.SU5.Registration.Unpad
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Realization given positive-pad convergence and its budget

Genuinely only require strong Cauchy in Hilbert at *fixed*, symmetric, strictly
positive allowance (width will thin before asking any smaller allowance).
Products are convergent everywhere in the domain topology specified in
`Grading`. Need to obtain the families `cut` and their hypotheses below on the
actual calibration to apply this theorem. `Delivery` is an estimate, **not**
a statement that the Cauchy or small-allowance price is granted without those
extra physical bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinRegistration
open Set Filter Function MeasureTheory Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading
variable {H : Hilbert} {a : Axis} (S : OS.Semigroup H a)
local notation "G" => bands S
local notation "D" => radial S
local notation "T" => S.E

/-- Positive-pad full point operator bill on the elected real-motion H.
For existence we even allow the threshold in width to depend on the chosen
s>0. Polynomial rates asked on just *one insertion at a time*, in operator
norm on genuine cuts, using any fixed pad. -/
structure Delivery (A : ℝ≥0→ℕ→H.Op) : Prop where
  coherent (t : ℝ≥0) (p : 0<t) (s : ℝ≥0) : ∀ᶠ i in atTop, A (t+s) i=T s * A t i * T s
  convergence (t : ℝ≥0) (p : 0<t) (x : H) : CauchySeq (fun i=> A t i x)
  price : ∃ k : ℕ, ∃ C≥(0:ℝ), ∀ t : ℝ≥0, 0<t→t≤1→ ∀ᶠ i in atTop, (t:ℝ)^k * ‖A t i‖ ≤ C

variable {S}
lemma ceiling {A : ℕ→ H.Op} (h : ∀ x:H, CauchySeq (fun i=> A i x)) : ∃ C≥(0:ℝ), ∀ i, ‖A i‖≤ C:= by
  obtain ⟨C,p⟩:=banach_steinhaus (g:=A) (fun x=>(by obtain ⟨C,h⟩: BddAbove (range (fun i=> ‖A i x‖)):= (h x).norm_bddAbove; exact ⟨C,fun i=>h (mem_range_self i)⟩))
  exact ⟨C,(norm_nonneg _).trans (p 0),p⟩
lemma delivery_limit {A : ℕ→ H.Op} (h : ∀ x:H, CauchySeq (fun i=> A i x)) :
    ∃ B : H.Op, ∀ x:H, Tendsto (fun i=> A i x) atTop (𝓝 (B x)) := by
  obtain ⟨C,hc,p⟩:=ceiling h
  exact Registers.extendS A atTop C (fun i y=> ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (p i) (norm_nonneg _))) (fun x=> cauchySeq_tendsto_of_complete (h x))
lemma limit_ceiling {A : ℕ→ H.Op} {B : H.Op} (h : ∀ x, Tendsto (fun i=>A i x) atTop (𝓝 (B x))) {C : ℝ} (p : 0≤C) (t : ∀ᶠ i in atTop, ‖A i‖≤C) : ‖B‖≤ C:= by
  apply ContinuousLinearMap.opNorm_le_bound _ p; intro x
  exact le_of_tendsto ((h x).norm) (t.mono fun i p=> ((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right p (norm_nonneg _)))

namespace Delivery
variable {A : ℝ≥0→ℕ→ H.Op}
def accepts (h : Delivery S A) (t : ℝ≥0) := if p:0<t then (delivery_limit (h.convergence t p)).choose else 0
lemma accepted (h : Delivery S A) (t : ℝ≥0) (p : 0<t) (x : H) :
    Tendsto (fun i=> A t i x) atTop (𝓝 (h.accepts t x)) := by
  unfold accepts; rw [dif_pos p]; exact (delivery_limit (h.convergence t p)).choose_spec x
lemma isSound (h : Delivery S A) : Sound S h.accepts:= by
  intro t p s; ext1 x
  apply tendsto_nhds_unique (h.accepted (t+s) (add_pos_of_pos_of_nonneg p (by positivity : (0:ℝ≥0)≤ s)) x)
  refine Tendsto.congr' ?_ (((T s).continuous.tendsto (h.accepts t (T s x))).comp (h.accepted t p (T s x)))
  filter_upwards [h.coherent t p s] with i u; exact (DFunLike.congr_fun u x).symm
lemma limit_price {k : ℕ} {C : ℝ} (e : 0≤C) (p : ∀ t : ℝ≥0, 0<t→t≤1→ ∀ᶠ i in atTop, (t:ℝ)^k * ‖A t i‖ ≤ C)
    (h : Delivery S A) : PadBound h.accepts k C := by
  intro t u v; have he: 0 < (t:ℝ)^k := pow_pos u _
  rw [mul_comm,←le_div_iff₀ he]; exact limit_ceiling (h.accepted t u) (div_nonneg e he.le) ((p t u v).mono fun i x=> (le_div_iff₀ he).2 ((mul_comm ..).le.trans x))
lemma paid (h : Delivery S A) : PadPaid h.accepts:= let ⟨k,C,v,b⟩:= h.price; ⟨k,C,v,h.limit_price v b⟩

lemma other (h : Delivery S A)
    (x : ∀ t:ℝ≥0, 0<t→∀ x:H,CauchySeq (fun i=> (A t i).adjoint x)) : Delivery S (fun t i=> (A t i).adjoint) where
  convergence := x
  coherent t p s := by
    refine (h.coherent t p s).mono ?_
    intro i q; rw [q]; rw [← ContinuousLinearMap.star_eq_adjoint,star_mul,star_mul]; simp only [ContinuousLinearMap.star_eq_adjoint,S.sym,mul_assoc]
  price := by obtain ⟨k,C,e,t⟩:=h.price; exact ⟨k,C,e,fun s u p=> by simpa only [ContinuousLinearMap.adjoint.norm_map] using t s u p⟩

lemma reverse {B : ℝ≥0→ℕ→H.Op} (h : Delivery S A) (p : Delivery S B) (u : ∀ s i, (A s i).adjoint=B s i) :
    p.accepts= fun s=> (h.accepts s).adjoint:= by
  funext s
  by_cases v:0<s
  · ext1 x; apply ext_inner_right ℂ; intro y
    rw [ContinuousLinearMap.adjoint_inner_left]; apply tendsto_nhds_unique (((p.accepted s v x)).inner (𝕜:=ℂ) (tendsto_const_nhds (x:=y)))
    simp_rw [← u, ContinuousLinearMap.adjoint_inner_left]; exact tendsto_const_nhds.inner (h.accepted s v y)
  simp [accepts,v]

lemma through_width (h : Delivery S A) (t : ℝ≥0) (u : 0<t) (f : Test4) {X : ℕ→D} {x : D} (p : (bands S).Approaches atTop X x) :
    (G).Approaches atTop (fun i=> warm S (A t i) f (X i)) (warm S (h.accepts t) f x) := by
  obtain ⟨C,hc,e⟩:= ceiling (h.convergence t u)
  have ho(B:H.Op)(p:‖B‖≤ C): PowerPrice S ((bands S).dissect B) 0 C:= fun m n=> le_trans (dissect_power S B m n) (by gcongr)
  refine enact_approach S ((G).dissect (h.accepts t)) _ atTop (fun i=> ((G).dissect (A t i))) (fun i=> dissect_paid S _) hc
    (ho _ (limit_ceiling (h.accepted t u) hc (Eventually.of_forall e))) (Eventually.of_forall fun i=> ho _ (e i)) ?_ f p
  exact fun m n v=> (((G).P m).continuous.tendsto (h.accepts t ((G).P n v))).comp (h.accepted t u ((G).P n v))
end Delivery

section list
variable {J : Type*} (A : J → ℝ≥0→ ℕ→H.Op) (p : ∀ j, Delivery S (A j))
abbrev DOp := (radial S)→ₗ[ℂ] (radial S)
/-- Arbitrarily query extra positive heat between words, alongside the field symbols. -/
inductive Letter (J : Type*) (σ : Type*)
| spend (v : σ)
| ask (j : J) (f : Test4) (v : σ)

namespace Letter
variable {σ : Type*} (r s : σ → ℝ≥0)
-- symmetric inner pad r first
noncomputable def applies : Letter J σ → @DOp _ _ S
| spend v=> stoveAt S (s v)
| ask j f v=> let B:= p j; warm S (B.accepts (r v)) f
noncomputable def buys (i : ℕ) : Letter J σ → @DOp _ _ S
| spend v=> stoveAt S (s v)
| ask j f v=> warm S (A j (r v) i) f
noncomputable def enacts : Letter J σ → @DOp _ _ S
| spend v=> stoveAt S (s v)
| ask j f _=> field S _ (p j|>.isSound) (p j|>.paid) f

lemma width (i : List (Letter J σ)) (e : ∀ z:σ, 0<r z) {X : ℕ→D} {x : D} (u : (bands S).Approaches atTop X x) :
    (bands S).Approaches atTop (fun n=> (i.map (buys (S:=S) A r s n)).prod (X n)) ((i.map (applies A p r s)).prod x) := by
  induction i with
  | nil=> exact u
  | cons v w ih =>
    cases v with
    | spend v=> exact through_heat S _ _ tendsto_const_nhds ih
    | ask j f v=> exact (p j).through_width _ (e v) f ih
lemma finish {ι : Type*} (l : Filter ι) (R T' : ι→ σ→ℝ≥0) (i : List (Letter J σ)) (q : ∀ z, Tendsto (fun t=> R t z) l (𝓝[>] 0))
    (v : ∀ z, Tendsto (fun t=> T' t z) l (𝓝 (s z))) {X : ι→D} {x : D} (u : (bands S).Approaches l X x) :
    (bands S).Approaches l (fun n=> (i.map (applies A p (R n) (T' n))).prod (X n)) ((i.map (enacts A p s)).prod x) := by
  induction i with
  | nil=> exact u
  | cons a w ih=>
    cases a with
    | spend a=> exact through_heat S _ _ (v a) ih
    | ask j f a=>
      let A':= (p j).accepts
      have h(x) : bothPads S A' x x=A' x:= by unfold bothPads; rw [min_self,tsub_self,S.eZero]; exact (one_mul (A' x) ▸ mul_one (A' x))
      have he:= passes_lim S A' (p j|>.isSound) (p j|>.paid) l f _ _ (q a) (q a) ih
      simp_rw [h] at he; exact he
end Letter
end list
end YM.SatinRegistration
