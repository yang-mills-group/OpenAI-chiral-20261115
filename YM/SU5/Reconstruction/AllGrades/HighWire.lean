import YM.SU5.Reconstruction.AllGrades.Dormitory
import YM.SU5.Reconstruction.Quanta.Touch
import YM.SU5.Verified.Satin.GroundExtension
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
/-! # Turn the fresh rotation into a hierarchy on the same selected even history -/
open SatinVerification
variable (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
local notation "π"=> i ∘ G.rows
local notation "κ"=> k ∘ G.columns
variable (D: Invitation Y H G)
local notation "σ₀"=> (i ∘ G.rows) ∘ D.indexN
local notation "τ₀"=> (k ∘ G.columns) ∘ D.indexN
local notation "T" => convey Y H G D
variable {b:Bool}{S Z:Finset Cover}{F F':Family (tent Y H)}(x:InTest (tent Y H) true S b F)


include V
local notation "W" t:max S:max=>volumeAround Λ l t S
abbrev launch (b:Bool):= stream Y H (T b)
local notation "l₀" s:max b:max t:max F:max=> launch Y H G D b s t F
variable (t:ℕ)
include x
lemma survives : InTest (tent Y H) true (W t S) b (l₀ s b t F):=by
 induction t with
 | zero=>exact x
 | succ n ih=> exact attaches_p Y H V (s+n) G D ih
lemma lighted (p:CovCover K F):CovCover K (l₀ s b t F):=by
 induction t with
 | zero=>exact p
 | succ n ih=> exact colors Y H V (s+n) G D (survives Y H V s G D x n) ih
lemma luminous{b':Bool}(p:InTest K true Z b' F')(h:Detached Λ l S Z):l₀ s (b ^^ b') t (F*F')=(l₀ s b t F) * (l₀ s b' t F'):=by
 induction t with
 | zero=>rfl
 | succ n ih=> unfold launch at ih ⊢; rw [stream_step, ih, fare_sep Y H V (s+n) G D (survives Y H V s G D x n) (survives Y H V s G D p n) ((Around_detaches Λ l h n).act Λ l), stream_step,stream_step]
 -- `unfold launch at ih ⊢` might fail
lemma flight_plus(p:InTest K true Z b F') : l₀ s b t (F+F')=(l₀ s b t F)+(l₀ s b t F'):=by
 induction t with
 | zero=>rfl
 | succ n ih=> unfold launch at ih ⊢; rw [stream_step, ih, combines Y H V (s+n) G D ((survives Y H V s G D x n).mono (subset_union_left (s₂:=W n Z))) ((survives Y H V s G D p n).mono subset_union_right), stream_step,stream_step]
lemma flight_scale(p:ℂ): l₀ s b t (p • F)= p • (l₀ s b t F):=by
 induction t with
 | zero=>rfl
 | succ n ih=> unfold launch at ih ⊢; rw [stream_step,ih,tuning Y H V (s+n) G D (survives Y H V s G D x n),stream_step]
lemma flight_halo (a:Axis)(z:ℤ): l₀ s b t (mirror K a z F) =mirror K a ((Λ.R.L.val:ℤ)^t*z) (l₀ s b t F):=by
 induction t with
 | zero=>simp only [launch,stream,Nat.rec_zero,pow_zero,one_mul]
 | succ n ih=> unfold launch at ih ⊢; rw [stream_step,ih,halo Y H V (s+n) G D (survives Y H V s G D x n),stream_step,pow_succ',mul_assoc]
lemma flight_chime(a:Axis)(z:ℤ): (l₀ s b t (chime K a z F))= chime K a ((Λ.R.L.val:ℤ)^t*z) (l₀ s b t F):=by unfold chime; rw [flight_halo Y H V s G D (axial K a 0 x), flight_halo Y H V s G D x,mul_zero]
lemma bend(p:InTest K true S b F'): T b s (F-F')=T b s F-T b s F':=by rw [sub_eq_add_neg, ←neg_one_smul ℂ F',combines Y H V s G D x (.smul _ p), tuning Y H V s G D p,neg_one_smul, sub_eq_add_neg]
lemma flight_minus(p:InTest K true Z b F') : (l₀ s b t (F-F'))= (l₀ s b t F)-(l₀ s b t F'):=by rw [sub_eq_add_neg,←neg_one_smul ℂ F',flight_plus Y H V s G D x t (.smul _ p),flight_scale Y H V s G D p,neg_one_smul, sub_eq_add_neg]
omit x

omit V in
lemma launch_step (F:Family (tent Y H))(b:Bool): l₀ s b (t+1) F= T b (s+t) (l₀ s b t F):=rfl
local notation "Q" b:max n:max r:max S:max F:max=> quarry Y H s (σ₀ r) (τ₀ r) b S F n
lemma journey_on_prices (b:Bool)(S:Finset Cover) (z:ℕ): ∃ C:ℝ,0<C ∧∀ε:ℝ,0< ε → ∀ᶠ r in atTop,
 ∀ (F:Family K), InTest K true S b F→∀x:ℝ,pay F x→
 pay (l₀ s b z F) (C*x) ∧ pay (Q b z r S F) (C*x) ∧ pay (Q b z r S F-(l₀ s b z F)) (ε*x):=by

 induction z with
 | zero=> refine ⟨1,zero_lt_one,fun ε p=>Eventually.of_forall fun r F x y h=>?_⟩; simp only [launch,stream,Nat.rec_zero,one_mul,Nat.add_zero,quarry]; refine ⟨h,h,(sub_self F).symm ▸ (fun i t=> (show ‖(0:Family K) i t‖=(0:ℝ) from norm_zero).le.trans (mul_nonneg p.le (pay_nonneg h)))⟩
 | succ z ih=>
    let U:= s+z; let S₀:=volumeAround Λ l z S
    obtain ⟨B,bp,g⟩:=ih; obtain ⟨A,h,c⟩:=value_of_lifts Y H V U G D S₀ b
    refine ⟨A*B,mul_pos h bp,fun ε e=>?_⟩
    let δ:= ε/(A+B+1); have hd:0<δ:=by unfold δ; positivity
    filter_upwards [g δ hd,c δ hd, D.thinned.tendsto_atTop.eventually (living Y H V s S G.history z)] with r p t Ω F iH x q
    let W₀:=l₀ s b z F; let Z:= Q b z r S F
    obtain ⟨h₁,h₂,h₃⟩:= p F iH x q
    have hv:InTest K true S₀ b W₀:= survives Y H V s G D iH z; have hs:InTest K true S₀ b Z:= Ω _ le_rfl F _ iH
    obtain ⟨h₄,h₅,h₆⟩:=t _ hs _ h₂
    rw [launch_step]; change pay _ _∧ pay (pick _ _ _ _ _ _ _ _) _ ∧ pay (pick Y H U (σ₀ r) (τ₀ r) b S₀ Z-T b U W₀) _; refine ⟨mul_assoc A B x ▸ (t _ hv _ h₁).1, mul_assoc A B x ▸ h₅,?_⟩ -- eq orientation
    intro n y; let V₁:=Garret.pick Y H U (σ₀ r) (τ₀ r) b S₀ Z
    change ‖V₁ n y-T b U W₀ n y‖≤ _; apply (norm_sub_le_norm_sub_add_norm_sub _ (T b U Z n y) _).trans
    have hd0:pay (T b U Z-T b U W₀) (A*(δ*x)):=by rw [←bend Y H V U G D hs hv]; exact (t _ (InTest.subOp hs hv) _ h₃).1
    apply (add_le_add (h₆ n y) (hd0 n y)).trans
    change δ*(B*x)+A*(δ*x)≤ ε*x
    have ht:(A+B)*δ≤ ε:= by have hp:(A+B+1)*δ=ε:=mul_div_cancel₀ _ (by positivity); nlinarith
    calc
      _ = ((A+B)*δ)*x:=by ring
      _≤ _:= mul_le_mul_of_nonneg_right ht (pay_nonneg q)
end Garret
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.flight_plus
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.flight_minus
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.luminous
#print axioms YM.CF.Buffered.Afterglow.Tower.Garret.journey_on_prices
