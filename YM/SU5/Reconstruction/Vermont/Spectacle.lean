import YM.SU5.Reconstruction.Vermont.Mintage
import YM.SU5.Reconstruction.Anvil.OpCoin
/-!
# Ports furnish REAL OP comparison, via analytic identity from just vacuum-ket charges
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Lens
open Function Set Filter MeasureTheory Spectral Analysis OS.Semigroup ConePrice Sail ContinuousLinearMap Anvil
open scoped BigOperators Topology NNReal InnerProductSpace ComplexOrder
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(A L:H.Op)(r e:ℝ≥0)(η:ℝ) (p q:H)
local notation "T"=> veil (-(r:ℝ)) (r:ℝ) η
local notation "𝕍"=> ((r:ℝ):ℂ)
local notation "𝔼"=> ((e:ℝ):ℂ)
-- L is A out, CP3 formulas compare only REAL z.
structure Plan (f:ℂ→ℂ) : Prop where
  paid : AnalyticOnNhd ℂ f (veil (-(r:ℝ)) (r:ℝ) η)
  plus (w:ℝ)(v:w∈ Ioo (e:ℝ) r): f w=before S r A L p q (e:ℝ) 0 w
  minus (w:ℝ)(v:w∈ Ioo (-(r:ℝ)) (0:ℝ)): f w= after S r A L p q (e:ℝ) 0 w
local notation "A'" B:max=> Plan S B L r e η p q

-- room both sides. furnishing with cost.
lemma performance {X:ℂ→H.Op}{c:ℝ≥0} (w:Port S L η X A e c)(hη:0<η)(he:e<r) : ∃ f, Plan S A L r e η p q f ∧ ∀ z∈T, ‖f z‖ ≤ ‖p‖*((c:ℝ) * ‖L‖ * ‖q‖):=by
 let d:= r-e; let B₀:=S.E r; let C₀:= S.E d;
 let K:= storm_port S L η r; let Q:= storm_port S L η d
 let Z(z:ℂ):= alloy (storm S L r) X B₀ A r z; let U(z:ℂ):= alloy Z (storm S L d) (B₀*A) C₀ (r+e) z
 let b:= welding (welding K w) Q; let y:ℝ≥0:= (1*c)*1; let l:= r+e+d; let F(z:ℂ):= inner ℂ p (U (z+𝕍) q)
 have v:(d:ℝ)= (r:ℝ)-(e:ℝ):= NNReal.coe_sub he.le
 have x'(z:ℂ)(p':z∈T): z+𝕍∈ veil 0 (l:ℝ) η:= by
   refine ⟨(by simp; linarith [show -(r:ℝ) < z.re from p'.1]),?_,?_⟩
   · change _ < (r:ℝ) + (e:ℝ)+(d:ℝ); simp; rw [v]; linarith [show z.re<(r:ℝ) from p'.2.1] -- simp maybe
   change |(z+𝕍).im| < η; simpa using (show |z.im|< _ from p'.2.2)
 refine ⟨F,⟨fun z h=> ?_,fun x h=>?_,fun x h=>?_⟩,fun z h=>?_⟩
 · exact (b.analytic p q (z+𝕍) (x' z h)).comp (f:=fun z:ℂ=>z+𝕍) (analyticAt_id.add analyticAt_const)
 · have a:(e:ℝ)≤x:= h.1.le; let α:ℂ:= x; have ht: ((r+e:ℝ≥0):ℝ) ≤ (α+𝕍).re :=by simp [α]; linarith only [a]
   unfold before F U;
   rw [aft (welding K w) Q ht (by simp [α]; exact hη.le), storm,show α+𝕍- (↑((r+e:ℝ≥0):ℝ):ℂ)=(x:ℂ)-𝔼 from (by unfold α; push_cast; ring), Complex.ofReal_zero, sub_zero,show ((d:ℝ):ℂ)- ((x:ℂ) -𝔼)=𝕍-(x:ℂ) from (by rw [v]; push_cast; ring)] -- ..
   rfl
 · have a:x≤0:= h.2.le
   have ht: ((x:ℂ)+𝕍).re ≤ r:=by simp; linarith only [a]
   unfold F U; rw [ahead (le_trans ht (show (r:ℝ)≤ _ from le_add_of_nonneg_right (e:ℝ≥0).property)), show Z _= _ from ahead ht] -- tune inferred equality RHS?
   unfold storm after; rw [Complex.ofReal_zero,sub_zero,add_comm (x:ℂ), show 𝕍-(𝕍+(x:ℂ))=-(x:ℂ) from (by abel), ←v,Real.toNNReal_coe]; rfl
 unfold F
 apply (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
 exact ((U _).le_opNorm q).trans (mul_le_mul_of_nonneg_right ((b.toll _ (bore_v _ _ (x' z h))).trans_eq (by rw [mul_one,one_mul])) (norm_nonneg _))
section compare
variable {T':ℕ→H.Op}{M:Set H.Op}{c:ℝ≥0}(L':∀ B∈M,∀ t:ℝ,|t|≤η → Commute B (LorTime S t L))(h:0<η)(v0:e<r)(q0:∀ n, Script S M (T' n) e c)(A0:Limited atTop T' A)
include h v0 L' q0 A0
lemma survives : ∃ f,Plan S A L r e η p q f:= by
 choose f hf b using fun n=> performance S (T' n) L r e η p q ((q0 n).port L').choose_spec h v0  -- argument order tune
 obtain ⟨F,HZ,u⟩:=limit_chance f (veil_open _ _ _) (fun n=>(hf n).paid.differentiableOn) b; refine ⟨F,HZ,fun x t=>?_,fun x t=>?_⟩
 · let v : x∈ Ioo (-(r:ℝ)) (r:ℝ):= ⟨lt_trans (neg_lt_zero.mpr (e.property.trans_lt (show (e:ℝ)< r from v0))) (lt_of_le_of_lt (e:ℝ≥0).property t.1),t.2⟩ -- tune syntax
   refine tendsto_nhds_unique (u _ (veil_real h _ v)) (Tendsto.mono_left ?_ (Ultrafilter.of_le atTop))
   simp_rw [(hf _).plus x t,before, ← S.swing]; apply A0.confirms -- tune S.swing direction
 have hz:x∈ Ioo (-(r:ℝ)) (r:ℝ):=⟨t.1,t.2.trans_le (r:ℝ≥0).property⟩
 refine tendsto_nhds_unique (u _ (veil_real h _ hz)) (Tendsto.mono_left ?_ (Ultrafilter.of_le atTop))
 simp_rw [(hf _).minus x t,after]
 let X: H.Op:= phase S (𝕍+(x:ℂ)); let Y:= phase S (-(x:ℂ)-(↑(0:ℝ):ℂ)); let z:= S.E (Real.toNNReal ((r:ℝ)-(e:ℝ))) q
 let W:= (X.comp L).comp Y
 change Tendsto (fun i=>inner ℂ p (W (T' i z))) atTop (𝓝 (inner ℂ p (W (A z))))
 simp_rw [← adjoint_inner_left W]; exact A0.confirms ..
end compare
variable (Z:Set H) (hZ: Dense Z) (w':0<(r:ℝ)) (e₀:e<r) (Φ:∀ s:ℝ≥0, S.E s q=q)
include hZ w' e₀ Φ
lemma buys (B:H.Op) (V:A q=B q) (h:∀ p∈ Z, ∃ η>0,∃ f,Plan S A L r e η p q f) (u:∀ p∈Z, ∃ η>0,∃ f,Plan S B L r e η p q f) (t:ℝ≥0) (w:0<t)(d:t<r-e): A (S.E t (L q))=B (S.E t (L q)):= by
 apply Dense.eq_of_inner_right ℂ ((S.whole r).dense_image (S.E r).continuous hZ); rintro _ ⟨x,hx,rfl⟩
 obtain ⟨a,a0,f,H⟩:= h x hx; obtain ⟨a',h0,g,Hg⟩:=u x hx
 let η₀:=min a a'; let s:=veil (-(r:ℝ)) (r:ℝ) η₀; have h₁:0<η₀:=lt_min a0 h0
 let wZ:= Ioo (-(r:ℝ)) (r:ℝ); let wX:= Ioo (-(r:ℝ)) 0; have H₀:wX⊆ wZ:= Ioo_subset_Ioo le_rfl w'.le
 have hu1(z:ℂ)(b z':ℝ)(h:z'≤b)(v:z∈veil (-(r:ℝ)) (r:ℝ) z') : z∈ veil (-(r:ℝ)) (r:ℝ) b:= ⟨v.1,v.2.1,(show |z.im|<_ from v.2.2).trans_le h⟩
 obtain ⟨z,b,gz⟩:= exists_between (neg_lt_zero.mpr w'); have H':z∈wX:=⟨b,gz⟩
 have heq: EqOn f g s:= by
   refine pioneer (veil_connected _ _ _) (veil_real (r:= -(r:ℝ)) (t:=(r:ℝ)) h₁ z (H₀ H')) _ _ H' (H.paid.mono (fun z=> hu1 z _ _ (min_le_left ..))) (Hg.paid.mono (fun z=> hu1 z _ _ (min_le_right ..))) ?_
   intro y k; rw [H.minus y k, Hg.minus y k, after,after,Φ,V]
 let y:ℝ:= (t:ℝ)+(e:ℝ); have kg:y∈ Ioo (e:ℝ) (r:ℝ):= ⟨lt_add_of_pos_left _ (show 0<(t:ℝ) from w),(lt_sub_iff_add_lt.mp (lt_of_lt_of_eq (show (t:ℝ)< _ from (show (t:ℝ)< ((r-e:ℝ≥0):ℝ) from d)) (NNReal.coe_sub e₀.le)))⟩
 have P:= heq (veil_real h₁ y ⟨lt_of_le_of_lt ((neg_lt_zero.mpr w').le.trans (e:ℝ≥0).property) kg.1,kg.2⟩)
 rw [H.plus y kg,Hg.plus y kg,before_real,before_real,Φ, show y-(e:ℝ)=(t:ℝ) by unfold y; ring, Real.toNNReal_coe] at P; exact P
end YM.Lens
