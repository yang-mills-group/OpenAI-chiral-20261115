import YM.SU5.Reconstruction.Vermont.Spectacle
/-! # Pay plan from an earlier observer after auditing ANY right state. -/
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
variable (Z:Set H) (hZ: Dense Z) (w':0<(r:ℝ)) (e₀:e<r) (Φ:∀ s:ℝ≥0, S.E s q=q)
include hZ w' e₀ 
lemma buysAt (B:H.Op) (V:∀ t:ℝ≥0, A (S.E t q)= B (S.E t q)) (h:∀ p∈ Z, ∃ η>0,∃ f,Plan S A L r e η p q f) (u:∀ p∈Z, ∃ η>0,∃ f,Plan S B L r e η p q f) (t:ℝ≥0) (w:0<t)(d:t<r-e): A (S.E t (L (S.E (r - (t+e)) q)))=B (S.E t (L (S.E (r - (t+e)) q))):= by
 apply Dense.eq_of_inner_right ℂ ((S.whole r).dense_image (S.E r).continuous hZ); rintro _ ⟨x,hx,rfl⟩
 obtain ⟨a,a0,f,H⟩:= h x hx; obtain ⟨a',h0,g,Hg⟩:=u x hx
 let η₀:=min a a'; let s:=veil (-(r:ℝ)) (r:ℝ) η₀; have h₁:0<η₀:=lt_min a0 h0
 let wZ:= Ioo (-(r:ℝ)) (r:ℝ); let wX:= Ioo (-(r:ℝ)) 0; have H₀:wX⊆ wZ:= Ioo_subset_Ioo le_rfl w'.le
 have hu1(z:ℂ)(b z':ℝ)(h:z'≤b)(v:z∈veil (-(r:ℝ)) (r:ℝ) z') : z∈ veil (-(r:ℝ)) (r:ℝ) b:= ⟨v.1,v.2.1,(show |z.im|<_ from v.2.2).trans_le h⟩
 obtain ⟨z,b,gz⟩:= exists_between (neg_lt_zero.mpr w'); have H':z∈wX:=⟨b,gz⟩
 have heq: EqOn f g s:= by
   refine pioneer (veil_connected _ _ _) (veil_real (r:= -(r:ℝ)) (t:=(r:ℝ)) h₁ z (H₀ H')) _ _ H' (H.paid.mono (fun z=> hu1 z _ _ (min_le_left ..))) (Hg.paid.mono (fun z=> hu1 z _ _ (min_le_right ..))) ?_
   intro y k; rw [H.minus y k, Hg.minus y k, after,after,V]
 let y:ℝ:= (t:ℝ)+(e:ℝ); have kg:y∈ Ioo (e:ℝ) (r:ℝ):= ⟨lt_add_of_pos_left _ (show 0<(t:ℝ) from w),(lt_sub_iff_add_lt.mp (lt_of_lt_of_eq (show (t:ℝ)< _ from (show (t:ℝ)< ((r-e:ℝ≥0):ℝ) from d)) (NNReal.coe_sub e₀.le)))⟩
 have P:= heq (veil_real h₁ y ⟨lt_of_le_of_lt ((neg_lt_zero.mpr w').le.trans (e:ℝ≥0).property) kg.1,kg.2⟩)
 rw [H.plus y kg,Hg.plus y kg,before_real,before_real, show y-(e:ℝ)=(t:ℝ) by unfold y; ring, Real.toNNReal_coe, show (((r:ℝ)-(0:ℝ))-y).toNNReal=r - (t+e) from ?_] at P; swap; · apply NNReal.eq; rw [Real.coe_toNNReal ( (r:ℝ)-0-y) (by rw [sub_zero]; exact sub_nonneg.mpr kg.2.le), NNReal.coe_sub (show t+e≤r from kg.2.le)]; exact (by rw[sub_zero]; rfl)
 exact P -- tune

end YM.Lens
