import YM.SU5.Assay.Lamp
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.OS.Semigroup.Marble
open Set Metric Filter
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}{j:Axis} (S:Semigroup H j)(v:H)(t:ℝ)
local notation "φ" => S.wax
local notation "V"=> H.Op
-- pair any direction absolute with lag `t≥0`; t includes center-offsets. Mat ordering in raising time.
noncomputable abbrev whisper (v:H)(A:H.Op):ℂ:= inner ℂ v (A v)
noncomputable abbrev hotPair (A B: V):ℂ:= whisper v (A*φ t*B)
noncomputable def seam (A B:V):ℂ:= hotPair S v t A B-whisper v A*whisper v B
noncomputable def quietArm (v:H):V→ₗ[ℂ]H where
 toFun F:= F v-whisper v F • v
 map_add' :=by intro A B; dsimp only [whisper]; change A v+B v-inner ℂ v (A v+B v) • v= _; rw [inner_add_right,add_smul]; abel
 map_smul' :=by intro f A; simp only [whisper]; change f • A v - inner ℂ v (f • A v) • v = f • _; rw [inner_smul_right,mul_smul, smul_sub]
structure Immutable (v:H): Prop where
 keeps : ∀ t:ℝ,S.wax t v=v
 unit : ‖v‖=1
variable (q:Immutable S v){x y:ℝ}
local notation "Δ"=> seam S v
local notation "d"=> whisper v
local notation "a"=> quietArm v
lemma hot_pay (A B:V) : hotPair S v t A B= inner ℂ (star A v) (φ t (B v)):=by change inner ℂ v (A _)= _; exact (ContinuousLinearMap.adjoint_inner_left ..).symm -- convention verify
lemma whispers_conj (A: V): star (whisper v A)= whisper v (star A):= by
 change (starRingEnd ℂ) (inner ℂ v (A v))= inner ℂ v ((star A) v); rw [inner_conj_symm]; exact (ContinuousLinearMap.adjoint_inner_right ..).symm
include q
lemma feel_unit: inner ℂ v v=1:=by rw [inner_self_eq_norm_sq_to_K,q.unit]; norm_num
lemma missed (A:V)(x y:ℝ): whisper v (S.sand A x y)= whisper v A:=by
 change inner ℂ v (φ x (A (φ y v)))= _; rw [← S.swing,q.keeps] -- trouble S.swing order
 rw [q.keeps]
lemma outsidePair (l r y₁ b:ℝ)(A B:V) (h:0≤r)(k:0≤y₁)(p:0 ≤ t): hotPair S v t (S.sand A l r) (S.sand B y₁ b)=hotPair S v (r+t+y₁) A B:=by
 unfold hotPair sand; change inner ℂ v (φ l (A (φ r (φ t (φ y₁ (B (φ b v)))))))=_; rw [← S.swing,q.keeps,q.keeps]; change d (A*(φ r*φ t*φ y₁)*B)= _; rw [S.wax_sq h p,S.wax_sq (add_nonneg h p) k]
lemma outside (l r y₁ b:ℝ)(A B:V) (h:0≤r)(k:0≤y₁)(p:0 ≤ t) : Δ t (S.sand A l r) (S.sand B y₁ b)= Δ (r+t+y₁) A B:=by unfold seam; rw [outsidePair S v t q l r y₁ b A B h k p, missed S v q, missed S v q]
lemma hushed (A:V): inner ℂ v (a A)=0:=by change inner ℂ v (A v-d A • v)=0; rw [inner_sub_right,inner_smul_right,feel_unit S v q,mul_one]; exact sub_self _
lemma still_pay (A B:V): Δ t A B=inner ℂ (a (star A)) (φ t (a B)):=by
 let X:= star A; let C:= d X; let D:= d A; let M:= d B; change _= inner ℂ (star A v-C • v) (φ t (a B)); rw [inner_sub_left,inner_smul_left, (show inner ℂ v (φ t (a B))=0 from by rw [←S.swing]; change inner ℂ (φ t v) _= _; rw [q.keeps,hushed S v q]), mul_zero,sub_zero]; unfold seam; rw [hot_pay]; change _=inner ℂ (star A v) (φ t (B v - whisper v B • v)); rw [map_sub,map_smul,q.keeps,inner_sub_right,inner_smul_right]; congr 1; rw [(show inner ℂ ((star A) v) v =d A from ContinuousLinearMap.adjoint_inner_left ..), mul_comm]
lemma still_coin (A:V): Δ 0 (star A) A= (↑(‖a A‖^2:ℝ):ℂ):=by rw [still_pay S v 0 q,star_star,S.wax_zero]; change inner ℂ (a A) (a A) = _; rw [inner_self_eq_norm_sq_to_K]; norm_cast
omit q
lemma seam_add (A C B:V) : Δ t (A+C) B=Δ t A B+Δ t C B:=by unfold seam hotPair whisper; simp only [add_mul,add_apply,inner_add_right]; ring
lemma seam_add_right (A C B:V) : Δ t A (C+B)=Δ t A C+Δ t A B:=by unfold seam hotPair whisper; simp only [mul_add,add_apply,inner_add_right]; ring
lemma seam_smul (z:ℂ)(A B:V) : Δ t (z • A) B=z*Δ t A B:=by unfold seam hotPair whisper; simp only [smul_mul_assoc,smul_apply,inner_smul_right]; ring
lemma seam_smul_right(z:ℂ)(A B:V): Δ t A (z • B)=z*Δ t A B:=by unfold seam hotPair whisper; simp only [mul_smul_comm,smul_apply,inner_smul_right]; ring
include q
lemma arm_cost (A:V): ‖a A‖≤2*‖A‖:=by
 have hv:= feel_unit S v q; have ht:= A.le_opNorm v; rw [q.unit,mul_one] at ht; let X(v'):ℂ:=inner ℂ v v'
 apply (norm_sub_le ..).trans; rw [norm_smul,q.unit,mul_one]; exact (add_le_add ht ((norm_inner_le_norm v (A v)).trans (by rw [q.unit,one_mul]; exact ht))).trans_eq (two_mul ..).symm
lemma arm_dagger (A:V):‖a (star A)‖≤2*‖A‖:= (arm_cost S v q _).trans_eq (by rw [norm_star])
lemma arm_sand (x y:ℝ)(F:V): a (S.sand F x y) = φ x (a F):=by change φ x (F (φ y v))- d (S.sand _ _ _) • v= φ x (F v-d F • v); rw [map_sub,map_smul,q.keeps,q.keeps,missed S v q] -- order
lemma arm_sand_cost (x y:ℝ)(F:V):‖a (S.sand F x y)‖ ≤ ‖a F‖:=by rw [arm_sand S v q]; exact ((φ x).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.wax_pay ..))
lemma touch (z x y:ℝ)(p:0<z)(h:z≤x)(t:z≤y)(A B:V): ‖Δ x A B- Δ y A B‖ ≤ ‖a (star A)‖ * (2/z* ‖x-y‖ * ‖a B‖):= by
 let h₀:=φ x - φ y; let c:= a (star A); let d':=a B
 rw [still_pay S v x q, still_pay S v y q, ← inner_sub_right]; change ‖inner ℂ c (h₀ d')‖ ≤ _; refine (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)); exact (h₀.le_opNorm _).trans (mul_le_mul_of_nonneg_right (S.wax_shaking p h t) (norm_nonneg _)) -- `_` with refine
lemma arm_bound (A B:V): ‖Δ t A B‖≤ ‖a (star A)‖ * ‖a B‖:=by rw [still_pay S v t q]; apply (norm_inner_le_norm ..).trans; exact mul_le_mul_of_nonneg_left (((φ t).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.wax_pay _))) (norm_nonneg _)
lemma again (r s k:ℝ)(A B C D:V)(g:‖a (star A)‖≤ r)(h:‖a B‖≤ s)(ℓ:‖C-A‖≤k)(p:‖D-B‖≤k):
 ‖Δ t C D - Δ t A B‖ ≤ 2*k*s+2*r*k+4*k^2 :=by
 let A':= C-A; let B':= D-B; have hu:0≤k:= (norm_nonneg _).trans p; have hp:‖quietArm v (star A')‖≤ 2*k:= (arm_dagger S v q A').trans (mul_le_mul_of_nonneg_left ℓ zero_le_two); have hy:‖quietArm v B'‖≤2*k:=(arm_cost S v q B').trans (mul_le_mul_of_nonneg_left p zero_le_two)
 rw [show Δ t C D - Δ t A B= Δ t A' B+ Δ t A B'+Δ t A' B' from by nth_rw 1 [show C=A'+A from (sub_add_cancel ..).symm]; nth_rw 1 [show D=B'+B from (sub_add_cancel ..).symm]; rw [seam_add,seam_add_right,seam_add_right]; abel]
 have y:0≤r:= (norm_nonneg _).trans g; have g₁:= (arm_bound S v t q A' B).trans (mul_le_mul hp h (norm_nonneg _) (by positivity)); have g₂:= (arm_bound S v t q A B').trans (mul_le_mul g hy (norm_nonneg _) y); have g₃:= (arm_bound S v t q A' B').trans (mul_le_mul hp hy (norm_nonneg _) (by positivity)); exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add g₁ g₂)) g₃).trans_eq (by ring))
end YM.OS.Semigroup.Marble
