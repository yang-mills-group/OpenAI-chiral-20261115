import YM.CF.Lattice.Reference
import YM.CF.Reflect.Annual

/-! Intrinsic unsquared far bra and initial pairing terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
section algebra
variable {n : Type*} [LinearOrder n] [Fintype n]
lemma seed_add (s : Finset n) (U V) : seedR s (U+V)=seedR s U+seedR s V := by unfold seedR; rw [star_add]; simp only [mul_add,add_mul,dyad_plus,smul_add]; abel
lemma crop (A : Op n) (s S : Finset n) : cutM s * (cutM S * A * cutM S) * cutM s=cutM (s∩S)*A*cutM (s∩S) := by
  ext i j
  -- pinch before? specialized
  unfold cutM; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul,mem_inter]; by_cases h:i∈s <;> by_cases g:i∈S <;> by_cases k:j∈s <;> by_cases u:j∈S <;> simp [h,g,k,u]
lemma letter (s S : Finset n) (A : Op n) : Sector S false (seedR s (cutM S*A*cutM S)) := by
  unfold seedR; apply Sector.scale; apply Sector.add
  · rw [star_mul,star_mul, (cutM_idp S).isSelfAdjoint,←mul_assoc (cutM S), crop] -- tune
    unfold dyad; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _
    by_cases h : i∈S∧ j∈S; exact ((Sector.down _ h.1).mul (Sector.down _ h.2)).scale _
    unfold cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; simp only [mem_inter]; split_ifs <;> first | tauto | (simp <;> apply Sector.zero)
  rw [crop]; unfold dyad; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _
  by_cases h : i∈S∧ j∈S; exact ((Sector.up _ h.1).mul (Sector.up _ h.2)).scale _
  unfold cutM; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]; simp only [mem_inter]; split_ifs <;> first | tauto | (simp <;> apply Sector.zero)
lemma stamp_twist (U : UNI n) (s t : Finset n) (h : twist U (cutM s)=cutM t) (A : Op n) : congrC U (cutM s*A*cutM s)= cutM t*congrC U A*cutM t := by
  have he := board_twist U (cutM s) A; rw [h] at he; simpa only [body,cut_real] using he.symm
@[fun_prop] lemma continuous_seed (s : Finset n) : Continuous (seedR s) := by
  have he (u v : FN n) (f : Op n→Op n) (h : Continuous f) : Continuous (fun x=>dyad (f x) u v) := continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> (h.matrix_elem i j).smul continuous_const
  unfold seedR; refine Continuous.smul (continuous_const (y:=(2:ℂ)⁻¹)) (Continuous.add ?_ ?_) <;> apply he
  · exact (continuous_const.mul continuous_id.star).mul continuous_const
  exact (continuous_const.mul continuous_id).mul continuous_const
end algebra

variable {m B : Side} (i : Axis)
lemma opens_pair {x y : Pack m B} (h : NorthOf m B i x y) : Ledge m B i* pair m B x.1 x.2 * Ledge m B i = Ledge m B i * pair m B y.1 y.2 * Ledge m B i := by
  ext r s; rw [Ledge,pinch,pinch]; split_ifs with e
  · unfold pair bow Cfield; simp only [jump_apply,Equiv.refl_apply]; split; swap; rfl
    apply congrArg (fun z:Vect=> localPair z r.2 s.2)
    have hp := (holder i r.1).mp ((colony_at r i).mp e.1); let z := node r.1
    obtain ⟨a,hz,w⟩ := full_r m B z
    have ht : a ∈ seaM m i := by
      by_contra g; have hh := (plane_all a i).resolve_left g; have hx := plane_room i ((plane_turn a i).mpr hh) ((roomA (slideM m i) a z).mpr hz)
      have H : node r.1∈ downField m B i := (return_north ..).mp hx; exact (no_fence ..).mp H ((colony_at r i).mp e.1)
    apply paint_local (s:=slot m x.2) (U:=x.1) (t:=slot m y.2) (V:=y.1) a hz (stick 0) (fun _ g e=>h.gaugeS _ (plane_room i ht g) (plane_room i ht e)) _
    intro i p; exact h.labels _ (level_keep _ ht (mem_filter.mpr ⟨mem_univ _,room_active hz p⟩))
  rfl
lemma field_sector (x:Site (CSide m B)→Vect) : let P := Ledge m B i; Commute P (Cfield x) := by
  intro P; change Commute (Ledge m B i) _; unfold Ledge cutM Cfield Commute SemiconjBy; ext y z; rw [Matrix.diagonal_mul,Matrix.mul_diagonal,jump_apply]; by_cases t:y.1=z.1
  · have hp : y∈colony m B i ↔ z∈colony m B i := by rw [colony_at,colony_at,t];
    split_ifs <;> first | tauto | simp
  rw [if_neg (show Equiv.refl _ y.1 ≠ z.1 from t)]; simp
lemma two_fields (x : Pack m B) :
    let A:= pair m B x.1 x.2; A=Ledge m B i*A*Ledge m B i+ Tedge m B i*A*Tedge m B i := by
  intro A; rw [etp]; have hp : IsStarProjection (Ledge m B i) := cutM_idp _; let P := Ledge m B i
  have he : P*A=A*P := ((field_sector (m:=m) (B:=B) i (grain _ _ _ _ _))).eq -- tune
  change A=P*A*P + _; rw [he,mul_assoc,hp.isIdempotentElem,show (1-P)*A=A-A*P by rw [sub_mul,one_mul,he]]; change A=A*P+(A-A*P)*(1-P); rw [mul_sub,mul_one,sub_mul,mul_assoc A,hp.isIdempotentElem,sub_self,sub_zero,add_sub_cancel]
abbrev Slater (m B : Side) (i : Axis) (x : Pack m B) := seedR (upperP (CSide m B)) (Ledge m B i* pair m B x.1 x.2* Ledge m B i)
lemma initial_think {e : ℝ} (b:Room B e) {x:Pack m B} (p:x∈payer m B e) :
    seedR (upperP (CSide m B)) (pair m B x.1 x.2)=Slater m B i x+theta (finger m B i) (Slater m B i (Pbar m B i x)) := by
  let F := pair m B x.1 x.2; let Y := Pbar m B i x; let X := pair m B Y.1 Y.2; let U := finger m B i; let S := colony m B i; let P := cutM S
  have hx : congrC U X=F := by
    nth_rw 1 [show F=pair m B (Pbar m B i Y).1 (Pbar m B i Y).2 by unfold F Y; rw [rpbar]] -- tune
    exact (shade_pin (slideM m i) Y.1 (slot m Y.2) _ i).symm
  have hp : Xᵀ= -X := (kappa (0:Phase.Part m B) b ((dominated (slideM m i) x p).1) ((dominated (slideM m i) x p).2)).2.1
  have he : (P*X*P)ᵀ= -(P*X*P) := by unfold P; simpa only [self_t] using skew_form (A:=cutM S) hp
  nth_rw 1 [two_fields (m:=m) (B:=B) i x]; change seedR _ (_+_) = _+theta U (seedR _ (P*X*P)); rw [seed_add,theta_seed _ U _ (slide_plus i) he,stamp_twist U S _ (movedCol ..),hx]; rfl
lemma harvest_x {x : Pack m B} {c : Phase.Part m B} {e : ℝ} (h : Room B e) (g:x∈payer m B e) : pairWave (n:=Xmind m B) (pair m B x.1 x.2)= acts (exp (seedR (upperP (CSide m B)) (pair m B x.1 x.2))) (linearB (CSide m B)) := harvest (grain _ _ _ _ _) (grain_unit h g.1 (show Verified m B margin _ _ {0} from g.2) (stick_in _ (mem_singleton_self _)))
lemma initial_sector (i) (x:Pack m B) : Sector (colony m B i) false (Slater m B i x) := letter ..
end YM.CF.RP
