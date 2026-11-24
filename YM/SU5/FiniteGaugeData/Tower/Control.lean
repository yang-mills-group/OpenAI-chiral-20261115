import YM.SU5.FiniteGaugeData.Tower.Base
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

/-!
Dual-norm compatibility with arbitrary approximations. One `CrimsonLine` per
course/Universal, unchanged observer-independent selection of scales; rates
include ferry and embedding qualification; cone errors to this E at that rate
uniform over EVERY mark with these support / host or native op bounds; spectra
for moving boxes and levels on a further common thinning of those (coefficient
or support rescalings allowed). We record both the comparison to E at the
approximating mark and the cost to transfer the answer from the mark itself
(i.e. under a vanishing approximation error measured at a host; for same
support / moving support). The election has fixed Λ.x as in Base.coupling_clock,
no changing the coupling with box or probe in these scalings.
-/

section family
variable (K₁:Calibration)(S:Finset Cover)
private lemma evaluation (F:Family K₁)(a:Evens S→Purse S)(e:F=∑ t:Evens S,note K₁ (a t).val (tagWord S t.val))
    (A:ℝ)(h:∀ t:Evens S,∀ x:PairsC, ‖(a t).val x‖≤A): pay F ((Fintype.card (Evens S):ℝ)*A):=by
 intro m x; rw [e]; simp_rw [Finset.sum_apply]; exact ((norm_sum_le ..).trans (Finset.sum_le_sum fun t _=>(pitched K₁ (tagWord S t.val) (a t).val m x).trans (h ..))).trans (le_of_eq (by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]))
lemma concern {F:Family K₁}(p:InTest K₁ true S false F){m:Side}(w:Hosp S (K₁.c m))(A:ℝ)(h:∀ x, ‖F m x‖≤A) : pay F ((Fintype.card (Evens S):ℝ)*A):=by
 obtain ⟨c,v⟩:= circulation S K₁ p; exact evaluation K₁ S F c v A (ruby S K₁ F c v w A h)
lemma box_ext {F G:Family K₁}(p:InTest K₁ true S false F)(v:InTest K₁ true S false G){m:Side}(w:Hosp S (K₁.c m))(h:F m=G m):F=G:=by
 apply sub_eq_zero.mp; have hp:= concern K₁ S (InTest.subOp p v) w 0 (by intro x; rw [Pi.sub_apply,h,sub_self, Pi.zero_apply, norm_zero])
 funext n x; exact norm_eq_zero.mp (le_antisymm ((hp n x).trans (by rw [mul_zero])) (norm_nonneg _))
end family

section cone
local notation "Sx" n:max t:max=> sharp Y H s n t
local notation "ζ" => tent Y H
local notation "Ω" s:max n:max=> (ζ).c (momentm Y n s)

def Charges (S:Finset Cover)(A:ℝ):Prop:=0≤A ∧ ∀ᶠ t:ℕ in atTop, ∀ n:ℕ,(Y.voyage n).kick ≤ t→ ∀ (f:Family (tent Y H)), InTest (tent Y H) true S false f→ ∀ C:ℝ, (∀ x, ‖f (momentm Y n s) x‖≤C)→ ‖(Sx n t) f‖ ≤ A*C

lemma charged (S:Finset Cover):∃ A:ℝ, Charges Y H s S A:=by
 obtain ⟨D,h,A⟩:= Homes Y H s S; refine ⟨D,h.le,?_⟩
 filter_upwards [A] with t v n u f p C x
 unfold sharp
 apply (v n u _ (p.support _)).trans (mul_le_mul_of_nonneg_left ?_ h.le)
 unfold cash; exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _)) (integrable_const C) (Filter.Eventually.of_forall fun i=> (x _))).trans (by simp)

include V
lemma Charges.limited {S:Finset Cover}{A:ℝ}(a:Charges Y H s S A)(f:Family (tent Y H))(p:InTest (tent Y H) true S false f)(C:ℝ):
 (∀ n, (∀ x, ‖f (momentm Y n s) x‖≤C)→‖I s f n‖≤ A*C) ∧ ((∀ᶠ r in atTop,∀ x, ‖f (momentm Y (i r) s) x‖≤C)→ ‖E s f‖≤ A*C):=by
 have hi:=V.together s f (aux_test p)
 have ht (n)(x:∀ x, ‖f (momentm Y n s) x‖≤C): ‖I s f n‖≤A*C:=by
    apply le_of_tendsto (hi.inner n).norm
    filter_upwards [V.pick.pass Y H s n,V.pick.grow_k.tendsto_atTop.eventually a.2] with r u v
    exact v n u.depth _ p C x
 refine ⟨ht, fun w=>?_⟩
 apply le_of_tendsto hi.periods.norm; exact w.mono fun i=>ht _
omit V
noncomputable def toll (S:Finset Cover):ℝ:=(charged Y H s S).choose
lemma toll_pays (S:Finset Cover):Charges Y H s S (toll Y H s S):=(charged Y H s S).choose_spec
local notation "D" b:max=> toll Y H s b
local notation "D'" b:max=> (toll Y H s b*(Fintype.card (Evens b):ℝ))
include V
lemma E_bound (S:Finset Cover){F:Family (tent Y H)} (p:InTest K true S false F){C:ℝ}(h:pay F C): ‖E s F‖≤D S*C:= (Charges.limited Y H V s (toll_pays Y H s S) F p C).2 (Eventually.of_forall fun r=> h _)
lemma I_bound (S:Finset Cover){n}{F:Family (tent Y H)} (p:InTest K true S false F){C:ℝ}(h:∀ x, ‖F (momentm Y n s) x‖≤C):‖I s F n‖≤D S*C:=(Charges.limited Y H V s (toll_pays Y H s S) F p C).1 _ h
lemma E_compare {S: Finset Cover}{f g:Family (tent Y H)}(p:InTest K true S false f)(u:InTest K true S false g)(m:Side)(z:Hosp S ((K).c m))(A:ℝ)(h:∀ x, ‖f m x-g m x‖≤A):‖E s f-E s g‖ ≤ D' S*A:=by
 rw [← E_sub Y H V s (aux_test p) (aux_test u)]; exact (E_bound Y H V s S (InTest.subOp p u) (concern (tent Y H) S (InTest.subOp p u) z A h)).trans_eq (mul_assoc ..).symm
lemma I_compare {S: Finset Cover}{f g:Family (tent Y H)}(p:InTest K true S false f)(u:InTest K true S false g)(m:Side)(z:Hosp S ((K).c m))(A:ℝ)(h:∀ x, ‖f m x-g m x‖≤A)(n:ℕ):‖I s f n-I s g n‖ ≤ D' S*A:=by
 rw [← I_sub Y H V s (aux_test p) (aux_test u)]; exact (I_bound Y H V s S (InTest.subOp p u) ((concern (tent Y H) S (InTest.subOp p u) z A h) _)).trans_eq (mul_assoc ..).symm

omit V
structure CrimsonLine (q:ℕ→ℕ) : Prop where
  grows : StrictMono q
  budget (s:ℕ)(S:Finset Cover): ∀ᶠ r in atTop,
    let t:=momentm Y (i (q r)) s
    Hosp S ((tent Y H).c t) ∧ (∀ j,legacy Y (i (q r)) (k j)→ Ferry Y s (i (q r)) (k j))∧
    ∀ (f:Family (tent Y H)), InTest (tent Y H) true S false f→ ∀ A:ℝ, (∀ x, ‖f t x‖≤A)→
      ‖I s f (i (q r))-E s f‖ ≤ (1/2:ℝ)^r*A ∧
      ∀ j, legacy Y (i (q r)) (k j)→ ‖sharp Y H s (i (q r)) (k j) f-E s f‖ ≤ (1/2:ℝ)^r*A
include V
lemma purchase_line :∃ q, CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q:=by
 obtain ⟨q,p,t⟩:= crimson Y H V
 refine ⟨q,p,fun s S=>?_⟩
 filter_upwards [p.tendsto_atTop.eventually (floor_pays Y H V s), t S s] with i u v; exact ⟨v.1,u,v.2⟩

variable {q:ℕ→ℕ}(Q:CrimsonLine (i:=i) (k:=k) (I:=I) (E:=E) Y H q)
omit V
include Q
open Filter
lemma CrimsonLine.approx (S:Finset Cover):
 ∀ᶠ r:ℕ in atTop, let M:=i (q r); let F:= momentm Y M s
 Hosp S ((tent Y H).c F) ∧ (∀ j,legacy Y M (k j)→
   Ferry Y s M (k j) ∧
   (((Y.voyage M).X (Y.uv (k j))).gram 0).beta=Λ.x ∧
   (∀ f: Family (tent Y H), TestFamily K true f→
      let a:=send Y H M s (f F); let v:= ((Y.voyage M).X (Y.uv (k j))).gram s; let T:=(Y.voyage M).CapeT s; let Z:= partitionZ v Λ.U T
      Integrable (fun x=> inner ℂ (Dial.mateK (side Y M s)) (acts (a (drawn T x)) (denZ v Λ.U T x))) (city (side Y M s)) ∧ Z≠0 ∧
      sharp Y H s M (k j) f=(∫ x, inner ℂ (Dial.mateK (side Y M s)) (acts (a (drawn T x)) (denZ v Λ.U T x)) ∂city (side Y M s))/Z))∧
 (∀ (f:Family K), InTest K true S false f → ∀ m:Side, Hosp S ((tent Y H).c m)→ ∀ A:ℝ, (∀ x, ‖f m x‖≤A)→
 ‖I s f M-E s f‖ ≤ (1/2:ℝ)^r*((Fintype.card (Evens S):ℝ)*A) ∧
 ∀ j,legacy Y M (k j)→ ‖sharp Y H s M (k j) f-E s f‖≤ (1/2:ℝ)^r*((Fintype.card (Evens S):ℝ)*A)):=by
 filter_upwards [Q.budget s S] with r p
 refine ⟨p.1,fun j h=> ?_,fun f h m t A a=> p.2.2 _ h _ (concern K S h t A a _)⟩
 have h₁:= p.2.1 j h
 exact ⟨h₁,(coupling_clock Y _ _ h₁.depth).1, fun F v=> Journey.paid Y H s (p:=h₁) v⟩
include V
-- vary BOTH regulatory mark and target (must be represented as family over
-- all periods, even if only evaluated on one. Next: extension from periodic
-- `AtSupport`). host for comparison may depend on r. Rhs second term
-- not scaled by r; must pay approximation at the *same level/box* there.
lemma CrimsonLine.interpolate (S:Finset Cover):
 ∀ᶠ r in atTop, let M:=i (q r); let T:=momentm Y M s
 ∀ (f g:Family (tent Y H)), InTest K true S false f→InTest K true S false g→
 ∀ (C:ℝ), (∀ x, ‖f T x‖≤C)→
 ∀ (m:Side), Hosp S ((tent Y H).c m)→∀ A:ℝ, (∀ x, ‖f m x-g m x‖≤A)→
 ‖I s f M-E s g‖≤ (1/2:ℝ)^r*C+D' S*A ∧
 ∀ j, legacy Y M (k j)→ ‖sharp Y H s M (k j) f-E s g‖≤ (1/2:ℝ)^r*C+D' S*A:=by
 filter_upwards [Q.budget s S] with r p
 intro M T f g x y C v m z A e
 have ht:=p.2.2 f x C v; have he:=E_compare Y H V s x y m z A e
 exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add ht.1 he),fun j k=> (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (ht.2 _ k) he)⟩

-- and analog for all sufficiently fitting *fixed* Y periods on the UV
-- sequence: convergence in norm there. UV threshold additionally depends on n.
omit Q
lemma interpolate_UV (S:Finset Cover):
 ∀ᶠ n in atTop, ∀ ε:ℝ,0<ε→∀ᶠ j in atTop,
   Ferry Y s n (k j) ∧
   ∀ f g:Family K, InTest K true S false f→ InTest K true S false g→
   ∀ (m:Side), Hosp S ((K).c m)→∀ C A:ℝ, (∀ x, ‖f m x‖≤C)→(∀ x, ‖f m x-g m x‖≤A)→
   ‖sharp Y H s n (k j) f-I s g n‖≤ ε*C+D' S*A:=by
 filter_upwards [(boutique Y H V S s).1] with n p ε he
 filter_upwards [p ε he,V.pick.pass Y H s n] with j a u
 exact ⟨u,fun f g h w m x C A b d=> (norm_sub_le_norm_sub_add_norm_sub (sharp Y H s n (k j) f) (I s f n) _).trans (add_le_add (a f h m x C b) (I_compare Y H V s h w m x A d n))⟩ -- let binder?

include Q
lemma CrimsonLine.identify_target {S:Finset Cover}{f:ℕ→Family K}{g:ℕ→Family K}(hf:∀ t,InTest K true S false (f t))(hg:∀ t,InTest K true S false (g t))
    (C A:ℕ→ℝ)(e:Tendsto (fun r:ℕ=>(1/2:ℝ)^r*C r) atTop (𝓝 0))(a:Tendsto A atTop (𝓝 0))
    (u:∀ᶠ r in atTop,let n:=momentm Y (i (q r)) s; ∀ x, ‖f r n x‖≤C r)
    (v:∀ᶠ r in atTop,∃ m:Side, Hosp S ((K).c m)∧∀ x, ‖f r m x-g r m x‖≤A r)
    (j:ℕ→ℕ)(h:∀ᶠ r in atTop,legacy Y (i (q r)) (k (j r))):
    Tendsto (fun r=>I s (f r) (i (q r))-E s (g r)) atTop (𝓝 0) ∧
    Tendsto (fun r=>sharp Y H s (i (q r)) (k (j r)) (f r)-E s (g r)) atTop (𝓝 0):=by
 have ht:Tendsto (fun r:ℕ=>(1/2:ℝ)^r*C r+D' S*A r) atTop (𝓝 0):=by simpa using e.add (a.const_mul (D' S))
 have hp:= (((Q.interpolate Y H V s S).and u).and v).and h
 constructor
 · rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ ht; filter_upwards [hp] with r ⟨⟨⟨t,p⟩,⟨m,g₁,g₂⟩⟩,d⟩; exact (t _ _ (hf r) (hg r) (C r) p m g₁ (A r) g₂).1
 rw [tendsto_zero_iff_norm_tendsto_zero]; apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ ht; filter_upwards [hp] with r ⟨⟨⟨t,p⟩,⟨m,g₁,g₂⟩⟩,d⟩; exact (t _ _ (hf r) (hg r) (C r) p m g₁ (A r) g₂).2 _ d
end cone

end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.CrimsonLine.interpolate
