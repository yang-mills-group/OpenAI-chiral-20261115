import YM.SU5.FiniteGaugeData.LocalLimit.Local.Space
import YM.SU5.FiniteGaugeData.LocalLimit.Local.Digest

/-! # Precompact functionals on L¹ of this gauge-local domain

Here norm-comparing via distances on the whole image of that compact-smoothing
production step. Equips unit test bank with *discrete* topology to aid use of sup distance
(not claiming the measured functionals continuous in product topology applied to
pointwise gauge tests; instead through the digest distance, or the L¹ norm, etc.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox.BoxGauge
open RG Lattice Wilson Filter MeasureTheory Function
open scoped Topology BigOperators Classical BoundedContinuousFunction
variable {G:Gauge}(r:ℕ) {c f:Side} (S:StepData c f) (v:ℝ) 
def Ticket (G:Gauge)(r:ℕ) := {x : ↥(paper G r) // weight r x ≤ 1}
def Ticket.val {r:ℕ} (t : Ticket G r) : paper G r := Subtype.val t
lemma Ticket.cap (t : Ticket G r) : weight r t.val ≤ 1:=Subtype.property t
instance : TopologicalSpace (Ticket G r) := ⊥
instance : DiscreteTopology (Ticket G r) := ⟨rfl⟩
abbrev Record (G:Gauge)(r:ℕ) := Ticket G r →ᵇ ℂ
structure Used (F₀: ↥(paper G r)→ℂ) (l:ℝ) : Prop where
 plus (A B : _) : F₀ (A+B)=F₀ A+F₀ B
 scalar (A : _) (c':ℂ): F₀ (c' • A)= c' * F₀ A
 charge(A : _): ‖F₀ A‖ ≤ l*‖digest r S v A‖
local notation "F" x => digest r S v x
namespace Used
variable {f₀ g : ↥(paper G r)→ℂ}{l:ℝ}(p : Used r S v f₀ l)
include p
private lemma linear : ∀ P Q,f₀ P - f₀ Q=f₀ (P-Q):= by
 intro P Q; have hu:=p.plus (P-Q) Q; rw [sub_add_cancel] at hu; rw [hu]; abel
lemma ext_lip (x x': Ticket G r): dist (f₀ x.val) (f₀ x'.val) ≤ l*dist (digest r S v x.val) (digest r S v x'.val) := by
 simp_rw [dist_eq_norm,linear _ _ _ p,← map_sub]; exact p.charge _
omit p
abbrev height (G:Gauge):= (digest_norm (G:=G) r S v).choose -- circular field naming?
lemma high_p : 0 ≤ height r S v G:= (digest_norm ..).choose_spec.1
include p
lemma unitBill (h:0≤l)(x:Ticket G r): ‖f₀ x.val‖ ≤ l*height r S v G :=
 (p.charge _).trans (mul_le_mul_of_nonneg_left (((digest_norm ..).choose_spec.2 x.val).trans (mul_le_of_le_one_left (high_p ..) (x.cap r))) h)
def bank (f₀:↥(paper G r)→ℂ) (p:Used r S v f₀ l)(h:0≤l): Record G r:= BoundedContinuousFunction.mkOfDiscrete (fun x : Ticket G r=>f₀ x.val) (2* (l*height r S v G)) (fun i j=> by linarith [dist_le_norm_add_norm (f₀ i.val) (f₀ j.val), unitBill _ _ _ p h i, unitBill _ _ _ p h j]) -- include p issues
lemma rate (hk:0 ≤ l) : ‖bank r S v f₀ p hk‖ ≤ l*height r S v G := (BoundedContinuousFunction.norm_le (mul_nonneg hk (high_p _ _ _))).mpr (fun x=> unitBill _ _ _ p hk x)

-- explicit card-vs-operator inequality, including case of null L¹. Sup convergence on Record buys
-- exactly `δ*weight` on all boxes; no more input approximations needed.
lemma zero_reads (x:paper G r)(t:weight r x=0):f₀ x=0:= by
 have h:= (digest_norm r S (G:=G) v).choose_spec.2 x; rw [t,zero_mul] at h; have he:= p.charge x; rw [norm_le_zero_iff.mp h,norm_zero,mul_zero] at he; exact norm_le_zero_iff.mp he
lemma see {v':ℝ}(h:0≤l)(q:Used r S v g l)(hp:dist (bank r S v f₀ p h) (bank r S v g q h) ≤ v') (x:paper G r):
 dist (f₀ x) (g x) ≤ v'*weight r x := by
 rcases eq_or_lt_of_le (weight_pos r x) with t|t
 · rw [zero_reads r S v p x t.symm,zero_reads r S v q x t.symm,dist_self,←t,mul_zero]
 let W:= weight r x; let c:ℂ:= ((W⁻¹:ℝ):ℂ); have hz:‖c‖=W⁻¹:= (Complex.norm_real _).trans (Real.norm_of_nonneg (inv_nonneg.mpr t.le))
 let A:Ticket G r:= ⟨c • x,(by rw [weight_scale,hz, inv_mul_cancel₀ t.ne'])⟩
 have he:= le_trans (BoundedContinuousFunction.dist_coe_le_dist (f:=bank r S v f₀ p h) (g:=bank r S v g q h) A) hp
 change dist (f₀ (c • x)) (g (c • x)) ≤ v' at he; rw [p.scalar, q.scalar, dist_eq_norm,←mul_sub,norm_mul,hz] at he; rw [dist_eq_norm]; exact (le_trans ((inv_mul_le_iff₀ t).mp he) (le_of_eq (mul_comm ..))) -- check mathlib notation
end Used
lemma packed (G : Gauge)(l:ℝ)(h:0<l):∃ A:Set (Record G r), 0 ∈ A ∧ IsCompact A ∧ ∀ (f: ↥(paper G r)→ℂ)(p:Used r S v f l) (u), Used.bank r S v f p u∈ A:= by
 let T := fun x : Ticket G r=>digest r S v x.val; let s :=l*Used.height r S v G; let X:Set (Record G r) := {f| ‖f‖≤s ∧ ∀ i j, dist (f i) (f j) ≤ l*dist (T i) (T j)}
 have ht:IsCompact (closure (Set.range T)) := digest_compact r S v
 refine ⟨closure X, subset_closure ?_,YM.SU5.FiniteGaugeData.LocalLimit.measurements_compact _ _ h T ht,fun f p u=> subset_closure ⟨Used.rate _ _ _ p u,p.ext_lip r S v⟩⟩
 refine ⟨?_,fun x y=>?_⟩; · rw [norm_zero]; exact mul_nonneg h.le (Used.high_p ..)
 change dist (0:ℂ) (0:ℂ)≤_; rw [dist_self]; exact mul_nonneg h.le dist_nonneg
end YM.Push.GridApprox.BoxGauge
