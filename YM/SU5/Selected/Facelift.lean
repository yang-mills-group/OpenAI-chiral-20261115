import YM.SU5.Selected.Faceted
/-! # DCT for tint. On selection data. General lemma for other preparations too.
Do not need past weights to vanish simultaneously. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 400000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Vacancy
open Buffered.Reliance Buffered.Reliance.ShortWave
open CF.Pannier.Chancel
open Buffered.Concord (Meter meter_p meter_time)
open Dial -- tune
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (C : Arena Y H Q.circuit 0 0 false)
variable (L : Finset (Face ℤ)) (S : Finset Cover) (p : restsOn L S)
local notation "T" x:max => tintMark L (Meter x) (tent Y H)
local notation "A" => actor Y H s Q.circuit 0 0 false C
local notation "π" => (Aurora Y H V Q 0 false C).orthogonalProjectionOnto
local notation "Ω" => seat0 Y H V Q 0 false C
local notation "φ" x:max => located Y H V s Q Qt 0 false C x
variable {J : Calibration} {x : Family (tent Y H)} {a' C' : ℝ}
open Branch -- tune

include V
/-- General continuity of marked E on fixed box and rung with *envelope* support,
vanishing eventually ae of answers at all the testing rooms (don't even test all uncountably
many fields jointly across m). -/
lemma low_cost_vanish (f : ℕ → Family (tent Y H)) (h : ∀ i,InTest (tent Y H) true S false (f i))
    (a : ℝ) (l' : 0<a) (w : ∀ i,pay (f i) a)
    (p : ∀ v m: ℕ, Ferry Y s v m→Tendsto (fun i=>sharp Y H s v m (f i)) atTop (𝓝 0)) :
    Tendsto (fun i=>E s (f i)) atTop (𝓝 0) := by
 refine Metric.tendsto_nhds.mpr fun ε e=> ?_
 let z:= (ε/2)/a; have he:0<z:=by unfold z; positivity
 obtain ⟨v,K₀,l,t⟩:= (((Satin.boutique Y H V S s).2 z he).and ((floor_pays Y H V s).and (hosp_later Y H V s S))).exists
 obtain ⟨m,_,u⟩:= legacy_above Y H V v 0
 have hQ (j:ℕ): ‖sharp Y H s (i v) (k m) (f j)-E s (f j)‖ ≤ z*a:= (K₀ (f j) (h j) (momentm Y (i v) s) t a (w j _)).2 m u
 filter_upwards [Metric.tendsto_nhds.mp (p (i v) (k m) (l m u)) (ε/2) (half_pos e)] with j hj
 rw [dist_zero_right] at hj ⊢; have hs:=hQ j; rw [show z*a=ε/2 from div_mul_cancel₀ _ l'.ne'] at hs
 have hx:= norm_le_norm_sub_add (E s (f j)) (sharp Y H s (i v) (k m) (f j)); rw [norm_sub_rev] at hx; linarith

omit V
open Skye Tapestry
lemma vanish_loom {M n : Side} (F : ℕ → Family J) (w : J.c M=n) (S : Finset Cover)
    (p : ∀ x, InTest J true S false (F x)) (a : ℝ) (h : ∀ r,pay (F r) a)
    (l : Loom n) (d : Orbit n→ Phys n) (u : Measurable l) (e : Integrable d (city n))
    (δ : ℂ)
    (q : ∀ᵐ z∂city n,∀ᶠ i:ℕ in atTop, (w ▸ F i M : Mark n) (drawn l z) = 0) :
    Tendsto (fun i => markedRead (w ▸ F i M) l d/δ) atTop (𝓝 0) := by
  subst n; let L₀ := fun (i:ℕ) (z:Orbit (J.c M))=> letterRead (F i M (drawn l z)) (d z)
  have he:Tendsto (fun i=> ∫ z,L₀ i z∂city (J.c M)) atTop (𝓝 (∫ _z:Orbit _,(0:ℂ)∂city (J.c M))) := by
    apply tendsto_integral_of_dominated_convergence (fun z=> a*‖d z‖) (fun i=> (mark_integrable u ((p i).support M).env e).aestronglyMeasurable) (e.norm.const_mul _)
    · exact fun i=> Eventually.of_forall fun z=> (mark_bound ..).trans (mul_le_mul_of_nonneg_right (h ..) (norm_nonneg _))
    filter_upwards [q] with z h; apply tendsto_const_nhds.congr'
    apply h.mono; intro i hi; change 0=letterRead (F i M (drawn l z)) (d z); rw [show F i M (drawn l z)=0 from hi]; exact (le_antisymm (by simpa using mark_bound 0 (d z)) (norm_nonneg (letterRead 0 (d z)))|> norm_eq_zero.mp).symm
  change Tendsto (fun i=> (∫ z,L₀ i z∂city (J.c M))/δ) atTop (𝓝 0); rw [integral_zero] at he; simpa only [zero_div] using he.div_const δ -- tune

abbrev unveil (x : Family (tent Y H)) (m : ℕ) := (T m)*x - x
local notation "X" n:max => unveil Y H L x n
include p in
lemma corner_tests (h : InTest (tent Y H) true S false x) (u : ℕ) : InTest (tent Y H) true S false (unveil Y H L x u) := by
 unfold unveil; rw [sub_eq_add_neg,←neg_one_smul ℂ x]; exact (((tint_price L S _ K p).widen).mul h).add (h.smul _) -- tune
lemma layered_budget (u : ℕ) : pay (T u) 1 := by
 intro i p; rw [tint_here,norm_smul,norm_one,mul_one,Complex.norm_real, Real.norm_of_nonneg (clay_nonneg ..)]; exact clay_inside ..
lemma layered_cost (v:pay x a') (n : ℕ) : pay (unveil Y H L x n) (1*a'+a'):=pay_sub (pay_mul (layered_budget Y H L n) v) v
lemma gap_is_nil {M n : Side} (w : (tent Y H).c M=n) (ℓ : Loom n) :
    ∀ᵐ z ∂city n,∀ᶠ i:ℕ in atTop, (w ▸ (unveil Y H L x i M) : Mark n) (drawn ℓ z) = 0 := by
  subst n
  have ht (f : Face ℤ) : ∀ᵐ z∂city ((K).c M),0 < SU.group.chord (faceValue (onC _ z.1) f):= by
    simp_rw [tile_face]; exact CF.Signal.Showcasing.displacement ..
  have hm : Tendsto (fun n:ℕ=> (2:ℝ)*Meter n) atTop (𝓝 0):=by simpa using meter_time.const_mul (2:ℝ)
  filter_upwards [Finset.eventually_all L|>.mpr (fun f _=> ht f)] with z h
  filter_upwards [Finset.eventually_all L|>.mpr (fun f g=> hm.eventually (ge_mem_nhds (h f g)))] with i v
  change tintMark L (Meter i) K M (drawn ℓ z)*x M _ - x M _=0
  rw [tint_here L]; rw [show (drawn ℓ z).1=z.1 from rfl, clay_some L (Meter i) _ (meter_p i) v, Complex.ofReal_one,one_smul,one_mul,sub_self]
lemma gap_both {M n : Side} (w : (tent Y H).c M=n) (ℓ : Loom n) :
    ∀ᵐ z ∂city n,∀ᶠ i:ℕ in atTop, (w ▸ ((mirror (tent Y H) 0 0 (unveil Y H L x i))*(unveil Y H L x i)) M : Mark n) (drawn ℓ z)=0:=by
  subst n; filter_upwards [gap_is_nil (M:=M) (x:=x) Y H L rfl ℓ] with i p; filter_upwards [p] with j hj
  change (mirror K 0 0 (X j) M _)*((X j) M (drawn ℓ i))=_; rw [show (X j) M (drawn ℓ i) = _ from hj,mul_zero]
include V p
lemma vignette (u : InTest (tent Y H) true S false x) :
    Tendsto (fun i=> E s (mirror (tent Y H) 0 0 (unveil Y H L x i)*(unveil Y H L x i))) atTop (𝓝 0):=by
  obtain ⟨a,w⟩:= Journey.valuation Y H u; have ht:pay x a:=w; let v:= (1*a+a)*(1*a+a)+1; have h:a≥0:=pay_nonneg ht
  let S₁:= reflectedBox 0 0 S∪ S
  let G:= fun i=> mirror (tent Y H) 0 0 (X i)*(X i)
  have ha i:InTest (tent Y H) true S₁ false (G i):= ((axial _ 0 0 (corner_tests Y H L S p u i)).mono subset_union_left).mul ((corner_tests Y H L S p u i).mono subset_union_right)
  have he i:pay (G i) v:= fun m y=> ((pay_mul (pay_flips K (layered_cost Y H L ht i) 0 0) (layered_cost Y H L ht i)) m y).trans (by unfold v; linarith) -- last `linarith`
  apply low_cost_vanish Y H V s S₁ G ha v (by unfold v; positivity) he
  intro r k h; let ℓ:=(Y.voyage r).CapeT s; let ht:=terrain Y H (Y.ir r) s
  exact vanish_loom G ht S₁ ha v he ℓ _ ((Y.voyage r).ownership s).paid.bill (LocalLimit.Marks.can_read _ _ _ _ h.fire.priceA) _ (gap_both Y H L _ _) -- args
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.vignette
