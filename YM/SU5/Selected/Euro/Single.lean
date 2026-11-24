import YM.SU5.Selected.Euro.Palate

/-!
# Actual exposed χ component on neutral ONLY is extremal in precisely Consensus sense.
Proof lifting test below via full Leg_w, not assuming any norm-density of finite sums of
gauge translates. Applies to all born positive ground rooms. Extend to public duplicate with
`r=true` still through full χ, not assuming new vacuum. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 650000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Single
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (C : Arena Y H Q.circuit j 0 false)
local notation "R" => Aurora Y H V Q j false C
local notation "A" => Ark.Ht Y H Q.circuit j 0 false C
local notation "W" => floorV Y H Q.circuit j 0 false C
local notation "F₊" n:max => Tower.Field Y H n j 0 true
local notation "φ" n:max => actor Y H n Q.circuit j 0 false C
local notation "Ω" => seat0 Y H V Q j false C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j false C
local notation "Test" => Vacancy.observable (tent Y H) true
local notation "Lab" => Beacon (tent Y H) true

open Companies Consensus Palate
section universal
-- extend an agreeing bill on all forward rungs to a Hilbert representation.
private lemma interpolation_v {X : Type} (F : ℕ→Type) [AddCommGroup X] [Module ℂ X]
    [∀ i,AddCommGroup (F i)] [∀ i,Module ℂ (F i)] (A' : Hilbert) (g : X→ₗ[ℂ] A')
    (T : ∀ i,F i→ₗ[ℂ]X) (J : ∀ i,F i→ₗ[ℂ] ℂ) (hp:DenseRange g) (c : ℝ)
    (h : ∀ i f,‖J i f‖≤ c*‖g (T i f)‖) (p : ∀ (i : ℕ) (x : X), ∃ (k:ℕ) (f:F k), i≤k∧ T k f=x)
    (t : ∀ (i : ℕ) (k : ℕ), i≤k→∀ x,∃ y,T k y=T i x∧J i x=J k y) : ∃ L0 : A' →L[ℂ] ℂ, ∀ i x, L0 (g (T i x))=J i x := by
  have hsame (i:ℕ) (x y : F i) (p: T i x = T i y): J i x=J i y := by
    have g' := h i (x-y); rw [map_sub (T i),p,sub_self,map_zero,norm_zero,mul_zero,map_sub (J i),norm_le_zero_iff] at g'; exact sub_eq_zero.mp g'
  -- equality after common rung. may need choose ordinary operator equality.
  have hc (i k : ℕ) (x : F i) (y : F k) (a : T i x=T k y) : J i x=J k y := by
    obtain ⟨z,e,v⟩ := t i (max i k) (le_max_left ..) x
    obtain ⟨w,f,Hw⟩ := t k (max i k) (le_max_right ..) y
    exact v.trans ((hsame _ z w (e.trans (a.trans f.symm))).trans Hw.symm)
  let s (x : X):= (p 0 x).choose; let y (x : X):= (p 0 x).choose_spec.choose
  let f (x : X):= J (s x) (y x)
  have hv i x : f (T i x)=J i x:= hc _ _ _ _ (p 0 _).choose_spec.choose_spec.2
  let L0 : X→ₗ[ℂ] ℂ :=
    { toFun := f
      map_add' x y := by
        obtain ⟨u,v,_,rfl⟩:=p 0 x; obtain ⟨k,w,hu,rfl⟩:=p u y; obtain ⟨v',hw,hz⟩ := t u k hu v
        rw [←hw,←map_add,hv,hv,hv,map_add]
      map_smul' c x := by obtain ⟨u,v,_,rfl⟩:=p 0 x; rw [←map_smul,hv,hv,map_smul]; rfl }
  have hL x: ‖L0 x‖ ≤ c*‖g x‖ := by obtain ⟨u,f',_,rfl⟩:= p 0 x; change ‖f (T u f')‖≤_; rw [hv]; exact h _ _
  exact ⟨L0.extendOfNorm g, fun i x=> (LinearMap.extendOfNorm_eq hp ⟨c,hL⟩ _).trans (hv _ _)⟩

private lemma via_adjoint (A' : Hilbert) (w : A'→L[ℂ] ℂ) (v : A') : inner ℂ (w.adjoint 1) v = w v := (w.adjoint_inner_left v 1).trans (by simp)

-- contraction & invariant ON functional
private lemma still_norm (A' : Hilbert) (f : ℕ→ A'.Op) (p : ∀ i,‖f i‖≤1) (k : A') (hk : ‖k‖=1)
    (w : A'→L[ℂ] ℂ) (t:w k=1) (hw:∀ i x,w (f i x)=w x) (L : stationary A' f=Submodule.span ℂ {k}) : ∀ z, inner ℂ k z = w z := by
  let y:=w.adjoint (1:ℂ); have h y' : inner ℂ y y' = w y':= via_adjoint A' w _
  have hv : y∈ stationary A' f := by
    rw [standing A' f y p]; intro i
    apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜:=ℂ)
    · exact ((f i).le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) (p i))
    rw [inner_re_symm]
    -- re inner y,T y via conjugate
    rw [h,hw,←h,inner_self_eq_norm_sq]
  rw [L,Submodule.mem_span_singleton] at hv
  obtain ⟨c,hc⟩:=hv
  have ht := (h k).trans t; rw [←hc,inner_smul_left, inner_self_eq_norm_sq_to_K,hk] at ht
  have he : starRingEnd ℂ c = 1:= by simpa using ht
  have eh : c=1:= star_injective (show star c=star (1:ℂ) from he.trans (star_one ℂ).symm)
  intro z; rw [show k=y from (by rw [←hc,eh,one_smul]), h]

private lemma square_disc (w q : ℝ) (p : 0 < w) (u : 0 ≤ q) (a b : ℂ) (x' : ℝ)
    (c : ℝ) (v : 0≤b) (t:c^2 ≤ a.re) (g:0≤x') (e : ((x'^2:ℝ):ℂ)=(w:ℂ)*a+(q:ℂ)*b) : c≤ (Real.sqrt w)⁻¹ * x' := by
  have hs : w*(c^2) ≤ x'^2:= by
    have h:= congrArg Complex.re e; simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero] at h
    exact (mul_le_mul_of_nonneg_left t p.le).trans (by rw [h]; linarith only [(show 0 ≤ q * b.re from mul_nonneg u (Complex.le_def.mp v).1)])
  have h' := Real.sqrt_pos.2 p; have h'' := Real.sq_sqrt p.le
  rcases le_total c 0 with p'|p'
  · exact p'.trans (mul_nonneg (inv_nonneg.mpr h'.le) g)
  rw [←div_eq_inv_mul,le_div_iff₀ h']; exact (sq_le_sq₀ (mul_nonneg p' h'.le) g).mp (by rw [mul_pow,h'',mul_comm]; exact hs)
end universal
local notation "Χ" => CapCharacter Y H V Q Qc j false C
local notation "Sw" => Sample Y H true
local notation "m" χ:max => marked Y H V Q Qc j false C χ
local notation "M" s:max => liftCap Y H V Q Qc j false C s
local notation "J" => Heat.gaugeShift Λ.block
local notation "P" => pipeline Y H V Q Qc j false C
local notation "UΩ" s:max => dash Y H j s
local notation "P₀" s:max => (asLeg Y H V Q Qc j false C s).comp (UΩ s)
variable {χ : CapCharacter Y H V Q Qc j false C} (U : Birthplace Y H V Q Qc j false C χ)
local notation "η" s:max => (markedActor Y H V Q Qc j false C U s).comp (UΩ s)
local notation "ζ₀" => vacuum Y H V Q Qc j false C U
local notation "Θ" => (bottom Y H V Q Qc j false C U)
local notation "T" => phaseMoves Y H V Q Qc j false C U
variable {x y : Sample Y H true} (u : Consensus Y H Q true x) (v : Consensus Y H Q true y) (s : ℕ)
local notation "F" s:max f:max => toTest Y H j true s f
local notation "E₀" s:max f:max => x s (F s f)

def single (x : Sample Y H false) : Sample Y H true := fun i f=> x i (feel Y H f)
lemma exact_together (x:Sample Y H false)(p:Consensus Y H Q false x) : Consensus Y H Q true (single Y H x):=
 ⟨p.one,fun i v w=> p.add i (feel Y H v) (feel Y H w),fun i v z=>p.scale i (feel Y H v) z,fun i k v=>p.upward i k (feel Y H v),fun i a z v=>p.shift i a z (feel Y H v),fun i a z v=>p.flip i a z (feel Y H v),fun i a z v s t w=>p.rp i a z (feel Y H v) s t w⟩
local notation "q_m" χ:max => single Y H (m χ)
local notation "J₀" => joinedReading Y H true
include V Q Qc C U u
-- stocking bound
include v in
lemma mixture_bound (w q : ℝ) (p : 0 < w) (hq : 0≤ q) (f : F₊ s) (h : q_m χ = J₀ w q x y) : ‖E₀ s f‖ ≤ (Real.sqrt w)⁻¹ * ‖(η s) f‖ := by
  have he := congrFun (congrFun h s) (bornTest Y H j true s f f)
  have h' : inner ℂ ((η s) f) ((η s) f)=(w:ℂ)*x s (bornTest Y H j true s f f)+(q:ℂ)*y s (bornTest Y H j true s f f) :=
    (affirmation Y H V Q Qc j false C U s ((UΩ s) f) ((UΩ s) f)).trans he
  refine square_disc w q p hq _ _ _ _ (rpos Y H Q j true v s f) (dominates Y H Q j true u s f) (norm_nonneg _) (Eq.trans ?_ h')
  rw [inner_self_eq_norm_sq_to_K]; norm_cast -- tune
-- common branch
local notation "b" => schematic Y H V Q Qc j false C χ -- name b variable!
omit u U in
private lemma representative (i : ℕ) (x : P) : ∃ (t : ℕ) (f : F₊ t), i ≤ t ∧ (P₀ t) f=x := by
  exact already Y H V Q Qc j C i x
open Localization.Canton
include v in
lemma coupon (w q : ℝ) (p : 0 < w) (hq : 0≤ q) (h : q_m χ=J₀ w q x y) :
    ∃ g : U.H→L[ℂ] ℂ, ∀ s f,g ((η s) f)= E₀ s f :=
  interpolation_v (fun i=> ↑(F₊ i)) U.H ((b).bloom U) (fun i=> P₀ i) (fun i=> Consensus.read Y H Q j true u i)
    ((b).bloom_dense U) _ (fun s f=> mixture_bound Y H V Q Qc j C U u v s w q p hq f h)
    (representative Y H V Q Qc j C) (fun i k f z=> ⟨Raise Y H Q.circuit j 0 true i k f z,
      prices_migrate Y H V Q Qc j C i k f z,(Consensus.mature Y H Q j true u i z k f).symm⟩)

-- dense equalizer via born (port repeatedly)
omit u V Q Qc U C in
private lemma left_route (X : Hilbert) (F' : ℕ→Type) (Y' : ∀ t:ℕ,F' t→X) (s:ℕ) (f : X.Op) (g : X →L[ℂ] ℂ)
    (p : Dense (⋃ (v : ℕ) (_ : s≤v), Set.range (Y' v))) (h : ∀ t:ℕ,s≤t→∀ x,g (f (Y' t x))=g (Y' t x)) :
      ∀ x, g (f x)=g x := by
  intro i
  let S' := { x | g (f x)=g x }
  refine closure_minimal (t:=S') ?_ (isClosed_eq (g.continuous.comp f.continuous) g.continuous) (p i)
  intro y x; obtain ⟨v,w⟩ := Set.mem_iUnion.mp x; obtain ⟨j,x',rfl⟩ := Set.mem_iUnion.mp w; exact h _ j _
local notation "w₀" u:max => leave Y H V Q Qc j false C U (hat Y H V Q Qc j false C u)
-- exact coupon saturation unselected to selected. For all v not just typical.
omit u in
lemma born (s:ℕ) : Dense (⋃ (v : ℕ) (_ : s ≤ v), Set.range (η v)) := by
 refine (born_dense Y H V Q Qc j false C U s).mono ?_
 intro x p; obtain ⟨i,p⟩:=Set.mem_iUnion.mp p; obtain ⟨h,y,rfl⟩:=Set.mem_iUnion.mp p; obtain ⟨f,e⟩:= tastes Y H V Q Qc j C i y
 exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨h,f,congrArg ((b).bloom U) e⟩⟩
section invariant_coupon
variable (g : U.H →L[ℂ] ℂ) (h : ∀ i f, g ((markedActor Y H V Q Qc j false C U i) (dash Y H j i f))= x i (toTest Y H j true i f))
include h
lemma same_tick (z : ℕ) : ∀ x, g (walking Y H V Q Qc j false C U s z x)=g x :=
  left_route U.H (fun i=> ↑(F₊ i)) (fun i x=> (η i) x) s (walking Y H V Q Qc j false C U s z) g (born Y H V Q Qc j C U s)
    (fun i p f=> (congrArg g (tempo Y H V Q Qc j false C U s z i p ((UΩ i) f))).trans ((h i (tick Y H i j 0 true (amount Λ s i z) f)).trans ((tick_rule Y H Q j true u i f (amount Λ s i z)).trans (h i f).symm)))
lemma same_sail (v : Trans j) (z : ℤ) : ∀ x, g (travel_χ Y H V Q Qc j false C U s v z x)=g x :=
  left_route U.H (fun i=> ↑(F₊ i)) (fun i x=> (η i) x) s (travel_χ Y H V Q Qc j false C U s v z) g (born Y H V Q Qc j C U s)
    (fun i p f=> (congrArg g (travel_acts Y H V Q Qc j false C U s v z i p ((UΩ i) f))).trans ((h i (sail Y H i j 0 true v.val v.property (smill Λ s i z) f)).trans ((sail_rule Y H Q j true u i f v (smill Λ s i z)).trans (h i f).symm)))
omit u U h V Q Qc C in -- may implicit U? command
private lemma splitAll (F' : Type) (f' : Exercise j → F') (p : F' → Prop)
    (w : ∀ i n, p (f' ⟨i,Sum.inl n⟩)) (v : ∀ i (s : Trans j) z,p (f' ⟨i,Sum.inr (s,z)⟩)) (x : ℕ) : p (f' (exercise j x)) := by rcases h : exercise j x with ⟨i,x|⟨x,t⟩⟩; exact w _ _; exact v _ x _
lemma holds (n : ℕ) : ∀ x, g (T n x)=g x := splitAll j U.H.Op (fun x'=>w₀ x') (fun k=>∀ x,g (k x)=g x)
  (fun i j'=> same_tick Y H V Q Qc j C U u i g h (2*j')) (fun i s z=> same_sail Y H V Q Qc j C U u i g h s (2*z)) n
end invariant_coupon

include v
lemma lone (L : LoneVac Y H V Q Qc j false C U) (w q : ℝ) (p : 0 < w) (hq : 0≤ q) (h : q_m χ=J₀ w q x y) : q_m χ=x := by
  obtain ⟨g,e⟩:= coupon Y H V Q Qc j C U u v w q p hq h
  have hg : g ζ₀=1:= (e _ (unity Y H j 0 true 0)).trans (u.one _)
  have hw := still_norm U.H (T) (motion_cost Y H V Q Qc j false C U) ζ₀ (vacuum_norm Y H V Q Qc j false C U) g hg (holds Y H V Q Qc j C U u g e) L
  have he (s : ℕ) (f : F₊ s) : (q_m χ) s (F s f)=x s (F s f):= (actual_expect Y H V Q Qc j false C U s ((UΩ s) f)).symm.trans ((hw _).trans (e s f))
  let o := exact_together Y H Q _ (all_together Y H V Q Qc j false C χ)
  funext s f; obtain ⟨S,pf⟩:= f.property.1.paid; obtain ⟨z,hy⟩:= canStart Y H j s S
  exact (wake_rule Y H Q j true o s f z).symm.trans ((he s (fromCover Y H j true s z f pf hy)).trans (wake_rule Y H Q j true u s f z))

omit v u U
include U
lemma owner (L : LoneVac Y H V Q Qc j false C U) : extremeJoint Y H Q true (q_m χ) := by
  refine ⟨exact_together Y H Q _ (all_together Y H V Q Qc j false C χ), fun x y h t w p hw e=> ⟨(lone Y H V Q Qc j C U h t L w (1-w) p (sub_nonneg.mpr hw.le) e).symm,
    (lone Y H V Q Qc j C U t h L (1-w) w (sub_pos.mpr hw) p.le (e.trans (funext fun i=>funext fun y=>add_comm ..))).symm⟩⟩
end YM.CF.Buffered.Afterglow.Tower.Selection.Single

namespace YM.CF.Buffered.Afterglow.Tower.Selection.Single
#print axioms owner
end YM.CF.Buffered.Afterglow.Tower.Selection.Single
