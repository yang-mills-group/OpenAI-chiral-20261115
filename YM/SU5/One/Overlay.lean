import YM.SU5.One.Refraction

/-!
# Locate and present any of the whole selected OS spaces on the physical polynomial system

In particular reconcile the two (worker) GNS constructions -- not by selecting
anything but by uniqueness on the indicated dense spans. Real time included.
Does not yet reconcile time *directions* except in the limited sense of common
input (see following modules).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 340000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.One
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification Tapestry PhaseChoice Altitude
open Selected CF.Pannier.Chancel Set

-- Gram uniqueness. See `PhaseChoice/Equate.lean identify` for this method.
lemma compatible {W U:Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    {X:Type} (f:X→W) (g:X→U) (hf:DenseRange f) (hg:DenseRange g)
    (he:∀ i j, inner ℂ (f i) (f j)=inner ℂ (g i) (g j)) :
    ∃ A : W≃ₗᵢ[ℂ]U, ∀i, A (f i)=g i := by
  let K' (i j:X):= inner ℂ (f i) (f j)
  let gram₁ : _root_.YM.Kernel.Gram K' :=
    { H:={ space:= W }, plant :=f, dense:= Dense.mono Submodule.subset_span hf, measure:= fun _ _=> rfl }
  let Z := Finsupp.linearCombination ℂ g
  have h(v w : X→₀ℂ): inner ℂ (Z v) (Z w)=inner ℂ (gram₁.stems v) (gram₁.stems w) := by
    induction v using Finsupp.induction_linear with
    | zero=>rw [map_zero,map_zero,inner_zero_left,inner_zero_left]
    | add u v a b=>rw [map_add,map_add,inner_add_left,inner_add_left,a,b]
    | single x c=>
      induction w using Finsupp.induction_linear with
      | zero=>rw [map_zero,map_zero,inner_zero_right,inner_zero_right]
      | add u v a b=>rw [map_add,map_add,inner_add_right,inner_add_right,a,b]
      | single y d=>
        change inner ℂ (Z _) (Z _) = inner ℂ (Finsupp.linearCombination ℂ f (Finsupp.single x c))
          (Finsupp.linearCombination ℂ f (Finsupp.single y d))
        simp [Z,he]
  obtain ⟨M,m,a⟩ := gram₁.by_bound g 1 zero_le_one (show ∀ i, ‖Z i‖≤1*‖gram₁.stems i‖ from
    fun i => by rw [one_mul,norm_eq_sqrt_re_inner (𝕜:=ℂ), h, ←norm_eq_sqrt_re_inner])
  let M' : W →L[ℂ] U := M
  have h': ∀ i, M' (f i)=g i := a
  let A : W →ₗᵢ[ℂ] U := {
    M'.toLinearMap with norm_map' x := congrFun (hf.equalizer M'.continuous.norm continuous_norm
      (show (fun y => ‖M' y‖) ∘ f=(norm ∘ f) from funext fun i=>by
        change ‖M' (f i)‖=‖f i‖; rw [h',norm_eq_sqrt_re_inner (𝕜:=ℂ), ←he,←norm_eq_sqrt_re_inner] )) x }
  have H : IsClosed (Set.range A) := A.isometry.isClosedEmbedding.isClosed_range
  have x : Surjective A := fun y=> closure_minimal (t:=Set.range A) (fun _ h=> by
    obtain ⟨i,rfl⟩:= h
    exact ⟨f i,h' i⟩) H (hg y)
  exact ⟨LinearIsometryEquiv.ofSurjective A x, fun i=>by rw [LinearIsometryEquiv.coe_ofSurjective]; exact h' i⟩


variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K"=> tent Y H
variable {i k:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ} {E:ℕ→Family (tent Y H)→ℂ} (V: Universal Y H i k I E)
    (G: GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (d : Axis) (S : ∀ j:Axis,Arena Y H G.history.circuit j 0 false)
local notation "𝔄" j:max=> displayAlgebra Y H V G.history G.clipped j false (S j)
variable (c : displayAlgebra Y H V G.history G.clipped d false (S d) →⋆ₐ[ℂ] ℂ) (j:Axis)
local notation "C"=> SameCharacter.resident Y H V G d false (S d) c
local notation "r" a:max=> displacement Y H V G.history G.clipped d false (S d) c a (S a)
local notation "M"=> evaluate Y H V G d S C
local notation "Δ"=> engaged Y H V G j false (S j) d (S d) C
local notation "γ" s:max=> Acting.voice Y H V G j false (S j) Δ s
local notation "κ" s:max=> bud Y H V s G.history G.clipped j false (S j) (r j)
local notation "℥" => indoor Y H V G.history G.clipped j false (S j) (r j)

noncomputable def batch : (Σ s, Tower.Field Y H s j 0 false) → (Δ).space := -- parentheses
  fun x => (γ x.1) x.2
noncomputable def inkling : (Σ s, Tower.Field Y H s j 0 false) → ℥ :=
  fun x=> (κ x.1) x.2

local notation "B"=> batch Y H V G d S c j
local notation "J"=> inkling Y H V G d S c j

lemma acknowledged : DenseRange (batch Y H V G d S c j) := by
  apply (Acting.densely Y H V G j false (S j) Δ).mono
  intro x h; obtain ⟨s,t⟩:= mem_iUnion.mp h; obtain ⟨y,z⟩:=t; exact ⟨⟨s,y⟩,z⟩
lemma inkling_dense : DenseRange (inkling Y H V G d S c j) := by
  apply (stroll_dense Y H V G.history G.clipped j false (S j) (r j)).mono
  intro x h; obtain ⟨s,t⟩:= mem_iUnion.mp h; obtain ⟨y,z⟩:=t; exact ⟨⟨s,y⟩,z⟩

lemma sync_gram (x y : Σ s,Tower.Field Y H s j 0 false) : inner ℂ (B x) (B y)=inner ℂ (J x) (J y) := by
  obtain ⟨s,x⟩:=x; obtain ⟨t,y⟩:=y; let u:=max s t; have hu:s ≤ u:=le_max_left ..; have ht:t ≤ u:=le_max_right ..
  let f:= Raise Y H G.history.circuit j 0 false s u hu x; let g:= Raise Y H G.history.circuit j 0 false t u ht y
  have hx: (γ u) f=B ⟨s,x⟩ := Acting.climbs Y H V G j false (S j) Δ s x u hu
  have hy: (γ u) g=B ⟨t,y⟩ := Acting.climbs Y H V G j false (S j) Δ t y u ht
  have hv: (κ u) f=J ⟨s,x⟩ := flourishes ..
  have hk: (κ u) g=J ⟨t,y⟩ := flourishes ..
  rw [←hx,←hy,←hv,←hk,←voice_at,earns,spinLoan Y H V G d S c j]
  rfl

private lemma obtain_both : ∃ e : ((Δ).space) ≃ₗᵢ[ℂ] (℥), ∀ x, e (B x)=J x:= by
  exact compatible B J (acknowledged Y H V G d S c j) (inkling_dense Y H V G d S c j) (sync_gram Y H V G d S c j)

/-- Canonical identification for this character. -/
def sameSpace : ((Δ).space) ≃ₗᵢ[ℂ] ℥:= (obtain_both Y H V G d S c j).choose
local notation "Z"=>sameSpace Y H V G d S c j
lemma sameSpace_points (s : ℕ) (x: Tower.Field Y H s j 0 false) :
    Z ((γ s) x)=(κ s) x:= (obtain_both Y H V G d S c j).choose_spec ⟨s,x⟩
lemma sameSpace_origin : Z (Δ).ground = doorstep Y H V G.history G.clipped j false (S j) (r j) :=
  (congrArg Z (Acting.unison Y H V G j false (S j) Δ 0).symm).trans
    ((sameSpace_points Y H V G d S c j 0 (unity Y H j 0 false 0)).trans (Selected.root ..))

open MeshClock
local notation "σ"=> timeMesh Λ
local notation "Ω"=> doorstep Y H V G.history G.clipped j false (S j) (r j)
local notation "Ψ"=> procession Y H V G.history G.clipped j false (S j) (r j)
local notation "X" i:max a:max=> (Ψ (shiftStamp Y H V G.history G.clipped j false (S j) i a))
local notation "λ₀"=> Acting.lattice Y H V G j false (S j) Δ

private lemma suffices_field {m:ℕ} (u v : (Δ).space → ℥) (hx:Continuous u)(hy:Continuous v)
    (p:∀ s≥m,∀ x: Tower.Field Y H s j 0 false, u ((γ s) x)=v ((γ s) x)): u=v:= by
  apply (acknowledged Y H V G d S c j).equalizer hx hy
  funext ⟨s,x⟩; change u ((γ s) x)=v ((γ s) x)
  have hu:s ≤ max s m:=le_max_left ..
  rw [←Acting.climbs Y H V G j false (S j) Δ s x (max s m) hu]; apply p _ (le_max_right ..)

lemma sameSpace_space (a:Trans j) (t:marks σ)(x:(Δ).space):
    Z (λ₀ a t x)=(X a t) (Z x):= by
  obtain ⟨s,i,rfl⟩:= (notch_exists σ t)
  let w:= notch σ s i
  suffices h : ∀ x, Z (λ₀ a w x)=(X a w) (Z x) from h x
  refine congrFun (suffices_field Y H V G d S c j (m:=s) _ _ ((Z).continuous.comp (λ₀ a w).continuous) ((X a w).continuous.comp (Z).continuous) (fun t q y=>?_))
  unfold w; rw [← notch_up σ s t q,
    Acting.space_voice,sameSpace_points,sameSpace_points, Selected.turns_across]

local notation "G₀"=> ride Y H V G.history G.clipped j false (S j) (r j)
local notation "T"=> Acting.clock Y H V G j false (S j) Δ
local notation "F" w:max=> (G₀).F (-Complex.I*w)
local notation "P" w:max=> Acting.halfSpaceFunction Y H V G j false (S j) Δ w
local notation "W" t:max=>Acting.unitaryTime Y H V G j false (S j) Δ t
lemma sameSpace_steam (x:(Δ).space) (t:ℝ≥0):
    Z (T t x)=(G₀).E t (Z x):=by
  let u (t:ℝ≥0):= Z (T t x); let v (t:ℝ≥0):=(G₀).E t (Z x)
  have hp:=Acting.price_every Y H V G j false (S j) Δ x; have hV:= (G₀).continuousE (Z x)
  apply congrFun (show u=v from ?_) t
  apply (fills (timeMesh Λ)).denseRange_val.equalizer ((Z).continuous.comp hp) hV
  funext y
  obtain ⟨s,b,h⟩:= MeshClock.split σ y.property
  change u y.val=v y.val; rw [←h]; let d':=whenly σ s b
  apply congrFun (suffices_field Y H V G d S c j (m:=s) _ _ ((Z).continuous.comp (T d').continuous) (((G₀).E d').continuous.comp (Z).continuous) ?_) x
  intro w p' z; change Z (T (whenly σ s b) ((γ w) z))= (G₀).E (whenly σ s b) (Z ((γ w) z))
  rw [←matchR σ s w b p', Acting.clock_voice,sameSpace_points,sameSpace_points, ride_ticks]

open Complex OS.Semigroup
local notation "H₀"=> {z:ℂ| 0<z.im}
private lemma join_hol {A₀ : Type} [NormedAddCommGroup A₀] [NormedSpace ℂ A₀]
    (f g : ℂ→ A₀)(p : AnalyticOnNhd ℂ f {z:ℂ| 0<z.im})(q:AnalyticOnNhd ℂ g {z:ℂ| 0<z.im})
    (h:∀ b:ℝ≥0,0<b→f ((b:ℝ)*Complex.I)=g ((b:ℝ)*Complex.I)): EqOn f g {z:ℂ| 0<z.im}:= by
  let w(x:ℝ≥0):=(x:ℝ)*Complex.I
  -- adapt Edges
  refine p.eqOn_of_preconnected_of_frequently_eq q (convex_halfSpace_gt imCLM.toLinearMap.isLinear 0|>.isPreconnected) (z₀:=w 1) (show 0<(w 1).im from by simp [w]) (fun hn=>?_)
  have ht:Tendsto w (𝓝[>] (1:ℝ≥0)) (𝓝[≠] w 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (show Continuous w from (continuous_ofReal.comp continuous_subtype_val).mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with i hi; change ¬w i= w 1; intro h; apply (mem_Ioi.mp hi).ne'; exact Subtype.ext (Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero h))
  obtain ⟨i,u,v⟩ := ((ht.eventually hn).and self_mem_nhdsWithin).exists
  exact u (h i (zero_lt_one.trans (mem_Ioi.mp v)))

lemma sameSpace_hol (v:(Δ).space)(z:ℂ)(q:0<z.im): Z ((P z) v)= (F z) (Z v):= by
  refine join_hol (fun z=>Z ((P z) v)) (fun z=>(F z) (Z v)) ?_ ?_ ?_ (show z∈ _ from q)
  · intro x hx
    let A: ((Δ).space).Op →L[ℂ] (((Δ).space).space):= ContinuousLinearMap.apply ℂ _ v
    let B':= (Z).toContinuousLinearEquiv.toContinuousLinearMap.comp A
    exact (B'.analyticAt _).comp (f:=Acting.halfSpaceFunction Y H V G j false (S j) Δ) (Acting.linker_analytic Y H V G j false (S j) Δ x hx)
  · intro x hx
    let A: (℥).Op→L[ℂ] (℥).space:= ContinuousLinearMap.apply ℂ _ (Z v)
    exact (A.analyticAt _).comp (f:=fun z=> F z) (ride_anal Y H V G.history G.clipped j false (S j) (r j) x hx)
  intro x hx; rw [Acting.linker_at Y H V G j false (S j) Δ hx,show -Complex.I * ((x:ℝ)*Complex.I) = duration x from by simp [duration,mul_comm _ Complex.I,←mul_assoc], (G₀).roots_heat hx,sameSpace_steam]

-- unique real-time boundary for that direction.
lemma sameSpace_wind (v:(Δ).space)(t:ℝ): Z ((W t) v)=(G₀).edge t (Z v):= by
  let u(x:ℝ≥0):= (t:ℂ)+(x:ℝ)*Complex.I
  have hp : Tendsto (fun x:ℝ≥0=> (F (u x)) (Z v)) (𝓝[>] 0) (𝓝 ((G₀).edge t (Z v))) := by
    apply (ride_continue Y H V G.history G.clipped j false (S j) (r j) _ t).congr'
    filter_upwards [self_mem_nhdsWithin] with y h
    unfold u; rw [selected_air Y H V G.history G.clipped j false (S j) (r j) (show 0< (u y).im from (by simpa [u] using (mem_Ioi.mp h)))]
  apply tendsto_nhds_unique _ hp
  have hx : Tendsto (fun u:ℝ≥0=> T u v) (𝓝[>] 0) (𝓝 v):=by
     have a:= (Acting.price_every Y H V G j false (S j) Δ v).continuousAt (x:=0); rw [ContinuousAt, Acting.clock_zero] at a; exact a.mono_left nhdsWithin_le_nhds
  apply ((show Continuous (fun w:(Δ).space=> Z ((W t) w)) from (Z).continuous.comp (W t).continuous).continuousAt.tendsto.comp hx).congr'
  filter_upwards [self_mem_nhdsWithin] with i p
  rw [←sameSpace_hol Y H V G d S c j v (u i) (by simpa [u] using mem_Ioi.mp p)]
  unfold u; rw [Acting.linked Y H V G j false (S j) Δ (mem_Ioi.mp p)]; rfl

lemma sameSpace_slab {w:ℕ}(s:ℕ)(x:Entry Y H s j false w)(p:0<w)(z:(Δ).space):
    Z ((Acting.watches Y H V G j false (S j) Δ s _ x p) z)= (Ψ (entrance Y H V s G.history G.clipped j false (S j) x p)) (Z z):= by
  let u:= Acting.watches Y H V G j false (S j) Δ s _ x p; let v:= Ψ (entrance Y H V s G.history G.clipped j false (S j) x p)
  apply congrFun (suffices_field Y H V G d S c j (m:=s) _ _ ((Z).continuous.comp u.continuous) (v.continuous.comp (Z).continuous) ?_) z
  intro i g y
  change Z (u ((γ i) y))=v (Z ((γ i) y))
  unfold u v
  rw [Acting.same_box Y H V G j false (S j) Δ i g x p, Acting.act_voice,sameSpace_points,sameSpace_points,slot_high Y H V s G.history G.clipped j false (S j) (r j) x p i g y]

end YM.CF.Buffered.Afterglow.Tower.One
