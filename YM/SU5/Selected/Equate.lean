import YM.SU5.Selected.PinEven

/-! Interpret all-axis moments on one common spectrum. Genuine unitary match
of Aurora spaces here; not an intertwiner between reconstructed Minkowski
Hilbert spaces, or proof of rotation symmetry. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "Ak"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "Bx" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set
local notation "cD" => disc Y H V G j strict C

section join
variable (d : Axis) (C' : Arena Y H G.history.circuit d 0 strict)
local notation "cD'"=>disc Y H V G d strict C'
local notation "Ω'"=>seat0 Y H V G.history d strict C'
local notation "Γ'"=>Aurora Y H V G.history d strict C'

/-- Remove the need to assume rooms are identical when using the moment theorem. -/
lemma exchange_room {S:Type*} [Fintype S] (f : S→Beacon K strict) {l' : List S}
    (p : l'.Nodup) :
    heavies Y H V G.history G.clipped j strict C f l'=
    heavies Y H V G.history G.clipped d strict C' f l' := by
  rcases eq_or_ne j d with a|h
  · subst d
    obtain ⟨u,a⟩ := exists_ne j
    let B : Arena Y H G.history.circuit u 0 strict := Classical.choice (voyage_H Y H V G.history.circuit u 0 strict)
    exact (between_axes Y H V G.history G.clipped j strict C f u B a.symm _ _ p (.refl _)).trans
      (between_axes Y H V G.history G.clipped j strict C' f u B a.symm _ _ p (.refl _)).symm
  exact between_axes Y H V G.history G.clipped j strict C f d C' h _ _ p (.refl _)

lemma matchedGram (f g : Beacon K strict) :
    inner ℂ (cD f Ω) (cD g Ω) = inner ℂ (cD' f Ω') (cD' g Ω') := by
  have h := exchange_room Y H V G j strict C d C' ![(f.1,dual Y H j strict f.2),g] (l' := [0,1]) (by decide)
  rw [←ContinuousLinearMap.adjoint_inner_right (cD f),←ContinuousLinearMap.adjoint_inner_right (cD' f)]
  -- be precise to avoid wrong occurrence?
  change inner ℂ Ω ((cD f).adjoint _) = inner ℂ Ω' ((cD' f).adjoint _)
  unfold disc
  rw [mirror_cap,mirror_cap, ←oppositeStar Y H V G d strict C' j C]
  exact h

private lemma identify {W U:Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
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

noncomputable def connector : (Γ)≃ₗᵢ[ℂ](Γ') := (identify _ _ (cyclic Y H V G j strict C)
  (cyclic Y H V G d strict C') (matchedGram Y H V G j strict C d C')).choose
local notation "𝒰"=>connector Y H V G j strict C d C'
lemma connector_disc (x:Beacon K strict) : 𝒰 (cD x Ω)=cD' x Ω' :=
  (identify _ _ (cyclic Y H V G j strict C)
    (cyclic Y H V G d strict C') (matchedGram Y H V G j strict C d C')).choose_spec x
lemma connector_omega : 𝒰 Ω=Ω' := by
  let f := observableOf Y H j strict 0 (unity Y H j 0 strict 0)
  have h := connector_disc Y H V G j strict C d C' (0,f)
  change 𝒰 (((P 0) f) Ω)= (cap Y H V 0 G.history G.clipped d strict C' f) Ω' at h
  rw [cap_unit Y H V G j strict C 0 f rfl,cap_unit Y H V G d strict C' 0 f rfl] at h
  exact h

lemma intertwines (t:Beacon K strict) : (𝒰).conjStarAlgEquiv (cD t)=cD' t := by
  apply DFunLike.coe_injective
  apply (cyclic Y H V G d strict C').equalizer ((𝒰).conjStarAlgEquiv (cD t)).continuous (cD' t).continuous
  funext x
  apply (cyclic Y H V G d strict C').eq_of_inner_right ℂ
  intro y
  change inner ℂ (cD' y Ω') (𝒰 (cD t ((𝒰).symm (cD' x Ω'))))= _
  conv_lhs => rw [←connector_disc Y H V G j strict C d C' x,←connector_disc Y H V G j strict C d C' y,
    LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]
  change inner ℂ (cD y Ω) (cD t (cD x Ω)) = inner ℂ (cD' y Ω') (cD' t (cD' x Ω'))
  have h := exchange_room Y H V G j strict C d C' ![(y.1,dual Y H j strict y.2),t,x] (l':=[0,1,2]) (by decide)
  rw [←ContinuousLinearMap.adjoint_inner_right (cD y),←ContinuousLinearMap.adjoint_inner_right (cD' y)]
  unfold disc
  rw [mirror_cap,mirror_cap, ←oppositeStar Y H V G d strict C' j C]
  exact h

local notation "A₀"=>catalog Y H V G j strict C
local notation "A'"=>catalog Y H V G d strict C'
private theorem beyond {T:(Γ)≃ₗᵢ[ℂ](Γ')} (ht:∀ x, T.conjStarAlgEquiv (cD x)=cD' x) :
    A₀ ≤ StarSubalgebra.comap T.conjStarAlgEquiv.toStarAlgHom (A') := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro y ⟨x,rfl⟩
    change T.conjStarAlgEquiv (cD x)∈A'
    rw [ht]
    exact included Y H V G d strict C' x
  exact (catalog_closed Y H V G d strict C').preimage (show Continuous T.conjStarAlgEquiv from move_cont T)
where move_cont {W U: Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (v : W≃ₗᵢ[ℂ]U) : Continuous v.conjStarAlgEquiv := (StarAlgEquiv.isometry v.conjStarAlgEquiv).continuous

/-- All-axis identification of phase algebras, * equiv (not changing Q history!). -/
theorem catalogEquiv : ∃ e:(A₀)≃⋆ₐ[ℂ](A'), ∀ x,(e x).val=(𝒰).conjStarAlgEquiv x.val := by
  let f:= (𝒰).conjStarAlgEquiv
  have h : ∀ x, f (cD x)=cD' x:= intertwines Y H V G j strict C d C'
  let L:=f.toStarAlgHom.comp (A₀).subtype
  let B:= L.codRestrict (A') (fun x=> beyond Y H V G j strict C d C' h x.property)
  have p : Injective B := fun i j e=> Subtype.ext (f.injective (show f i.val=f j.val from congrArg Subtype.val e))
  have he(x): f.symm (cD' x)=cD x:=by rw [←h,f.symm_apply_apply]
  have ht : Surjective B := fun x=> ⟨⟨_,beyond Y H V G d strict C' j C (T:=(𝒰).symm) he x.property⟩,
    Subtype.ext (f.apply_symm_apply x.val)⟩
  exact ⟨StarAlgEquiv.ofBijective B ⟨p,ht⟩,fun x=>by rw [StarAlgEquiv.ofBijective_apply]; rfl⟩
end join
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.intertwines
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.catalogEquiv
