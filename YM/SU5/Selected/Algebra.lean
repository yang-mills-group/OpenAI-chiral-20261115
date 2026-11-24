import YM.SU5.Selected.GridU
import YM.SU5.Selected.Order

/-! A C⋆ of actual Euclidean slab operators and grid shifts, all positive
shapes, all levels. Products (including compressing onto Aurora **after** product,
a different operation from products of caps). Normal form using arbitrary rung
shifts -- a single grid offset becomes integral notch at some higher rung,
so can always promote a box. In particular all finite words slide over &
land in the concrete cap algebra under compression. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 250000
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
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Set
local notation "U"=>shift Y H V G j strict C
local notation "A₀"=>catalog Y H V G j strict C
open MeshClock
local notation "M"=>timeMesh Λ
local notation "Q"=>advance Y H V G.history.circuit j 0 strict C

/-- Standard order on the concrete catalog. -/
instance orderedCatalog : StarOrderedRing (A₀) := OrderedAux (A₀) (catalog_closed Y H V G j strict C)
where OrderedAux {X:Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] (T: StarSubalgebra ℂ (X →L[ℂ] X)) (p:IsClosed (T : Set (X→L[ℂ]X))) : StarOrderedRing T := by have := p; exact closedStarOrdered T

noncomputable def shifts : Set (A →L[ℂ] A) := {w| ∃ a t,w=U a t}
noncomputable def boxes : Set (A →L[ℂ] A) := {w| ∃ (t u : ℕ) (f : Entry Y H t j strict u) (h:0<u), w=(B t f h)}
local notation "Bx" => boxes Y H V G j strict C
local notation "Uk" => shifts Y H V G j strict C
noncomputable def slabPolynomials := StarAlgebra.adjoin ℂ (boxes Y H V G j strict C ∪ shifts Y H V G j strict C)
local notation "Tx" => slabPolynomials Y H V G j strict C

lemma boxes_activate (t u : ℕ) (f:Entry Y H t j strict u) (h:0<u) : (B t f h) ∈ Bx := ⟨t,u,f,h,rfl⟩
lemma shifts_activate (a:Trans j) (t:marks (timeMesh Λ)) : U a t ∈ Uk := ⟨a,t,rfl⟩
lemma poly_span : (Tx).toSubalgebra.toSubmodule =
    Submodule.span ℂ (Submonoid.closure (Bx ∪ Uk) : Set (A →L[ℂ] A)) := by
  unfold slabPolynomials
  rw [StarAlgebra.adjoin_toSubalgebra, Set.union_eq_left.mpr, Algebra.adjoin_eq_span]
  intro w h
  change star w ∈ Bx ∪ Uk at h
  rw [←star_star w]
  generalize star w = x at *
  rcases h with a|a
  · obtain ⟨t,u,f,p,rfl⟩:=a
    exact Or.inl ⟨t,u,inverse Y H t j strict u f,p,respects Y H V t G.history G.clipped j strict C u f p⟩
  obtain ⟨a,t,rfl⟩:=a
  exact Or.inr ⟨a,-t,shift_star Y H V G j strict C a t⟩

lemma boxes_mul {x y:A →L[ℂ] A}(p:x∈Bx)(q:y∈Bx): x*y∈Bx := by
  have lift(t:A →L[ℂ] A)(p:t∈Bx): ∀ᶠ s in atTop, ∃ (u:ℕ) (f:Entry Y H s j strict u) (h:0<u), t=(B s f h) := by
    obtain ⟨r,u,f,h,rfl⟩ := p
    filter_upwards [eventually_ge_atTop r] with t ht
    exact ⟨_,_,_,refined_box Y H V r G.history G.clipped j strict C u f h t ht⟩
  obtain ⟨s, ⟨u,f,h,rfl⟩,v,g,t,rfl⟩ := ((lift x p).and (lift y q)).exists
  exact ⟨s,u+v,_,_,edit_comp Y H V s G.history G.clipped j strict C u v f g h t⟩

lemma boxes_conjugate {x u:A→L[ℂ] A} (p:x∈Uk) (q:u∈Bx) : ∃ y∈Bx, x*u=y*x := by
  obtain ⟨a,t,rfl⟩:=p
  obtain ⟨s,v,f,e,rfl⟩:=q
  obtain ⟨r,n,rfl⟩:=notch_exists M t
  let k:=max s r; have ht:s ≤ k:=le_max_left ..; have hv:r ≤ k:=le_max_right ..
  rw [←notch_up M r k hv,refined_box Y H V s G.history G.clipped j strict C v f e k ht]
  exact ⟨_, boxes_activate Y H V G j strict C k _ _ _, notch_comp Y H V G j strict C a _ _ _⟩

lemma closure_shift {x u:A→L[ℂ] A} (p:x∈Submonoid.closure (Uk)) (q:u∈Bx) :
    ∃ y∈Bx, x*u=y*x := by
  revert q
  induction p using Submonoid.closure_induction generalizing u with
  | mem _ p=> exact fun q=> boxes_conjugate Y H V G j strict C p q
  | one=> exact fun q=> ⟨u,q,by rw [one_mul,mul_one]⟩
  | mul _ _ _ _ hx hy=>
    intro q; obtain ⟨y,v,e⟩ := hy q; obtain ⟨z,t,h⟩ := hx v
    exact ⟨z,t,by rw [mul_assoc,e,←mul_assoc,h,mul_assoc]⟩

lemma valve {x:A→L[ℂ] A} (p:x∈Submonoid.closure (Bx∪Uk)) : x∈Submonoid.closure (Uk) ∨
    ∃ y∈Bx, ∃ s ∈ Submonoid.closure (Uk), x=y*s := by
  induction p using Submonoid.closure_induction with
  | mem x h => exact h.elim (fun a=> Or.inr ⟨x,a,1,(Submonoid.closure _).one_mem,(mul_one _).symm⟩) (fun a=> Or.inl (Submonoid.subset_closure a))
  | one=> exact Or.inl ((Submonoid.closure _).one_mem)
  | mul x y _ _ p q =>
    rcases p with a|⟨t,m,d,g,rfl⟩
    · rcases q with b|⟨u,b,v,h,rfl⟩
      · exact Or.inl ((Submonoid.closure (Uk)).mul_mem a b)
      obtain ⟨w,q,e⟩:=closure_shift Y H V G j strict C a b
      exact Or.inr ⟨w,q,x*v,(Submonoid.closure (Uk)).mul_mem a h,by rw [←mul_assoc,e,mul_assoc]⟩
    rcases q with b|⟨u,b,v,h,rfl⟩
    · exact Or.inr ⟨t,m,d*y,(Submonoid.closure _).mul_mem g b,mul_assoc ..⟩
    obtain ⟨w,q,e⟩:=closure_shift Y H V G j strict C g b
    exact Or.inr ⟨t*w,boxes_mul Y H V G j strict C m q,d*v,(Submonoid.closure (Uk)).mul_mem g h,
      by rw [←mul_assoc (t*d) u v,mul_assoc t d u,e]; simp [mul_assoc]⟩

-- topology props
private theorem cli_top (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] : IsTopologicalRing (W →L[ℂ] W) := inferInstance
private theorem cli_star (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] : ContinuousStar (W →L[ℂ] W) := inferInstance
-- instance not needed?
--instance : IsTopologicalRing (A →L[ℂ] A) := cli_top (A)
--instance : ContinuousStar (A →L[ℂ] A) := cli_star (A)
noncomputable def stationC := (slabPolynomials Y H V G j strict C).topologicalClosure
local notation "St" => stationC Y H V G j strict C
instance station_closed : IsClosed (St : Set (A →L[ℂ] A)) := isClosed_closure
instance station_order : StarOrderedRing (St) := closedStarOrdered (St)
lemma station_poly : Tx ≤ St := StarSubalgebra.le_topologicalClosure _
lemma station_box {x}(h:x∈Bx) : x∈St := station_poly Y H V G j strict C (StarAlgebra.subset_adjoin ℂ (Bx∪Uk) (Or.inl h))
lemma station_U {x}(h:x∈Uk) : x∈St := station_poly Y H V G j strict C (StarAlgebra.subset_adjoin ℂ (Bx∪Uk) (Or.inr h))
lemma mesh_heat (s u:ℕ) (p:0<u) : Q (whenly M s u)∈Bx :=
  ⟨s,u,_,p,(ticket_birth Y H V s G.history G.clipped j strict C u p).symm⟩
lemma norm_cont_heat (t:ℝ≥0)(p:0<t) : ContinuousAt (Q) t := by
  let ν (x:ℝ≥0) := ((x:ℝ):ℂ)*Complex.I
  have he : 0 < (ν t).im := by simpa [ν] using (show 0 < (t:ℝ) from p)
  refine (((holo Y H V G.history.circuit j 0 strict C _ he).continuousAt).comp
    (show ContinuousAt ν t by unfold ν; fun_prop)).congr ?_
  filter_upwards [lt_mem_nhds p] with x h using agrees_euclid Y H V G.history.circuit j 0 strict C (a:=x) h -- direction?
lemma station_heat (t:ℝ≥0) : Q t∈St := by
  rcases eq_or_ne t 0 with rfl|p
  · rw [advance_source]; exact (St).one_mem
  have h:0<t:= pos_iff_ne_zero.mpr p
  apply (show IsClosed (St : Set _) from station_closed Y H V G j strict C).mem_of_tendsto
    ((norm_cont_heat Y H V G j strict C t h).tendsto.comp (MeshClock.shade M t))
  exact Eventually.of_forall (fun v:ℕ=> station_box Y H V G j strict C (mesh_heat Y H V G j strict C v _ (Nat.succ_pos _)))

/-- compression on the ambient operator norm system. -/
noncomputable def squeeze : (A →L[ℂ] A) →L[ℂ] ((Γ) →L[ℂ] (Γ)) :=
  (ContinuousLinearMap.compL ℂ (Γ) A (Γ) π) ∘L
    ((ContinuousLinearMap.compL ℂ (Γ) A A).flip (ι₀))
local notation "Sq"=>squeeze Y H V G j strict C
lemma squeeze_val (x:A→L[ℂ] A) : Sq x=(π).comp (x.comp (ι₀)) := rfl
lemma squeeze_one : Sq (1:A→L[ℂ]A)=1 := by
  rw [squeeze_val]
  ext1 x
  change π x.val=x
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x
lemma squeeze_box (s u : ℕ) (f : Entry Y H s j strict u) (p:0<u) :
    Sq (B s f p) = (P s) (observableOf Y H j strict s f.val) := (cap_entry Y H V G j strict C s u f p).symm
lemma closes_caps {x} (p:x∈St) : Sq x∈A₀ := by
  let A' := Submonoid.closure (Uk)
  have hi(k)(e:k∈ A'): k.comp ι₀ = ι₀ := by
    induction e using Submonoid.closure_induction with
    | mem x h=> obtain ⟨a,v,rfl⟩:=h; ext1 p; exact shift_ground ..
    | one=> rfl
    | mul x y _ _ a b=> rw [show x*y=x.comp y from rfl, ContinuousLinearMap.comp_assoc,b,a]
  refine closure_minimal (t:=(Sq) ⁻¹' (A₀ : Set _)) ?_ ((catalog_closed Y H V G j strict C).preimage (Sq).continuous) p
  intro z h
  change z ∈ (Tx).toSubalgebra.toSubmodule at h
  rw [poly_span] at h
  change Sq z∈A₀
  induction h using Submodule.span_induction with
  | mem b p=>
    rcases valve Y H V G j strict C p with e|⟨f,⟨s,u,w,rwpos,rfl⟩,t,k,rfl⟩
    · rw [squeeze_val,hi b e]
      exact (show (π).comp (ι₀)=(1: (Γ)→L[ℂ](Γ)) from squeeze_one ..) ▸ (A₀).one_mem -- direction?
    have hh := included Y H V G j strict C (s, observableOf Y H j strict s w.val)
    rw [squeeze_val,show (B s w rwpos)*t=(B s w rwpos).comp t from rfl,ContinuousLinearMap.comp_assoc,hi t k,←squeeze_val,squeeze_box]
    exact hh
  | zero => rw [map_zero]; exact (A₀).zero_mem
  | add _ _ _ _ a b=> rw [map_add]; exact add_mem a b
  | smul _ _ _ a => rw [map_smul]; exact (A₀).smul_mem a _
end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.valve
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.closes_caps
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.station_heat
