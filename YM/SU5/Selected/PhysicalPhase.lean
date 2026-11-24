import YM.SU5.Selected.Overview
/-!
# Physical sub-ensemble of the constructed C⋆ slab system

The physical-only operators at this resolution stage mean the ones supported with the
same requirements AND SU(5)-invariant, together with the same (countable) spatial grid
translations and positive-length heat. This is STILL a crossed operator algebra on
positive-time strips (in the sense described in Region), not a Haag-local or gauge fixing
claim. Why use this? Every physical test in the hierarchy can be read to a suitable
such slab; all widths and any purchases of overlap products at the allowed levels stay
on the same reflected s-forms and gauge system. We can rule out both the extremality /
rank-one calculation on all extensions being due only to inclusion of unphysical colored
questions, and being due to fake geometry in a reduced abstract cap spectrum. It costs nothing
to restrict to this system now. Furthermore, we include the Gram embedding (the next file): the selected
physical space actually arises from the resolution-local gauge invariant test algebra on the
positive half-plane (any axis j at 0 here). Not asserting time-zero algebras or real-time
fields. Dynamics here still from E. Estimates at fixed kernel rows etc are the ones verified
on the *same* history, not changed vacuum UV weights by hand.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open Tapestry.Exhibition Tapestry.Altitude Set
section restrict
variable {A B:Type} [CStarAlgebra A][PartialOrder A][StarOrderedRing A][CStarAlgebra B][PartialOrder B][StarOrderedRing B]
variable (f : A→ₚ[ℂ]ℂ) (g : B→ₚ[ℂ]ℂ) (σ : B →⋆ₐ[ℂ] A) (e : ∀ x, f (σ x)=g x)
local notation "π"=> f.gnsStarAlgHom
local notation "θ"=> g.gnsStarAlgHom
local notation "ζ"=> origin f
local notation "ω"=> origin g
set_option maxHeartbeats 120000 in
lemma gns_pair (x y:A): inner ℂ ((π x) ζ) ((π y) ζ) = f (star x * y):=by
  rw [takes_state,takes_state]; simp [PositiveLinearMap.preGNS_inner_def]
set_option maxHeartbeats 120000
include e
lemma restriction_inner (x y:B): inner ℂ ((θ x) ω) ((θ y) ω) = inner ℂ ((π (σ x)) ζ) ((π (σ y)) ζ):= by
  rw [gns_pair,gns_pair,← map_star,←map_mul,e]
lemma pairing_isometry : ∃ U : g.GNS→ₗᵢ[ℂ] f.GNS, ∀ b : B, U ((θ b) ω)= (π (σ b)) ζ := by
  have ht:=gns_dense g; let b:Hilbert:= { space:=g.GNS }; let p:Hilbert:={space:=f.GNS}; obtain ⟨U,T,h⟩:= send_buds (A:=b) (B:=p) (fun x=> _) (fun x=>_) (ht.mono (Submodule.subset_span)) (restriction_inner f g σ e)
  have he:∀ i:g.GNS, ‖U i‖=‖i‖:=by
    intro i; apply congrFun (_ : (fun v:g.GNS=>‖U v‖)=(fun v=> ‖v‖)) i
    apply ht.equalizer U.continuous.norm continuous_norm; funext v
    simp only [Function.comp_apply]; rw [h]
    nth_rw 1 [@norm_eq_sqrt_re_inner ℂ]; rw [← restriction_inner f g σ e v v, ← @norm_eq_sqrt_re_inner ℂ]
  exact ⟨{ U with norm_map':=he },h⟩
omit e
lemma restrict_space (U : g.GNS →ₗᵢ[ℂ] f.GNS) (hU : ∀ b:B, U ((θ b) ω)=(π (σ b)) ζ) (b:B) : U.toContinuousLinearMap.comp (θ b)= (π (σ b)).comp U.toContinuousLinearMap:=by
  apply DFunLike.coe_injective; apply (gns_dense g).equalizer (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _); funext i
  change U ((θ b * θ i) ω)=(π (σ b)) (U (θ i ω)); rw [← map_mul,hU (b*i),hU i,map_mul σ,map_mul π]; rfl
lemma restrict_one_space (U:g.GNS→ₗᵢ[ℂ] f.GNS)(hU : ∀ b:B, U ((θ b) ω)=(π (σ b)) ζ): U ω=ζ:=by
  have h:=hU 1; rw [map_one,map_one,map_one] at h; exact h

variable (J:B) (p : ‖J‖≤1)
include p e
lemma restrict_residual (x : B) : jointResidual g J x=jointResidual f (σ J) (σ x):=by
  have ht:=grain_limit f (σ J) ((NonUnitalStarAlgHom.norm_apply_le σ J).trans p) (σ x); apply tendsto_nhds_unique (grain_limit g J p x)
  apply ht.congr; intro t; have he:σ (sweep J t)=sweep (σ J) t:=by unfold sweep; rw [map_smul,map_sum]; simp_rw [map_pow]
  unfold grain; rw [← he,← map_mul,← map_star,← map_mul,e]
end restrict
section heat
open ContinuousLinearMap
variable {A B:Hilbert}(T : ℝ≥0→B.Op){j:Axis}(S:OS.Semigroup A j)(U:B→ₗᵢ[ℂ]A)
-- instantiate hU explicitly
lemma continuity_help {X:Type}[TopologicalSpace X] {t:X→B} {q:X→A}(p:Continuous q)(V:∀x,U (t x)= q x) : Continuous t:= U.isometry.isEmbedding.isInducing.continuous_iff.mpr (by rwa [show ⇑U ∘ t=q from funext V])
noncomputable def inheritS (u:∀t,∀ x:B,U (T t x)= S.E t (U x)) : OS.Semigroup B j where
  E:=T
  U _:= ContinuousLinearMap.id ℂ _
  eZero:=ContinuousLinearMap.ext (fun x=>U.injective (by rw [u,S.eZero]; rfl))
  time t s:=ContinuousLinearMap.ext (fun x=>U.injective (by rw [ContinuousLinearMap.comp_apply,u,u,u,S.time]; rfl)) -- fix
  shrinks t:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y=> by rw [← U.norm_map,← U.norm_map y,u]; exact (S.E t).le_of_opNorm_le (S.shrinks t) (U y))
  sym t:=ContinuousLinearMap.ext (fun x=>by
    apply ext_inner_left ℂ; intro y; rw [ContinuousLinearMap.adjoint_inner_right, ← U.inner_map_map,← U.inner_map_map y, u,u,S.swing]) -- S.swing import yes
  uZero:=rfl
  space _ _:=rfl
  independent _ _:=by simp
  unitary _ _:=rfl
  continuousU _:=continuous_const
  continuousE x:= continuity_help U (S.continuousE (U x)) (fun t=>u t x)
lemma fixed_transit (f : B.Op)(g:A.Op)(U : B→ₗᵢ[ℂ] A)(x:B)(p : U (f x)=g (U x)): f x=x ↔ g (U x)=U x:=by
   rw [←U.injective.eq_iff,p]
end heat

namespace Spine
set_option maxHeartbeats 120000
variable (P : Spine)(j : Axis)
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "V"=> P.law
local notation "K"=> P.calibration
local notation "Ω"=> P.par
local notation "π"=> P.history
local notation "Qt"=>P.projection.clipped
local notation "C₀"=> P.room j
local notation "L"=> P.par.R.L.val
local notation "r" t:max=> P.halfShift j t
local notation "u"=> enclave K
local notation "A"=> P.Slabs j
local notation "J"=> P.jointTest j
local notation "S"=> P.Test
local notation "X"=> P.Spectrum0 j
-- Qualification easiest by CovCover (ALL periods). Need not require all B marked with both(Pane original & auxiliary),
-- since advancement can turn the query into the latter kind we include that wide system; single pane interps correspond.
lemma shifts_keep (i:Axis)(c:ℤ){x:S}(e:x∈ enclave K): P.shifts i c x∈ enclave K:=
    chime_cov K i _ ((Tapestry.locates ..).1 (findsBay K x).choose_spec) e
lemma mirror_keeps (i:Axis)(c:ℤ){x:S}(e:x∈ enclave K): aureole K i c x∈ enclave K:=
    covariant_flips K i c ((Tapestry.locates ..).1 (findsBay K x).choose_spec) e
lemma refine_keeps (s:ℕ)(f:S)(p:f∈ enclave K)(n:ℕ): P.conveying s n f∈ enclave K:=by
  obtain ⟨T,h⟩:=findsBay K f; exact (obs_in ..).1 (chroma Y H (π).circuit s n ((obs_in ..).2 ⟨(Tapestry.locates ..).1 h,(show CovCover K _ from p)⟩))|>.2
local notation "δ" s:max f:max=> P.voxTest j s f
-- SubSt.
def admitted : Set (P.Slabs j):={x : A | ∃ (s w:ℕ)(p:0<w) (f:P.Card j s w), x=P.atSide j s w p f∧ P.voxTest j s f.val∈ Tapestry.enclave P.calibration}
local notation "T₀"=> P.admitted j
lemma adverts {s w:ℕ}(p:0<w)(f:P.Card j s w)(e:P.voxTest j s f.val∈u): P.atSide j s w p f ∈ P.admitted j:= ⟨s,w,p,f,rfl,e⟩
lemma acceptsStar {x:A} (p:x∈P.admitted j): star x∈ P.admitted j := by
  obtain ⟨s,w,p,f,rfl,h⟩:=p; rw [P.grainStar]; refine ⟨s,w,p,inverse Y H s j false w f,rfl,?_⟩; have he:δ s (inverse Y H s j false w f).val = aureole K j (gaugeT K (w:ℤ)) (δ s f.val):= rfl; rw [he]; exact P.mirror_keeps j _ h
lemma physical_tab {s w v:ℕ} (p:0<w)(f:P.Card j s w)(e:δ s f.val∈u)(ep:0<v)(g:P.Card j s v)(p':δ s g.val∈u): P.atSide j s w p f* P.atSide j s v ep g∈ P.admitted j:=by
  rw [P.concat]; apply P.adverts
  rw [show P.voxTest j s (edit Y H s j false w v f g).val=δ s f.val * P.shifts j (w:ℤ) (δ s g.val) from Subtype.ext (editor ..)]; exact Subalgebra.mul_mem u e (P.shifts_keep j (w:ℤ) p')
lemma upper_tab (s w : ℕ)(p:0<w)(f:P.Card j s w)(t:ℕ)(h:s≤t): P.atSide j s w p f=P.atSide j t _ (Nat.mul_pos (pow_pos (Ω).R.L.property _) p) (furnished Y H s π j false w f t h):=Subtype.ext (refined_box Y H V s π Qt j false C₀ w f p t h)
lemma convey_vox {s w t:ℕ}(f:P.Card j s w)(h:s≤t): P.conveying s (t-s) (δ s f.val)= P.entryTest j t (furnished Y H s π j false w f t h):=rfl
lemma acceptsMul {x y:A} (p:x∈P.admitted j)(e:y∈P.admitted j): x*y∈P.admitted j:=by
  obtain ⟨s,w,h,f,rfl,hv⟩:=p; obtain ⟨t,v,k,g,rfl,e⟩:= e; let m:=max s t; let hp:=le_max_left s t; let ht:=le_max_right s t
  rw [P.upper_tab j s w h f m hp,P.upper_tab j t v k g m ht]; apply P.physical_tab
  · exact P.refine_keeps _ (δ s f.val) hv _
  exact P.refine_keeps _ (δ t g.val) e _
lemma approved_move (g:Grid j) {x:A} (p:x∈P.admitted j): ∃ y∈ P.admitted j, P.movesOf j g*x=y*P.movesOf j g:=by
  obtain ⟨s,w,h,f,rfl,v⟩:=p; rcases g with ⟨t,i,k⟩; let m:=max s t; let e:=le_max_left s t; let b:=le_max_right s t
  let F:= furnished Y H s π j false w f m e; let t':= L^(m-s)*w; have Vv:0<t':=by exact Nat.mul_pos (pow_pos (Ω).R.L.property _) h
  let i':=castor (timeMesh Ω) t m i; have hu:P.movesOf j (t,i,k)=P.movesOf j (m,i',k):=by
    apply Subtype.ext; change (P.crew j k).play _ = _; rw [← notch_up (timeMesh Ω) t m b i]
  let F':=alongS Y H m j false t' F k i'; refine ⟨P.atSide j m t' Vv F', P.adverts j Vv F' ?_,?_⟩
  · apply show ∀ e:δ m F.val∈u, _ from fun e=> P.shifts_keep k.val i' e; exact P.refine_keeps _ (δ s f.val) v _
  rw [hu,P.upper_tab j s w h f m e]; exact Subtype.ext (shape_across Y H V m π Qt j false C₀ t' F Vv k i')

local notation "G" g:max => P.movesOf j g
local notation "T"=> insert 1 (P.admitted j)
local notation "d" xs:max=> (List.map (P.movesOf j) xs).prod
-- physical monoid only. From previous.
lemma falls_ground (s:ℕ)(k:ℤ)(i:Trans j): star (P.movesOf j (s,k,i))=P.movesOf j (s,-k,i) := Subtype.ext (P.shift_star ..)
lemma falls_toUnit(g:Grid j): P.movesOf j g∈ unitary (P.Slabs j):= ⟨Subtype.ext (P.shift_unitary j g|>.1), Subtype.ext (P.shift_unitary j g|>.2)⟩
lemma together_flight(f : List (Grid j)) (x:A)(p:x∈T): ∃ u' ∈T,(d f)*x=u'*(d f):=by
 induction f with
 | nil=> exact ⟨x,p,by simp⟩
 | cons i xs ih=>
  obtain ⟨y,p,e⟩:= ih; rw [List.map_cons,List.prod_cons,mul_assoc,e]
  rcases mem_insert_iff.mp p with rfl|p; · exact ⟨1,Set.mem_insert .. ,by simp⟩
  obtain ⟨v,p,q⟩:=P.approved_move j i p; exact ⟨v,Set.mem_insert_of_mem _ p,by rw [←mul_assoc,q,mul_assoc]⟩
open scoped Pointwise
def authorized : Set (P.Slabs j):= (insert 1 (P.admitted j))∪ Set.range (P.movesOf j)
def flyingForm : Set (P.Slabs j):= {x|∃ y∈ insert 1 (P.admitted j), ∃ l : List (Grid j), y*(d l)=x}
local notation "U₀"=> P.authorized j
lemma flies_mul {x y:A} (p:x∈T)(q:y∈T): x*y∈ T:=by
 rcases mem_insert_iff.mp p with rfl|p; · rwa [one_mul]
 rcases mem_insert_iff.mp q with rfl|q; · rw [mul_one]; exact Set.mem_insert_of_mem _ p
 exact Set.mem_insert_of_mem _ (P.acceptsMul j p q)
lemma flies {x:A} (p : x∈ Submonoid.closure ((P.authorized j)∪star (P.authorized j))): x∈ P.flyingForm j:=by
  induction p using Submonoid.closure_induction with
  | mem u' t=>
    have hp {a:A}(p:a∈ U₀):star a∈ U₀:=by
      rcases p with (rfl|p)|⟨⟨s,i,k⟩,rfl⟩; · rw [star_one]; exact Or.inl (Set.mem_insert ..)
      · exact Or.inl (Set.mem_insert_of_mem _ (P.acceptsStar j p))
      rw [P.falls_ground]; exact Or.inr ⟨_,rfl⟩
    have he: u'∈ U₀:=t.elim id (fun e=> (star_star u') ▸ hp (Set.mem_star.mp e))
    rcases he with v|⟨g,rfl⟩
    · exact ⟨u',v,[],by simp⟩
    exact ⟨1, Set.mem_insert ..,[g],by simp⟩
  | one=> exact ⟨1,Set.mem_insert ..,[],by simp⟩
  | mul f g _ _ hx hy=> obtain ⟨f,v,s,rfl⟩:=hx; obtain ⟨g,t,q,rfl⟩:=hy; obtain ⟨h,p,w⟩:= P.together_flight j s g t; exact ⟨f*h,P.flies_mul j v p,s++q,by rw [List.map_append,List.prod_append, mul_assoc f (d s),← mul_assoc (d s) g,w]; simp only [mul_assoc]⟩
-- exact algebra no projections added; physics state supports these issued through test X.
def neutralSlabs : StarSubalgebra ℂ (P.Slabs j) := (StarAlgebra.adjoin ℂ (P.authorized j)).topologicalClosure
local notation "S₀"=> P.neutralSlabs j
abbrev Physical : Type:= ↑(P.neutralSlabs j)
instance hereClosed : IsClosed (P.neutralSlabs j : Set A):=isClosed_closure
instance physicalOrdered : StarOrderedRing (P.Physical j):= sub_positive (P.neutralSlabs j)
lemma makesIt {x:A}(p:x∈T): x∈P.neutralSlabs j:= StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ (P.authorized j) (Or.inl p))
lemma mobility (g:Grid j): P.movesOf j g∈P.neutralSlabs j:= StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ (P.authorized j) (Or.inr ⟨_,rfl⟩))
lemma sunshine(s w:ℕ)(p:0<w):P.Eucl j (whenly (timeMesh Ω) s w)∈P.admitted j:=by
  let f:= SlabMark.identity Y H s j false w
  rw [show P.Eucl j _=P.atSide j s w p f from Subtype.ext ((ticket_birth Y H V s π Qt j false C₀ w p).symm)]
  exact P.adverts j p f (show (1:P.Test)∈ u from one_mem _)
lemma warms_admitted (s v:ℕ):P.Eucl j (whenly (timeMesh P.par) s v)∈P.neutralSlabs j:=by
 rcases Nat.eq_zero_or_pos v with rfl|p; · rw [when_zero,P.eucl_zero]; exact one_mem _
 exact P.makesIt j (Set.mem_insert_of_mem _ (P.sunshine j s v p))
lemma days (t:ℝ≥0): P.Eucl j t∈P.neutralSlabs j := by
  rcases eq_zero_or_pos t with rfl|p; · rw [P.eucl_zero]; exact one_mem _
  exact (P.hereClosed j).mem_of_tendsto ((P.eucl_cont j t p).tendsto.comp (shade (timeMesh Ω) t)) (Eventually.of_forall fun n=>P.warms_admitted j n _)
lemma faith0 : P.jointTest j ∈ P.neutralSlabs j:= (P.hereClosed j).mem_of_tendsto (cog_hasSum _ (P.slots_small j)|>.tendsto_sum_nat) (Eventually.of_forall fun _ => Subalgebra.sum_mem (S₀).toSubalgebra (fun i _=> (S₀).smul_mem (show P.shiftsAndTimes j i∈ S₀ from (P.visible j).mpr ⟨P.warms_admitted j,P.mobility j⟩ i) _))
section dynamics
local notation "B"=> P.Physical j
variable (x:P.Spectrum0 j)
abbrev pinJoint : P.Physical j:=⟨P.jointTest j,P.faith0 j⟩
def restrictPortion : P.Physical j→ₚ[ℂ]ℂ := (P.portion j x).comp (PositiveLinearMap.ofClass (P.neutralSlabs j).subtype)
lemma restricts (z:B) : P.restrictPortion j x z=P.portion j x z.val:=rfl
local notation "φ"=> P.portion j x
local notation "Ψ"=> P.restrictPortion j x
local notation "Φ"=> (Ψ).gnsStarAlgHom
local notation "J'"=>P.pinJoint j
lemma pin_paid : ‖P.pinJoint j‖≤1:=P.testing_norm j
lemma unit_too : P.restrictPortion j x 1=1:= P.portion_unit j x
lemma faith_again : P.restrictPortion j x (P.pinJoint j) = 1:=P.portion_joint j x
abbrev ColorHil : Hilbert := {space:= (Ψ).GNS}
local notation "Λ"=> P.ColorHil j x
abbrev colorSpace := (P.restrictPortion j x).gnsStarAlgHom
abbrev colorZero := origin (P.restrictPortion j x)
local notation "ω"=> P.colorZero j x
local notation "ζ"=> P.emptyV j x
def gnsIn : (P.ColorHil j x) →ₗᵢ[ℂ] (P.PortionHil j x):= (pairing_isometry (φ) (Ψ) (P.neutralSlabs j).subtype (fun _=> rfl)).choose
lemma identifies (b:B) : P.gnsIn j x ((Φ b) ω)= (φ).gnsStarAlgHom b.val ζ := (pairing_isometry (φ) (Ψ) (P.neutralSlabs j).subtype (fun _=> rfl)).choose_spec b
lemma present0 : P.gnsIn j x (P.colorZero j x)= P.emptyV j x:= restrict_one_space (φ) (Ψ) (P.neutralSlabs j).subtype _ (P.identifies j x)
lemma restrict_flight (z:P.Physical j) : (P.gnsIn j x).toContinuousLinearMap.comp ((P.restrictPortion j x).gnsStarAlgHom z)= ((P.portion j x).gnsStarAlgHom z.val).comp (P.gnsIn j x).toContinuousLinearMap :=
  restrict_space (φ) (Ψ) (P.neutralSlabs j).subtype _ (fun b=> P.identifies j x b) _
lemma colorResidual (p:P.lodestarHere j x): ∀ y:P.Physical j, jointResidual (P.restrictPortion j x) J' y= ‖P.restrictPortion j x y‖^2 := fun y=>
 (restrict_residual (φ) (Ψ) (P.neutralSlabs j).subtype (fun _=> rfl) J' (P.pin_paid j) y).trans (p y.val)
lemma selected_physical (p:P.lodestarHere j x) : pure0 (P.restrictPortion j x) ∧ rooted (Ψ) J'=Submodule.span ℂ {ω}:=by
  have he: ((Ψ) J').re=1:=by rw [P.faith_again]; rfl
  exact ⟨root_pure _ (P.unit_too j x) J' (P.pin_paid j) he (P.colorResidual j x p), root_rank _ (P.unit_too j x) J' (P.pin_paid j) he (P.colorResidual j x p)⟩

abbrev walksColor (g : Grid j) : P.Physical j:= ⟨P.movesOf j g,P.mobility j g⟩
abbrev risesColor (t:ℝ≥0) : P.Physical j:= ⟨P.Eucl j t,P.days j t⟩
def warming (t:ℝ≥0) : (P.ColorHil j x).Op:= Φ (P.risesColor j t)
lemma warmTransit (t:ℝ≥0) (v:P.ColorHil j x): P.gnsIn j x (P.warming j x t v)= P.innerEucl j x t (P.gnsIn j x v) := DFunLike.congr_fun (P.restrict_flight j x (P.risesColor j t)) v
lemma moveTransit (g:Grid j)(v:P.ColorHil j x): P.gnsIn j x ((Φ) (P.walksColor j g) v)= (φ).gnsStarAlgHom (P.movesOf j g) (P.gnsIn j x v):= DFunLike.congr_fun (P.restrict_flight j x (P.walksColor j g)) v
noncomputable def physicalEnergy : OS.Semigroup (P.ColorHil j x) j := inheritS (P.warming j x) (P.dynamics0 j x) _ (P.warmTransit j x) 
lemma inherits_edge (t : ℝ)(v:P.ColorHil j x) : P.gnsIn j x ((P.physicalEnergy j x).edge t v)=(P.dynamics0 j x).edge t (P.gnsIn j x v):= by
  refine DFunLike.congr_fun (within_energy («G»:=(Λ)) (P.physicalEnergy j x) (P.dynamics0 j x) ((P.gnsIn j x).toContinuousLinearMap) (fun s=>?_) t) v
  exact ContinuousLinearMap.ext (fun v=> P.warmTransit j x s v)
local notation "U"=> P.gnsIn j x
lemma actual_color (y: P.ColorHil j x) : y∈rooted (P.restrictPortion j x) J' ↔
    (∀ t:ℝ,(P.physicalEnergy j x).edge t y=y)∧∀ g,(P.colorSpace j x) (P.walksColor j g) y=y:=by
  have h : y∈rooted (Ψ) J' ↔ (U y)∈rooted (φ) J := fixed_transit («B»:=Λ) («A»:=P.PortionHil j x) (Φ J') ((φ).gnsStarAlgHom J) (U) y (DFunLike.congr_fun (P.restrict_flight j x J') y)
  apply Iff.trans h ((P.vacuum_full j x (U y)).trans ?_)
  apply and_congr (forall_congr' fun t=> (fixed_transit _ _ U y (P.inherits_edge j x t y)).symm) (forall_congr' fun g=> (fixed_transit _ _ U y (P.moveTransit j x g y)).symm)
end dynamics
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.pairing_isometry
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.restrict_space
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.inheritS
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.acceptsStar
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.flies
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.faith0
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.identifies
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.selected_physical
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.present0
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.physicalEnergy
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.inherits_edge
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.actual_color
