import YM.SU5.FiniteGaugeData.Hierarchy.Zone
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Mixed hierarchy -- test prescriptions

A test is a polynomial in the streams of *physical* levelwise insertions. A
stream specifies finitely many observing levels, and at each an element of
that resolution's algebra W. Although W is a commutative (even Fock)
Euclidean algebra, the prescription kept when composing different levels will
be to insert as on our actual (further thinned, same Course) levels, using
Palm propagation from coarse to fine, not matter insertion as if the finite
Fock state at one resolution were that on a different one, nor by ordinary
star. This is a genuine algebra of recipes with a gauge-invariant reading,
including on mixed products; don't claim a presentation without redundancy,
or that these data are sufficient for T→continuum RECONSTRUCTION.

No multiplication claiming that averaging through the step is a deterministic
*-homomorphism. E.g. it is perfectly possible here even to insert an element
at one resolution AND another stencil at the next resolution on exactly the
same region in a prescription. The limiting reading of this recipe
will be identified with the physical limit with that order. Only
separated multiplicativity is purchased for transport. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Playlist
open Charm
section alg
variable (K:Calibration)
def octaves : Submonoid (ℕ→ W K) where
  carrier := {v | ∃ s:ℕ,∀ i≥ s,v i=1}
  mul_mem' := by rintro x y ⟨s,t⟩ ⟨z,k⟩; exact ⟨max s z,fun i e=> by simp only [Pi.mul_apply,t i ((le_max_left ..).trans e),k i ((le_max_right ..).trans e),mul_one]⟩
  one_mem' := ⟨0,fun _ _=>rfl⟩
abbrev Motif := ↥(octaves K)
lemma octave_price (u:Motif K): ∃ s:ℕ,∀ i≥s, u.val i=1:=u.property
-- instance CommMonoid to automatically lift
instance : CommMonoid (Motif K) := { (inferInstance : Monoid ↥(octaves K)) with mul_comm a b:= Subtype.ext (funext fun i=> commW K (a.val i) (b.val i)) }
@[simp] lemma steps_mult (x y:Motif K)(i:ℕ): (x*y).val i=x.val i * y.val i:= rfl
@[simp] lemma steps_unit (i:ℕ): (1:Motif K).val i=1:= rfl
abbrev Region (m:Motif K)(S:ℕ→ Finset Cover):Prop:= ∀ i:ℕ,Locator K (m.val i) (S i)
abbrev Ends (m:Motif K)(s:ℕ):Prop:=∀  i:ℕ, s < i → m.val i=1

def localChord (S:ℕ→Finset Cover) : Submonoid (Motif K) where
 carrier:={v| Region K v S}
 mul_mem' a b := fun i=> locate_join K (S i) (a (show ℕ from i)) (b _)
 one_mem':= fun _=> locate_one K _

def indoor (a:Axis)(t:ℕ→ℤ)(r:ℕ→ℕ) : Submonoid (Motif K) where
 carrier:={m| ∀ i:ℕ,∃ S:Finset Cover,Ahead a (t i) (r i) S∧ Locator K (m.val i) S}
 mul_mem' {x y} p q:= fun i=> by
   obtain ⟨S,h,a⟩:= p i; obtain ⟨T,g,z⟩:=q i
   exact ⟨S∪T, ahead_union S T _ _ h g, locate_join K (S∪T) (locate_sub K a subset_union_left) (locate_sub K z subset_union_right)⟩
 one_mem':= fun _=>⟨∅,fun _ v=>False.elim (Finset.notMem_empty _ v),locate_one K ∅⟩

def opus (a:Axis)(t:ℕ→ℤ)(m:Motif K): Motif K :=
 ⟨fun i=> fire K a (t i) (m.val i),(octave_price K m).elim fun i p=>⟨i,fun n h=> by dsimp only; rw [p n h, ice_central]⟩⟩
def mirrorH (a:Axis)(t:ℕ→ ℤ) : Motif K→*Motif K where
 toFun:= opus K a t
 map_mul' x y:= Subtype.ext (funext fun i=> ice_join K a (t i) (x.val i) (y.val i))
 map_one':= Subtype.ext (funext fun i=> ice_central K a (t i))
lemma opus_idem (a:Axis)(t:ℕ→ℤ)(x:Motif K):opus K a t (opus K a t x)=x:= Subtype.ext (funext fun i=>burning_ice K a (t i) (x.val i))
lemma region_exists (x: Motif K): ∃ S,Region K x S:= ⟨fun i=>(testimony K (x.val i)).choose,fun i=>(testimony K (x.val i)).choose_spec⟩
-- stages, one-time price freely enlarged
lemma ends_exists (x:Motif K):∃ s, Ends K x s:= ⟨(octave_price K x).choose,fun i h=> (octave_price K x).choose_spec i h.le⟩
lemma ends_cold (a:Axis)(t:ℕ→ℤ)(x:Motif K){s:ℕ}(p:Ends K x s): Ends K (opus K a t x) s:= fun i h=> (congrArg (fire K a (t i)) (p _ h)).trans (ice_central ..)
lemma ends_mul {x y:Motif K}{s:ℕ}(a:Ends K x s)(b:Ends K y s): Ends K (x*y) s:= fun i h=> by rw [steps_mult,a i h,b i h,mul_one]

namespace Show
abbrev Theater := MonoidAlgebra ℂ (Motif K)
-- A basis of streams. For local products naturally test on common horizon, dummies disappear. Use support in this basis; may cost larger than another representation.
abbrev flow (v: Motif K): Theater K:= MonoidAlgebra.single v 1
lemma singleC (v: Motif K)(z:ℂ): z • flow K v=MonoidAlgebra.single v z:= by rw [flow,MonoidAlgebra.smul_single',mul_one]
lemma flowOne : flow K 1=1 := rfl
lemma flowProd (x y:Motif K):flow K (x*y)= flow K x*flow K y:=by simp [flow,MonoidAlgebra.single_mul_single]

def intermezzo (a:Axis)(t:ℕ→ℤ) : Theater K→+* Theater K:=
 (MonoidAlgebra.mapDomainRingHom ℂ (mirrorH K a t)).comp (MonoidAlgebra.mapRingHom _ (starRingEnd ℂ))
lemma moment_one (a:Axis)(t:ℕ→ℤ)(x:Motif K)(z:ℂ): intermezzo K a t (MonoidAlgebra.single x z)=MonoidAlgebra.single (opus K a t x) (star z):=by rw [intermezzo,RingHom.comp_apply, MonoidAlgebra.mapRingHom_single]; exact MonoidAlgebra.mapDomain_single

-- canonical summing; use this wherever the state is read on Whole recipes. Includes check of reflection.
def fill {V:Type*}[AddCommMonoid V][Module ℂ V](f:Motif K→V): Theater K →ₗ[ℂ] V:= (Finsupp.linearCombination ℂ f).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
lemma fill_mode {V:Type*}[AddCommMonoid V][Module ℂ V](f:Motif K→V)(x:Motif K) (z:ℂ) : fill K f (MonoidAlgebra.single x z) = z • f x:=by
  change Finsupp.linearCombination ℂ f (Finsupp.single x z)=_; simp
lemma fills {V:Type*}[AddCommMonoid V][Module ℂ V](f:Motif K→V)(x:Theater K): fill K f x=∑ v∈ x.coeff.support,x.coeff v • f v:=rfl
lemma pick_all (x:Theater K):∑ i∈x.coeff.support, MonoidAlgebra.single i (x.coeff i)=x:= by
  apply MonoidAlgebra.coeff_injective; simp_rw [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single]; exact Finsupp.sum_single ..
lemma inter_twice (a:Axis)(t:ℕ→ℤ) (x:Theater K): intermezzo K a t (intermezzo K a t x)=x:=by
  let y:= intermezzo K a t; conv_lhs=> rw [← pick_all K x]
  simp_rw [map_sum,moment_one, opus_idem,star_star]; exact pick_all K x
lemma inter_scale (a:Axis)(t:ℕ→ℤ)(x:Theater K)(z:ℂ): intermezzo K a t (z • x)=star z • intermezzo K a t x:= by
  nth_rw 1 2 [← pick_all K x]; simp_rw [Finset.smul_sum,map_sum,MonoidAlgebra.smul_single',moment_one,Finset.smul_sum, star_mul,MonoidAlgebra.smul_single', mul_comm (star z)] -- order

def active (P:Submonoid (Motif K)) : Subalgebra ℂ (Theater K) where
 carrier:= (MonoidAlgebra.supported ℂ ℂ (P:Set (Motif K)):Set _)
 add_mem' := Submodule.add_mem _
 mul_mem' {x y} (h: (x:Theater K)∈MonoidAlgebra.supported ℂ ℂ _) (b: (y:Theater K)∈ MonoidAlgebra.supported ℂ ℂ _) := by
   change _∈ MonoidAlgebra.supported ℂ ℂ (P:Set (Motif K))
   rw [← pick_all K x,← pick_all K y]; simp_rw [sum_mul,mul_sum]
   refine Submodule.sum_mem _ (fun i p=> Submodule.sum_mem _ (fun j t=> ?_)); rw [MonoidAlgebra.single_mul_single]; refine (MonoidAlgebra.mem_supported).2 ?_
   intros r u; rw [MonoidAlgebra.coeff_single] at u; rw [Finset.mem_singleton.mp (Finsupp.support_single_subset u)]; exact P.mul_mem (MonoidAlgebra.mem_supported.mp h p) (MonoidAlgebra.mem_supported.mp b t)
 algebraMap_mem' x:= by
   change _∈ MonoidAlgebra.supported ℂ ℂ (P:Set (Motif K))
   rw [Algebra.algebraMap_eq_smul_one]; apply Submodule.smul_mem; change _ ∈ MonoidAlgebra.supported ..; apply MonoidAlgebra.mem_supported.mpr; simp [MonoidAlgebra.one_def]
lemma active_iff (P:Submonoid (Motif K))(x:Theater K): x∈ active K P ↔ (∀ i∈ x.coeff.support,i∈ P):= by
 constructor; · intro h i j; exact MonoidAlgebra.mem_supported.mp (show _∈ MonoidAlgebra.supported ℂ ℂ _ from h) j
 exact fun h=> (show x∈ MonoidAlgebra.supported ℂ ℂ (P:Set (Motif K)) from MonoidAlgebra.mem_supported.mpr fun _ v=>h _ v)
lemma flow_active (P:Submonoid (Motif K))(x: Motif K) (h:x∈P): flow K x∈ active K P:= by rw [active_iff]; classical simp [flow,h]
end Show
end alg
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.Playlist.Show.inter_scale
