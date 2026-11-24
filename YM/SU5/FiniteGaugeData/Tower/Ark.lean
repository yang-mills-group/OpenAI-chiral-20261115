import YM.SU5.FiniteGaugeData.Tower.Upright
import YM.Hilbert.Kolmogorov
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
# The resolution Hilbert spaces here

Not making signed reads be *states* on a C⋆-system. Use actual Gram completion
on the whole resolution tower, physical invariant inputs if `strict`, both
for full hierarchy and boson algebra versions. No disconnected Hilberts per
resolution: even the vacuum identifies. No unitary motion group supplied yet.
`strict` does NOT mean restrict first-link-only continuous: concerns the
covariance of all of these physical same-color fields; need to use the second
argument too when mapping by graded step. First-link-only narrow singlets
included.
-/
open scoped InnerProductSpace
open Fock Heat
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}(Q:Resolution (E:=E) Y H D)
variable (j:Axis)(z:ℤ)
local notation "m" u:max=> meshface (Λ:=Λ) z u

/-- positive box of physical gauge singlets / optional restrict on covariance
in the entire chiral two-field algebra -/
def purpose (Z:Calibration)(s:ℤ)(j:Axis)(strict:Bool): Subalgebra ℂ (Family Z) where
 carrier:={F | F∈ wing Z j s ∧ (strict=true→ CovCover Z F)}
 zero_mem':=⟨(wing ..).zero_mem,fun _=> covariant_zero _⟩
 one_mem':=⟨(wing ..).one_mem,fun _=>covariant_one _⟩
 add_mem':=fun {F G} ⟨x,h⟩ ⟨y,t⟩=> ⟨Subalgebra.add_mem (wing ..) x y,fun c=>(covariant_parts _ (h c) (t c)).1⟩
 mul_mem':=fun {F G} ⟨x,h⟩ ⟨y,t⟩=> ⟨Subalgebra.mul_mem (wing ..) x y,fun c=>(covariant_parts _ (h c) (t c)).2⟩
 algebraMap_mem' c:=⟨(wing ..).algebraMap_mem _,fun _=>by rw [Algebra.algebraMap_eq_smul_one]; exact covariant_scale _ (covariant_one _) c⟩
lemma purpose_ok (Z:Calibration)(s:ℤ)(j:Axis)(p:Bool)(F:Family Z): F∈ purpose Z s j p↔F∈ wing Z j s ∧ (p=true→ CovCover Z F):= Iff.rfl

variable (strict:Bool)
abbrev Field:= (purpose (tent Y H) (meshface (Λ:=Λ) z s) j strict).toSubmodule

def freeze (x:Tower.Field Y H s j z strict) : Clock Y H s j z := ⟨x.val,((purpose_ok ..).mp x.property).1⟩
def Choir: Type:= Sigma (fun s:ℕ=> ↥(Tower.Field Y H s j z strict))
def survey (x:Choir Y H j z strict): Voice Y H j z:= ⟨x.1,freeze Y H x.1 j z strict x.2⟩
local notation "vol"=> survey Y H j z strict
local notation "read"=>kennel Y H Q j z

abbrev Arena : Type 1 := _root_.YM.Kernel.Gram (fun v w: Choir Y H j z strict=>read (vol v) (vol w)) -- K explicit?
local notation "AR"=> Arena Y H Q j z strict
include V
lemma voyage_H : Nonempty (AR):=_root_.YM.Kernel.host fun _ v=>eclectic Y H V Q j z (vol ∘ v)
variable (C: Arena Y H Q j z strict)
local notation "W" s:max=> Tower.Field Y H s j z strict

/-- OS vector candidate on supported bosonic marks. -/
def actor (f:W s) := (show _root_.YM.Kernel.Gram _ from C).plant (show Choir Y H j z strict from ⟨s,f⟩)
abbrev Ark.Ht := (show _root_.YM.Kernel.Gram _ from C).H
local notation "B"=> Ark.Ht Y H Q j z strict C
local notation "D₀" S:max=>actor Y H S Q j z strict C -- argument order? C implicit
#check @actor
lemma contracts (s t U:ℕ)(h:s ≤ U)(e:t ≤ U)(f:W s)(g:W t): inner ℂ ((D₀ s) f) ((D₀ t) g)=
 E U (mirror K j (meshface (Λ:=Λ) z U) (stream Y H D s (U-s) f.val) * stream Y H D t (U-t) g.val) :=
 ((show _root_.YM.Kernel.Gram _ from C).measure _ _).trans (vitals Y H Q j z (vol (show Choir Y H j z strict from ⟨s,f⟩)) (vol (show Choir Y H j z strict from ⟨t,g⟩)) h e)
omit V
include C
-- Ext by all individual plants (with all-Hilbert RHSs), no uniform probe
-- norms needed at this equality step
lemma all_voices{x y:B}(p:∀ t:ℕ,∀ v:W t,inner ℂ ((D₀ t) v) x=inner ℂ ((D₀ t) v) y):x=y:=by
 let h:=C
 let D':= innerSL ℂ x -- wrong orientation; want right arg x anti linear. use adjoint flip.
 have hp: ∀ t : B, inner ℂ x t=inner ℂ y t:=by
    let Z:Set B:={t|inner ℂ x t=inner ℂ y t}
    have hz:Set.range (show _root_.YM.Kernel.Gram _ from C).plant⊆Z:=by
       rintro v ⟨k,rfl⟩; change inner ℂ x ((D₀ k.1) k.2)=inner ℂ y ((D₀ k.1) k.2); exact _root_.star_injective (show _ from (inner_conj_symm ..).trans ((p _ _).trans (inner_conj_symm ..).symm)) -- star vs conj
    have hw: Dense Z:= (show _root_.YM.Kernel.Gram _ from C).dense.mono (by
      intro v u
      exact Submodule.span_induction (s:= Set.range (show _root_.YM.Kernel.Gram _ from C).plant) (p:=fun v _=>v∈Z) (fun v t=>hz t) (show inner ℂ x 0=_ from by simp) (fun u v _ _ (h:inner ℂ _ _=_)(g:inner ℂ _ _=_)=> show inner ℂ x (u+v)=_ from by rw [inner_add_right,inner_add_right,h,g]) (fun a i _ (e:inner ℂ _ _=_ )=> show inner ℂ x (a • i)=_ from by rw [inner_smul_right,inner_smul_right,e]) u)
    intro v
    have h: IsClosed Z:= isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    exact closure_minimal (Set.Subset.refl Z) h (hw v)
 exact ext_inner_right ℂ hp -- check

-- linear. compare at any common registration rung via contracts.
include V
noncomputable def arrows(s:ℕ): (W s) →ₗ[ℂ] B where
 toFun:=actor Y H s Q j z strict C
 map_add' f g:=by
    apply all_voices Y H Q j z strict C; intro t v
    let u:=max s t; have hs:s≤u:=le_max_left ..; have ht:t≤u:=le_max_right ..
    rw [inner_add_right,contracts Y H V Q j z strict C t s u ht hs,contracts Y H V Q j z strict C t s u ht hs,contracts Y H V Q j z strict C t s u ht hs,AddSubmonoid.coe_add]
    have hq(a:W s):TestFamily K true a.val:= (exam j _ K ((purpose_ok ..).mp a.property).1).1
    let Z:=stream Y H D s (u-s); let T:=stream Y H D t (u-t) v.val
    rw [woven_add Y H Q s (u-s) (hq f) (hq g),mul_add]
    have hr(a:W s): TestFamily K true (Z a.val):= streams_test Y H Q s _ (hq a)
    let p:= ((purpose_ok ..).mp v.property).1
    have hZ:T ∈ wing K j (meshface (Λ:=Λ) z u):= (newer Y H Q j z ht (freeze Y H t j z strict v)) -- tune
    have e:= (exam j _ K hZ).2
    exact E_add Y H V u (e.mul (hr f)) (e.mul (hr g))
 map_smul' a f:=by
    apply all_voices Y H Q j z strict C; intro t v
    change inner ℂ ((D₀ t) v) ((D₀ s) (a • f))= inner ℂ ((D₀ t) v) (a • (D₀ s) f); rw [inner_smul_right]
    let u:=max s t; have hs:s≤u:=le_max_left ..; have ht:t≤u:=le_max_right ..
    rw [contracts Y H V Q j z strict C t s u ht hs,contracts Y H V Q j z strict C t s u ht hs,Submodule.coe_smul]
    have hq(a:W s):TestFamily K true a.val:= (exam j _ K ((purpose_ok ..).mp a.property).1).1
    let Z:=stream Y H D s (u-s); let T:=stream Y H D t (u-t) v.val
    rw [woven_smul Y H Q s _ (hq f) a,Algebra.mul_smul_comm]
    have hr(a:W s): TestFamily K true (Z a.val):= streams_test Y H Q s _ (hq a)
    have hZ:T∈ wing K j (meshface (Λ:=Λ) z u):=newer Y H Q j z ht (freeze Y H t j z strict v)
    exact E_scale Y H V u ((exam j _ K hZ).2.mul (hr _)) a

#check ext_inner_right
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.contracts
#print axioms YM.CF.Buffered.Afterglow.Tower.arrows
