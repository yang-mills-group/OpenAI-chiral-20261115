import YM.SU5.FiniteGaugeData.Tapestry.Cabana
import YM.SU5.FiniteGaugeData.Tapestry.Chroma
import YM.SU5.FiniteGaugeData.Tapestry.Height
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill

/-!
# Local observable Algebra at each level `s`. Region support.

At resolution `s` use `Dome` of all the Scaffold's *supported, even* marked tests
`f : Family K, TestFamily K true f`. This is the even observable algebra at that
scale, prior to restricting to gauge-neutral and first-link only tests. It is a
COMMUTATIVE algebra (even operators in the chiral polarization). There is no
use in this theorem of C*-positivity for a state on this algebra and we don't
equip it with any C*-structure. It allows arbitrary products at one level
where TOTAL parity is even (so can make gauge-frame & path tests mixed with
even products of odd chiral insertions). We build the theory of THESE
observables (not the theory of field/odd-fermion correlations: e.g. a mixed
product of two odd observables at different resolution levels won't be a
polynomial here). The gauge-invariant local observable algebra will be built
from the Domes; see the distinctions `vestibule K false` using only first
pane & continuous, `enclave` (gauge invariant, can read both first and second
pane), and the multi-level results ahead. At no point is the auxiliary law
asserted a second physical gauge field: the reading is always on one city and
that same Cape. Auxiliary-dependent tests admitted only where made explicit.

Don't give Dome a global norm. Consider the subalgebras with declared
facing/support & width, and measure their norm by Swatches, using bona fide
link/matter sup costs. Possible co-usage of other locally convex topologies later
shouldn't confuse these relatively direct measurements.
-/
set_option quotPrecheck false
variable (K : Calibration)
def screenHall : Subalgebra ℂ (Family K) where
 carrier := {f| TestFamily K true f}
 add_mem' := fun p q=> TestFamily.add p q
 mul_mem' := fun p q=> TestFamily.mul p q
 zero_mem' := TestFamily.zeroT
 one_mem':= TestFamily.oneT
 algebraMap_mem' := fun z=>by rw [Algebra.algebraMap_eq_smul_one]; exact TestFamily.oneT.scale z
abbrev Dome := ↥(screenHall K)
lemma marque {x:Family K}: x∈ screenHall K ↔ TestFamily K true x:=Iff.rfl
instance domeRing : CommRing (Dome K) where
  mul_comm x y := Subtype.ext <| ((marque K).mp x.property).comm ((marque K).mp y.property)
-- prove Faithful Algebra & Nontrivial. filler λ independent K.x.
lemma lifting₁ : (1 : Family K)≠0:=fun e=> one_ne_zero (α:=FC (Single (K.c 1))) (congrFun (congrFun e 1) (1,1)) -- syntax one_ne_zero implicit
instance : Nontrivial (Dome K) := ⟨⟨1,0,fun h=> lifting₁ K (congrArg ((screenHall K).val) h)⟩⟩ -- uses fake projection tune
instance (priority:=high) : Algebra ℂ (Dome K):=inferInstanceAs (Algebra ℂ ↥(screenHall K)) -- maybe diamond

-- Support WITHOUT neutral qualification. first with cont still not neutral generally.
private lemma widenA (wide:Bool)(S:Finset Cover)(f:Family K)(p:InTest K wide S false f): InTest K true S false f:=by cases wide; exact p.widen; exact p
variable (S:Finset Cover)(wide:Bool)
def bay : Subalgebra ℂ (Dome K) where
 carrier:={ f:Dome K| InTest K wide S false f.val }
 mul_mem':= fun {x y} p q=> InTest.mul (b:=false) (c:=false) p q -- names
 add_mem':= fun {x y} p q=> InTest.add p q
 zero_mem':= InTest.zero
 one_mem':= InTest.one
 algebraMap_mem':= fun z=> by rw [Algebra.algebraMap_eq_smul_one]; exact InTest.smul (K:=K) (f:=1) z .one
private lemma bayhere {f:Dome K} : f∈bay K S wide ↔ InTest K wide S false f.val:= Iff.rfl -- public
lemma locates {f:Dome K}: f∈bay K S wide ↔ InTest K wide S false f.val:= bayhere ..
lemma widerBay: bay K S wide≤ bay K S true:= fun _ h=> widenA K wide S _ h
lemma tallerBay {B:Finset Cover} (p:S⊆B): bay K S wide ≤ bay K B wide:= fun _ h=> InTest.mono h p
lemma findsBay (f:Dome K): ∃ S,f∈ bay K S true:= (TestFamily.paid f.property)
def badge : Swatch S →ₗ[ℂ] Dome K :=
 LinearMap.codRestrict (screenHall K).toSubmodule (render S K) (fun f=> broadCompile K S (texture ..)) -- beware topology instances
@[simp] lemma domTag (x:Swatch S): (badge K S x).val= render S K x:=rfl
lemma locatesBadge (x:Swatch S): badge K S x ∈ bay K S true:= texture ..
lemma badge_inj : Injective (badge K S):= fun x y h=> render_inj _ _ (congrArg Subtype.val h)
lemma accolade (f:Dome K)(p:f∈ bay K S true): ∃ x,badge K S x=f:=by
  obtain ⟨x,h⟩:= rendered S K ((bayhere ..).mp p); exact ⟨x, Subtype.ext h⟩
lemma badgeRange : LinearMap.range (badge K S)=(bay K S true).toSubmodule:= by ext f:1; exact ⟨by rintro ⟨x,rfl⟩; exact locatesBadge .., accolade K S f⟩
@[simp] lemma laureled: badge K S (colorless K S)=1 := Subtype.ext (bareUnit ..)
lemma badge_brocade (x y): badge K S (brocade K S x y)=badge K S x*badge K S y:= Subtype.ext (bareMult ..)
lemma widenBadge {T:Finset Cover}(h:S⊆T)(x:Swatch S): badge K T (Tapestry.broad K S T h x)=badge K S x:= Subtype.ext (broadRender ..)
def precinct (x:Dome K): Finset Cover:= (findsBay K x).choose
lemma precinct_spec (x:Dome K): x∈bay K (precinct K x) true:= (findsBay K x).choose_spec
def trophy {S:Finset Cover}(x:Dome K)(p:x∈bay K S true):Swatch S:=(accolade K S x p).choose -- optional syntax
lemma trophy_at {S:Finset Cover}(x:Dome K)(p:x∈bay K S true): badge K S (trophy K x p) = x:= (accolade K S x p).choose_spec
lemma trophy_bounds {m:Side}{A:ℝ}{S:Finset Cover}(x:Dome K)(p:x∈bay K S true)(v:Hosp S (K.c m))(u:∀ z, ‖x.val m z‖ ≤ A): ‖trophy K x p‖ ≤ A :=sampling S K m v _ fun z=>by rw [←appearRender,←domTag,trophy_at]; exact u z

def vestibule : Subalgebra ℂ (Dome K) where
 carrier := {f:Dome K| ∃ S,f∈bay K S wide}
 zero_mem':= ⟨∅,(bay K ∅ wide).zero_mem⟩
 one_mem':= ⟨∅,(bay K ∅ wide).one_mem⟩
 algebraMap_mem':= fun z=> ⟨∅,(bay K ∅ wide).algebraMap_mem z⟩
 add_mem' {x y} h p:= by obtain ⟨S,t⟩:=h; obtain ⟨T,w⟩:=p; exact ⟨S∪T, (bay K (S∪T) wide).add_mem (tallerBay K S wide subset_union_left t) (tallerBay K T wide subset_union_right w)⟩
 mul_mem' {x y} h p:= by obtain ⟨S,t⟩:=h; obtain ⟨T,w⟩:=p; exact ⟨S∪T, (bay K (S∪T) wide).mul_mem (tallerBay K S wide subset_union_left t) (tallerBay K T wide subset_union_right w)⟩
def enclave : Subalgebra ℂ (Dome K) where
 carrier := {f:Dome K| Neutral K f.val }
 add_mem' {x y} (p:Neutral K x.val)(q:Neutral K y.val) :=
   ofSinglet (K:=K) (precinct_spec K (x+y)) (singlet_add (impliesSinglet p) (impliesSinglet q)) -- type table
 mul_mem' {x y} (p:Neutral K x.val)(q:Neutral K y.val) :=
   ofSinglet (K:=K) (precinct_spec K (x*y)) (singlet_mul (impliesSinglet p) (impliesSinglet q))
 zero_mem':= ofSinglet (InTest.zero (K:=K) (wide:=true) (S:=∅) (b:=false)) singlet_zero
 one_mem':= ofSinglet (InTest.one (K:=K) (wide:=true) (S:=∅)) singlet_identity
 algebraMap_mem':= fun z=>by rw [Algebra.algebraMap_eq_smul_one]; exact ofSinglet (InTest.smul (K:=K) (wide:=true) (S:=∅) (f:=1) (b:=false) z .one) (singlet_smul singlet_identity z)
lemma vestibule_spec {x:Dome K}: x∈vestibule K wide ↔ ∃ S,x∈bay K S wide := Iff.rfl
lemma vestibuleFull : vestibule K true = ⊤:= top_unique (fun x u=>findsBay K x)
lemma concentration {x:Dome K}(p:x∈vestibule K false)(m:Side): ∃ g:Window.Evaluation (K.c m), x.val m=toMark g ∧ Continuous g:=
  let h:=(vestibule_spec K false).1 p; ((bayhere K h.choose false).1 h.choose_spec).only_cont m
lemma enclave_spec {x:Dome K}: x∈enclave K ↔ ∀ m:Side,covariant (x.val m):= Iff.rfl
lemma enclaveS {x:Dome K}: x∈enclave K ↔ Singlet x.val:= ⟨impliesSinglet, ofSinglet ((bayhere ..).1 (precinct_spec ..))⟩
/-- All the (even) TestFamily false observables, not just a set of words. -/ -- syntax tune
abbrev Native := vestibule K false ⊓ enclave K
lemma native_spec {x:Dome K}: x∈ Native K ↔ TestFamily K false x.val:=by
 change (_∧_)↔ _; exact ⟨fun p=> ⟨(vestibule_spec K false).mp p.1,fun _=>(enclaveS ..).mp p.2⟩,fun p=> ⟨p.paid,(enclaveS ..).mpr (p.allowed rfl)⟩⟩
def trulyNamed {f:Family K}(p:TestFamily K false f): Dome K:= ⟨f,broadCompile K p.paid.choose p.paid.choose_spec.widen⟩
lemma nativeRepresentation {f:Family K}(p:TestFamily K false f): trulyNamed K p∈ Native K:= (native_spec K).mpr p

-- reflection on any axis & z
variable (a:Axis)(z:ℤ)
def aureole : Dome K→ₗ⋆[ℂ] Dome K where
 toFun x:= ⟨bounce K z a x.val,broadCompile K (negativeSide (precinct K x) z a) (bounceEligible z a ((bayhere ..).mp (precinct_spec ..)))⟩
 map_add' x y:= Subtype.ext (bounce_plus (K:=K) (f:=x.val) (g:=y.val) z a)
 map_smul' r x:= Subtype.ext (bounce_scale (K:=K) (f:=x.val) z a r)
@[simp] lemma aureole_eq(x:Dome K): (aureole K a z x).val=bounce K z a x.val:= rfl
lemma aureoleUnit : aureole K a z 1=1:= Subtype.ext (bounce_identity z a)
lemma aureoleProduct (x y:Dome K): aureole K a z (x*y)=aureole K a z x*aureole K a z y:=Subtype.ext (bounce_times ..) -- implicit
lemma aureoleBay (x:Dome K)(p:x∈bay K S wide):aureole K a z x∈bay K (negativeSide S z a) wide:= bounceEligible z a ((bayhere ..).mp p)
lemma aureoleReflect (x:Swatch S): aureole K a z (badge K S x)= badge K (negativeSide S z a) (mirrorL K S z a x):= Subtype.ext (mirrored_render K S z a x).symm
lemma aureoleTwice (x:Dome K): aureole K a z (aureole K a z x) = x:=by obtain ⟨S,s⟩:=findsBay K x; obtain ⟨y,rfl⟩:= accolade K S x s; exact Subtype.ext (mirror_twice K S z a y)
lemma aureoleNarrow {x:Dome K}(p:x∈vestibule K wide): aureole K a z x∈vestibule K wide:= (vestibule_spec ..).mpr ⟨_, aureoleBay K _ _ a z x ((vestibule_spec ..).mp p).choose_spec⟩
lemma aureoleEnclave {x:Dome K}(p:x∈enclave K): aureole K a z x∈enclave K:= (enclave_spec K).mpr fun m=> covariant_reflected (((bayhere ..).mp (precinct_spec K x)).support m) ((enclave_spec K).mp p m) z a
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.badgeRange
#print axioms YM.CF.Buffered.Afterglow.Tapestry.native_spec
#print axioms YM.CF.Buffered.Afterglow.Tapestry.aureoleEnclave
#print axioms YM.CF.Buffered.Afterglow.Tapestry.aureoleTwice
