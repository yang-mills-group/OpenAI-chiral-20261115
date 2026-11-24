import YM.CF.Fixed.OneParticle
import YM.CF.Reed.Dance

/-!
Local supports for probes in d8's CAR convention. The fermion words are not
all of the matrix algebra (e.g. not closed under raw matrix `star`). They are
in the physical `Reed.Fine` subspace. At this boundary the probes use the
letters `(Reed.think (upperIndices N)).term r`; even probes may use any even
products of these. We use `Reed.reverseW` (including its `Reflect.chord`
phase on odd words) both for the reflected product and to define a dagger
(label conjugation on matter). Gauge-link functions are evaluated on the
Euclidean SU links. Our real form for the gauge function in the onsite
dagger on this test algebra is complex conjugation. We are not interpreting
a single gauge link variable as a component of a tensor reconstructed as a
Hermitian operator.

These conventions are for the test algebra. No claim about attachment to local
real-time operators in this module.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Fixed
open Function Fock NormedSpace SU Lat Lattice Cube Finset Scroll MeasureTheory Tulip
open Reed (Fine reverseW)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
attribute [local instance] opCStarAlgebra

section lemmas
variable {I : Type*} [LinearOrder I] [Fintype I]

lemma fine_growRegion {s p q : Finset I} {b} {A} (h : Fine s p b A) (hpq : p⊆q) :
    Fine s q b A := by
  induction h with
  | empty => apply Fine.empty
  | one => exact Fine.one
  | seed x hx => exact .seed x (hpq hx)
  | add _ _ ih it => exact ih.add it
  | scale _ c ih => exact ih.scale c
  | grow _ _ ih it => exact ih.grow it

lemma commuteWithGauge_theta {S : Finset I} {b : Bool} {A}
    (U V W : UNI I) (e : U.val*V.val=W.val*U.val) (h : Sector S b A) :
    Fock.theta U (twist (quantU V) A)= twist (quantU W) (Fock.theta U A) := by
  have hu (P:Ket I) : acts U.val (acts V.val P)=acts W.val (acts U.val P) := by rw [←act_mul, ←act_mul,e]
  have ht (i:I) : Fock.theta U (twist (quantU V) (put i))= twist (quantU W) (Fock.theta U (put i)) := by
    rw [←create_put,twist_create,Fock.theta_upV,Fock.theta_upV,twist_scalar,twist_remove,hu]
  induction h with
  | zero=> rw [map_zero,Fock.theta_zero,map_zero]
  | one=> rw [map_one,Fock.theta_one,map_one]
  | up i _=> exact ht i
  | down i _=> rw [takeF,map_star,Fock.theta_star,Fock.theta_star,map_star,ht]
  | add _ _ ih it=> rw [map_add,Fock.theta_add,Fock.theta_add,map_add,ih,it]
  | scale _ _ ih=> rw [twist_scalar,Fock.theta_smul,Fock.theta_smul,twist_scalar,ih]
  | mul _ _ ih it=> rw [map_mul,Fock.theta_mul,Fock.theta_mul,map_mul,ih,it]

lemma commuteWithGauge {S : Finset I} {b : Bool} {A}
    (U V W : UNI I) (e : U.val*V.val=W.val*U.val) (h : Sector S b A) :
    reverseW U b (twist (quantU V) A)= twist (quantU W) (reverseW U b A) := by
  unfold reverseW; rw [commuteWithGauge_theta U V W e h,twist_scalar]

lemma add_reverseW (U : UNI I) (b : Bool) (A B : FC I) :
    reverseW U b (A+B)=reverseW U b A + reverseW U b B:=by rw [reverseW,Fock.theta_add,smul_add]; rfl
end lemmas

variable {N : Side} (X : Support (More N)) (i : Axis) (b : Bool)

/-- Ambient cutoff algebra; evaluation is finite dimensional in the fermionic
variables. -/
abbrev Test (N : Side) := Bkg (More N) → FC (Single N)

/-- Reflection adjoint of a `b`-graded test. -/
def reflectTest (F : Test N) : Test N := fun U =>
  reverseW (reflectP N i) b (F (reflConfig N i U))

/-- Onsite label adjoint convention. Spacetime reflection of the probe (pulls
links, permutes matter sites with the anticut sign), including this adjoint,
is implemented on these tests by `reflectTest`. The gauge coefficient in
`adjTest` is just conjugated, and `reflectTest` takes its complex conjugate
at the reflected Euclidean configuration. -/
def adjTest (F : Test N) : Test N := fun U => reverseW (adjSpin N i) b (F U)

lemma reflectTest_cont {F : Test N} (h : Continuous F) : Continuous (reflectTest i b F) :=
  (continuous_const (y:=Reflect.chord b)).smul
    ((Fock.theta_cont _).comp (h.comp (reflConfig_cont N i)))
lemma adjTest_cont {F : Test N} (h : Continuous F) : Continuous (adjTest i b F) :=
  (continuous_const (y:=Reflect.chord b)).smul ((Fock.theta_cont _).comp h)

/-- The finite-level local tests. `X` is a set of gauge vertices: this bound
must actually imply dependence only on links with both endpoints in `X` and
on Fock letters at matter nodes in `X`. We take `i=timeAxis` for temporal
reflection; it is not part of the definition of a localized probe. -/
structure InRegion (F : Test N) : Prop where
  cont : Continuous F
  depends : LocalOn X F
  support (U) : Fine (upperIndices N) (matterRegion N X) b (F U)
  inv (g: Site (More N)→ SU.E) (U) :
    F (Lattice.gauge g U) = twist (quantU (tradew N g)) (F U)

namespace InRegion
variable {X b}
variable {F G : Test N} {e} (h : InRegion X b F) (k : InRegion X e G)

include h
lemma rotate : InRegion (reflRegion N i X) b (reflectTest i b F) := by
  refine ⟨reflectTest_cont _ _ h.cont,fun U V y=>?_,fun U=>?_,fun g U=>?_⟩
  · exact congrArg (reverseW _ b) (h.depends _ _ (reflConfig_agrees N i U V X y))
  · exact Fine.returnW (reflectP_region N i X) (reflectP_upper N i) (h.support _)
  unfold reflectTest; rw [reflConfig_gauge,h.inv]
  exact commuteWithGauge _ _ _ (reflectP_gauge N i g) (h.support _).sector

lemma reflect_involutive : reflectTest i b (reflectTest i b F)=F := by
  funext U; unfold reflectTest; rw [square_reflConfig]
  exact Fine.realAdj (h.support U) (reflectP_square N i)

lemma dagger : InRegion X b (adjTest i b F):=
  ⟨adjTest_cont _ _ h.cont,fun _ _ e=> congrArg (reverseW _ b) (h.depends _ _ e),
    fun U=> Fine.returnW (adjSpin_region N i X) (adjSpin_upper N i) (h.support _),
    fun g U=>by unfold adjTest; rw [h.inv]; exact commuteWithGauge _ _ _ (adjSpin_gauge N i g) (h.support _).sector⟩
lemma dagger_involutive : adjTest i b (adjTest i b F)= F:=
  funext fun U => Fine.realAdj (h.support U) (adjSpin_square N i)

lemma enlarge (Y : Support (More N)) (g : X ⊆ Y) : InRegion Y b F :=
  ⟨h.cont,fun _ _ z=> h.depends _ _ (agrees_mono z g),
    fun U=> fine_growRegion (h.support U) (fun _ x=> (mem_matterRegion ..).mpr (g ((mem_matterRegion ..).mp x))),
    h.inv⟩
lemma add (g : InRegion X b G) : InRegion X b (F+G):=
  ⟨h.cont.add g.cont,fun _ _ p=>congrArg₂ (·+·) (h.depends _ _ p) (g.depends _ _ p),
    fun U=>(h.support U).add (g.support U),fun s U=>by rw [Pi.add_apply,h.inv,g.inv,Pi.add_apply,map_add]⟩
lemma cash (z : ℂ) : InRegion X b (z • F):=
  ⟨continuous_const.smul h.cont,fun _ _ p=>congrArg (z • ·) (h.depends _ _ p),
   fun U=>(h.support U).scale _, fun s U=>by rw [Pi.smul_apply,h.inv,Pi.smul_apply,twist_scalar]⟩
omit h
lemma zero (X : Support (More N)) (b : Bool) : InRegion X b 0:=
  ⟨continuous_const,fun _ _ _=>rfl,fun _=> Fine.empty _,fun _ _=>(map_zero _).symm⟩
lemma one (X : Support (More N)) : InRegion X false 1:=
  ⟨continuous_const,fun _ _ _=>rfl,fun _=> Fine.one,fun _ _=>(map_one _).symm⟩

include h k
lemma mul : InRegion X (b.xor e) (F*G):=
  ⟨h.cont.mul k.cont,fun _ _ p=>congrArg₂ (·*·) (h.depends _ _ p) (k.depends _ _ p),
    fun U=> (h.support U).grow (k.support U),fun s U=>by rw [Pi.mul_apply,h.inv,k.inv,Pi.mul_apply,map_mul]⟩
lemma reflect_mul :
    reflectTest i (b.xor e) (F*G)=reflectTest i e G*reflectTest i b F :=
  funext fun U=> Fine.reverse_mul (reflectP_region N i X) (reflectP_upper N i)
    (h.support (reflConfig N i U)) (k.support _)
lemma adj_mul : adjTest i (b.xor e) (F*G)=adjTest i e G*adjTest i b F :=
  funext fun U => Fine.reverse_mul (adjSpin_region N i X) (adjSpin_upper N i) (h.support U) (k.support _)

end InRegion

/-- Gauge-invariant, physical **even** local test algebra. We use complex linear
combinations within this algebra. -/
def probes : Subalgebra ℂ (Test N) where
  carrier := InRegion X false
  one_mem' := InRegion.one _
  zero_mem' := InRegion.zero _ _
  algebraMap_mem' := fun a=>by rw [Algebra.algebraMap_eq_smul_one]; exact (InRegion.one X).cash a
  add_mem' := InRegion.add
  mul_mem' := fun h g=> InRegion.mul h g

@[simp] lemma mem_probes (F : Test N) : F∈probes X ↔ InRegion X false F:=Iff.rfl

/-- One net for all regions. Even products commute; the involution below gives
the dagger (time-axis convention). -/
lemma enlarge_probes {X Y : Support (More N)} (h : X⊆Y) : probes X ≤ probes Y :=
  fun _ p=> InRegion.enlarge p Y h

lemma even_commute {X Y : Support (More N)} {F G : Test N} (h : F∈probes X) (k : G∈probes Y):
    F*G=G*F := by
  let T := X ∪ Y
  have hp : InRegion T false F:=enlarge_probes (show X⊆T from subset_union_left) h
  have hq : InRegion T false G:=enlarge_probes (show Y⊆T from subset_union_right) k
  funext U
  rw [(show (F*G) U= _ from (hp.support U).sign_com (hq.support U))];
  exact one_smul ℂ _

/-- Strictly positive-time domain. -/
def positiveRegion : Support (More N):=univ.filter fun x => 0<(x i).val ∧ (x i).val<N.val
/-- Reflected pairing domain: no fermions or gauge links on the reflection planes. -/
abbrev PositiveTest (F : Test N) := F∈ probes (positiveRegion (N:=N) i)
/-- Plain unplaced (full-torus) probes. -/
abbrev Probe (F : Test N) := F∈probes (X:=univ)
lemma positive_to_probe {F : Test N} (h : PositiveTest i F) : Probe F :=
  enlarge_probes (subset_univ _) h
lemma probe_reflect {F : Test N} (h : Probe F) : Probe (reflectTest i false F) :=
  enlarge_probes (subset_univ _) ((show InRegion (univ:Support (More N)) false F from h).rotate i)

lemma reflectTest_add (F G : Test N) : reflectTest i b (F+G)= reflectTest i b F+reflectTest i b G:=
  funext fun U => add_reverseW _ b (F (reflConfig N i U)) _
lemma reflectTest_smul (F : Test N) (z : ℂ) : reflectTest i b (z•F)=star z • reflectTest i b F:=
  funext fun U=> Fine.trans _ b (F (reflConfig N i U)) z
lemma adjTest_add (F G : Test N) : adjTest i b (F+G) = adjTest i b F + adjTest i b G:=
  funext fun U=> add_reverseW _ b (F U) _
lemma adjTest_smul (F : Test N) (z : ℂ) : adjTest i b (z•F)= star z • adjTest i b F:=
  funext fun U=>Fine.trans _ b (F U) _

end YM.CF.Fixed
