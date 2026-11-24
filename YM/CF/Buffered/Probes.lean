import YM.CF.Buffered.Lifted
import YM.CF.Buffered.History

/-!
# Entire buffered chiral test class

Represent by generating the words, so they are bona fide fixed probes on
this whole system. MarkG = false special restriction (link, continuous
case, no \hat V reads), MarkG true permits Borel V-pairs with local sup
bound (per joint-E). Singlet rule added as its own condition: positivity is
independent of that condition; availability of the limiting values need not
be. Coefficients are on *cover* fields. E.g. any Borel function on the
local coordinates gives one by precomposition with restriction. Fock support
uses fixed integer sites of matter, in corresponding signed frames.
All these tests allow arbitrary finite combinations/ordered products, no
positivity assumption on scalar tests. Later lemmas verify that the finite
reflection collects to the reflected cover formula.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG
open Lifted
open Reed (Fine)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable (K : Calibration)
-- family of actual level-zero probes
abbrev Family (K : Calibration) := ∀ m : Side, Mark (K.c m)
def reflected (z : ℤ) (f : Family K) : Family K := fun m => reflMark 3 z (f m)
abbrev thetaK := reflected K K.plane0
def scalar (f : PairsC→ℂ) : Family K := fun m V=> f (onC (K.c m) V.1,onC (K.c m) V.2) • 1
def creation (x : Cover) (i : SpinIdx) (b : SU.Slot) : Family K := fun m _=> create (basisC (K.c m) x i b)
def removal (x : Cover) (i : SpinIdx) (b : SU.Slot) : Family K := fun m _=> Fock.remove (basisC (K.c m) x i b)
structure Coeff (wide : Bool) (S : Finset Cover) (f : PairsC → ℂ) : Prop where
  narrow : wide=false → ∃ g: LinksC → ℂ, Continuous g ∧ f = g ∘ Prod.fst
  env : Envelope f
  locus (x y : PairsC) (p : Agrees S x.1 y.1) (q : Agrees S x.2 y.2) : f x=f y
inductive InTest (wide : Bool) (S : Finset Cover) : Bool→ Family K → Prop where
 | seed {f : PairsC → ℂ} (p : Coeff wide S f) : InTest wide S false (scalar K f)
 | creator {x : Cover} {i : SpinIdx} (b : SU.Slot) (p : i∈plusHalf) (v : nodeC x∈S) : InTest wide S true (creation K x i b)
 | remover {x : Cover} {i : SpinIdx} (b : SU.Slot) (p : i∉plusHalf) (v : nodeC x∈ S) : InTest wide S true (removal K x i b)
 | zero {b} : InTest wide S b 0
 | one : InTest wide S false 1
 | add {f g b} : InTest wide S b f → InTest wide S b g → InTest wide S b (f+g)
 | smul {f b} (c : ℂ) : InTest wide S b f → InTest wide S b (c • f)
 | mul {f g b c} : InTest wide S b f → InTest wide S c g → InTest wide S (b.xor c) (f*g)
variable {S T : Finset Cover} {K} {wide : Bool} {i : SpinIdx} {b c a : Bool}
lemma Coeff.fromC (wide : Bool) (S : Finset Cover) {f : LinksC → ℂ} (h : Continuous f) (d : ∀ x y:LinksC, Agrees S x y → f x=f y) : Coeff wide S (f ∘ Prod.fst) := ⟨fun _=>⟨_,h,rfl⟩, Env.compact (h.comp continuous_fst), fun _ _ p _=>d _ _ p⟩
lemma Coeff.mono {f : PairsC → ℂ} (p : Coeff wide S f) (h : S ⊆ T) : Coeff wide T f:= ⟨p.narrow,p.env,fun _ _ u v=> p.locus _ _ (fun i x y=> u i (h x) (h y)) (fun i x y=>v i (h x) (h y))⟩
namespace InTest
variable {f g : Family K}
lemma widen (p : InTest K false S b f) : InTest K true S b f := by
 induction p with
 | seed p => exact .seed ⟨fun v=> by contradiction,p.env,p.locus⟩
 | creator b p v=> exact .creator b p v
 | remover b p v=> exact .remover b p v
 | zero=>exact .zero
 | one=>exact .one
 | smul a _ ih=> exact .smul a ih
 | add _ _ a b=> exact .add a b
 | mul _ _ a b=> exact .mul a b
lemma mono (p : InTest K wide S b f) (h : S ⊆ T) : InTest K wide T b f := by
 induction p with
 | seed p=> exact .seed (p.mono h)
 | creator b p v=> exact .creator b p (h v)
 | remover b p v=> exact .remover b p (h v)
 | zero=>exact .zero
 | one=>exact .one
 | smul a _ ih=> exact .smul a ih
 | add _ _ a b=> exact .add a b
 | mul _ _ a b=> exact .mul a b
private lemma basis_halfUp (n : Side) (x : Cover) (i : SpinIdx) (b : SU.Slot) (p : i∈plusHalf) : withinM (Tset n) (basisC n x i b) := by
 unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index n x i b) ((mem_Tset ..).mpr p)]
private lemma basis_halfDown (n : Side) (x : Cover) (i : SpinIdx) (b : SU.Slot) (p : i∉plusHalf) : withinM (Tset n)ᶜ (basisC n x i b) := by
 unfold withinM basisC; rw [map_smul,within_basis (Tset n)ᶜ (Lifted.index n x i b) (mem_compl.mpr fun h=>p ((mem_Tset ..).mp h))]
private lemma basis_within (n : Side) (x : Cover) (i : SpinIdx) (b : SU.Slot) (p : nodeC x∈ S) : withinM (modesIn n (S.image (wrap (More n)))) (basisC n x i b) := by
 have he : Lifted.index n x i b ∈ modesIn n (S.image (wrap (More n))) := by rw [modes_at]; change node (wrap n x) ∈_; rw [node_of]; exact mem_image_of_mem _ p
 unfold withinM basisC; rw [map_smul, within_basis _ _ he]
lemma support (p : InTest K wide S b f) (m : Side) : AtSupport b (S.image (wrap (More (K.c m)))) (f m) := by
 induction p with
 | @seed f p=>
    let X(V : Fields (K.c m)):= (onC (K.c m) V.1,onC (K.c m) V.2); refine ⟨pole_w (f ∘ X) (fun x:ℂ=> x • (1:FC (Single (K.c m)))) (continuous_id.smul continuous_const) (Env.along p.env ?_),fun x y u v=> congrArg (fun x:ℂ=> x • (1:FC _)) (p.locus (X x) (X y) (on_agree _ u) (on_agree _ v)),fun U=>Fine.one.scale _⟩
    exact ((on_cont _).measurable.comp measurable_fst).prodMk ((on_cont _).measurable.comp measurable_snd)
 | @creator x i b p v=> exact ⟨rite_c _, fun _ _ _ _=> rfl, fun _=> fine_create _ (basis_halfUp _ x _ b p) (basis_within _ x i b v)⟩
 | @remover x i b p v=> exact ⟨rite_c _, fun _ _ _ _=> rfl, fun _=> fine_remove _ (basis_halfDown _ x _ b p) (basis_within _ x i b v)⟩
 | zero=> exact AtSupport.zeroM
 | one=> exact AtSupport.oneM _
 | add _ _ a b=> exact a.addM b
 | smul a _ ih=> exact ih.smulM a
 | mul _ _ a b=> exact a.mulM b
lemma sum {I : Type*} (s : Finset I) (f : I→ Family K) (p : ∀ i∈s,InTest K wide S b (f i)) : InTest K wide S b (∑ i∈s, f i) := by
 classical
 induction s using Finset.induction_on with
 | empty => rw [sum_empty]; exact .zero
 | insert i s h ih=> rw [sum_insert h]; exact .add (p _ (mem_insert_self ..)) (ih fun j v=> p _ (mem_insert_of_mem v))
-- narrow means link-only and continuous
lemma only_cont (p : InTest K false S b f) (m : Side) : ∃ g : Evaluation (K.c m), f m=toMark g ∧ Continuous g := by
 induction p with
 | @seed f p=> obtain ⟨g,h,rfl⟩:= p.narrow rfl; exact ⟨_,rfl,(h.comp (on_cont _)).smul continuous_const⟩
 | creator=> exact ⟨_,rfl,continuous_const⟩
 | remover=> exact ⟨_,rfl,continuous_const⟩
 | zero=> exact ⟨0,rfl,continuous_const⟩
 | one=> exact ⟨1,rfl,continuous_const⟩
 | add _ _ a b=> obtain ⟨g,h,t⟩:= a; obtain ⟨f,v,w⟩:= b; exact ⟨g+f,congrArg₂ (· + ·) h v,t.add w⟩
 | smul a _ ih=> obtain ⟨g,h,t⟩:= ih; exact ⟨a • g,congrArg (fun f=> a • f) h,continuous_const.smul t⟩
 | mul _ _ a b=> obtain ⟨g,h,t⟩:= a; obtain ⟨f,v,w⟩:= b; exact ⟨g*f,congrArg₂ (· * ·) h v,t.mul w⟩
end InTest
-- gauge equivariance evaluated on its two arguments. Permit any accidental symmetries,
-- and don't constrain the probe on tiny sides (even though it is still evaluated there
-- as a function so we don't have to carry size proofs). 
def simultaneous {n : Side} (g : Seat n→ SU.E) (x : Fields n) := Prod.map (Lattice.gauge g) (Lattice.gauge g) x
def covariant {n : Side} (f : Mark n) := ∀ (g : Seat n→ SU.E) (x : Fields n), f (simultaneous g x)=twist (quantU (tradew n g)) (f x)
lemma covariant_reflected {n : Side} {f : Mark n} {G : Support (More n)} (h : AtSupport b G f) (p : covariant f) (s : ℤ) (i : Axis) : covariant (reflMark i s f) := by
 intro g x; unfold reflMark; let g':=g ∘ (plane i s).anon n; rw [show reflFields i s (simultaneous g x) = simultaneous g' (reflFields i s x) from Prod.ext (van ..) (van ..), p]; exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare i s n g)) (h.allV _).sector

def Singlet (f : Family K) := ∀ᶠ m in atTop, K.takes m → covariant (f m)
lemma singlet_add {f g : Family K} (h : Singlet f) (k : Singlet g) : Singlet (f+g) := by
 filter_upwards [h,k] with m p t u g x; simp_rw [Pi.add_apply,p u g x, t u g x, map_add]
lemma singlet_mul {f g : Family K} (h : Singlet f) (k : Singlet g) : Singlet (f*g) := by
 filter_upwards [h,k] with m p t u g x; simp_rw [Pi.mul_apply,p u g x, t u g x, map_mul]
lemma singlet_smul {f : Family K} (v : Singlet f) (a : ℂ) : Singlet (a • f) := by
 filter_upwards [v] with m v u g x; simp_rw [Pi.smul_apply,v u g x,twist_scalar]
lemma singlet_zero : Singlet (0:Family K) := Eventually.of_forall fun _ _ _ _=> (map_zero _).symm
lemma singlet_identity : Singlet (1:Family K) := Eventually.of_forall fun _ _ _ _=> (map_one _).symm
lemma singlet_reflected (f : Family K) (p : InTest K wide S b f) (x : Singlet f) : Singlet (thetaK K f) := x.mono (fun m h v=> covariant_reflected (p.support m) (h v) _ 3)
end YM.CF.Buffered
