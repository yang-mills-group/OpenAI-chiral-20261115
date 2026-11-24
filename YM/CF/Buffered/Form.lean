import YM.CF.Buffered.Size

/-!
# The buffered limiting form on the paired, actual histories

Any prescribed iterated joint choice of limits as in ms corollary.
No convergence or existence of the limits assumed *at all* as m,n→∞
along the product order/unenlarged cone. `Settled` means the hypotheses of
taking them: first at each fixed, sufficiently large member m of the given
sequence, then along those m; For simplicity intermediate values needed
ONLY there. Can even allow period-wise UV subsequence in the continuous
version. In the Borel system specialize to joint-E sequences (record also
taking the joint convergence for those sequences; not needed to prove PSD,
just its iteration part used). No estimates of total boundedness in this
proof; no claim that the limits exist outside the assumptions of corollary.

State the finite-list positive semidefinite inequality on that expectation,
in addition to the nonnegative / Hermitian form theorem. Same
expectation E including centered mark applications later. E leaves all
unqualified arguments underspecified. No positivity/linearity assumptions
on E as such! Derive them (on their respective domains).
-/
set_option autoImplicit false
set_option maxHeartbeats 470000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
attribute [local instance] opCStarAlgebra
variable (K : Calibration) (P : Histories K)
structure Process (K : Calibration) where
  m : ℕ → Side
  sides : ∀ r, K.takes (m r)
  grows : Tendsto m atTop atTop
  n : ℕ→ℕ→ℕ -- all read on that period use same subsequence
  grows_n : ∀ r,Tendsto (n r) atTop atTop
variable (C : Process K)
namespace Process
variable {K}
def atUV (r j : ℕ) (f : Family K) : ℂ := P.cap (C.n r j) (f (C.m r))
-- n_k even when using the same k across periods is chosen in the relevant history (choice common within holds).
lemma cap_add {f g : Family K} {wide : Bool} (p : TestFamily K wide f) (q : TestFamily K wide g) (m : ℕ) : ∀ᶠ i in atTop, C.atUV P m i (f+g)=C.atUV P m i f+C.atUV P m i g := by
  filter_upwards [P.eventuallyPaid (C.n m) (C.grows_n m) (C.sides m)] with k w
  obtain ⟨x,t⟩:=p.paid; obtain ⟨X,v⟩:= q.paid
  unfold atUV Histories.cap atZero; rw [Pi.add_apply, mark_add w.loom (t.support ..).env (v.support ..).env w.pay',add_div]
lemma cap_scale (a : ℂ) (f : Family K) (m i : ℕ) : C.atUV P m i (a • f)=a*C.atUV P m i f := by unfold atUV Histories.cap atZero; rw [Pi.smul_apply,mark_smul,mul_div_assoc]
lemma cap_one (m : ℕ) : ∀ᶠ i in atTop,C.atUV P m i 1=1 := by
 filter_upwards [P.divisions (C.n m) (C.grows_n m) (C.sides m)] with i hp; unfold atUV Histories.cap atZero; rw [Pi.one_apply,markvac]; exact div_self hp.1
end Process
variable {K}
def Iterated (f : Family K) (z : ℂ) := ∃ l : ℕ→ℂ, (∀ᶠ r : ℕ in atTop,Tendsto (fun j=> C.atUV P r j f) atTop (𝓝 (l r))) ∧ Tendsto l atTop (𝓝 z)
structure Settled (wide : Bool) (E : Family K → ℂ) : Prop where
  convergence (f : Family K) (h : TestFamily K wide f) : Iterated P C f (E f)
  joint (p : wide=true) : ∃ n : ℕ → ℕ, C.n=(fun _=> n) ∧ ∀ f: Family K, TestFamily K wide f → ∀ k:ℕ→ℕ,
    (∀ᶠ r in atTop, (C.m r).val^5 ≤ n (k r)) → Tendsto (fun r=> C.atUV P r (k r) f) atTop (𝓝 (E f))
namespace Iterated
variable {P C} {z w : ℂ} {f g : Family K} {wide : Bool}
lemma uniq (e : Iterated P C f z) (h : Iterated P C f w) : z=w := tendsto_nhds_unique_of_eventuallyEq e.choose_spec.2 h.choose_spec.2 ((e.choose_spec.1.and h.choose_spec.1).mono fun _ p=>tendsto_nhds_unique p.1 p.2)
lemma more (a : TestFamily K wide f) (b : TestFamily K wide g) (p : Iterated P C f z) (e : Iterated P C g w) : Iterated P C (f+g) (z+w) := by
 obtain ⟨l,p,h⟩:=p; obtain ⟨k,u,g'⟩:=e; exact ⟨fun i=>l i+k i,(p.and u).mono (fun i x=> (x.1.add x.2).congr' (((C.cap_add P a b i)).mono fun i h=> h.symm)),h.add g'⟩
lemma times (p : Iterated P C f z) (a : ℂ) : Iterated P C (a • f) (a*z) := by
 obtain ⟨l,p,h⟩:=p; exact ⟨fun i=>a*l i,p.mono (fun i h=> (h.const_mul a).congr' (Eventually.of_forall fun j=> (C.cap_scale P a f i j).symm)),h.const_mul a⟩
lemma identity : Iterated P C 1 1 := ⟨fun _=>1,Eventually.of_forall (fun i=> tendsto_const_nhds.congr' ((C.cap_one P i).mono fun _ p=> p.symm)),tendsto_const_nhds⟩
end Iterated
-- limiting Gram on the generated Family
variable {wide : Bool}
namespace Settled
variable {P C} {E : Family K→ℂ} (h : Settled P C wide E)
include h
lemma value : E 1=1 := (h.convergence _ TestFamily.oneT).uniq Iterated.identity
lemma add {f g} (p : TestFamily K wide f) (t : TestFamily K wide g) : E (f+g)=E f+E g :=
  (h.convergence _ (p.add t)).uniq ((h.convergence _ p).more p t (h.convergence _ t))
lemma smul {f} (a : ℂ) (p : TestFamily K wide f) : E (a • f)=a*E f := (h.convergence _ (p.scale a)).uniq ((h.convergence _ p).times a)
lemma gram {f} (p : Eligible K wide f) : 0 ≤ E (thetaK K f*f) := by
 obtain ⟨l,t,u⟩:= h.convergence (thetaK K f*f) (p.forget.ref.mul p.forget)
 apply ge_of_tendsto u; filter_upwards [C.grows.eventually p.fits_time,t] with m w e
 exact P.uvSign (C.n m) (C.grows_n m) (C.sides m) w e
include h
local notation "S" => eligible K wide
def cross (E : Family K→ℂ) {wide : Bool} (f g : eligible K wide) := E (thetaK K f.val*g.val)
local notation "reading" => cross E
-- into ℂ, Domain is submodule of all test declarations, not ambient unbuffered CAR.
lemma lin₂ (f g k : eligible K wide) : reading f (g+k)=reading f g+reading f k := by unfold cross; rw [AddSubmonoid.coe_add,mul_add]; exact h.add ((Eligible.forget f.property).ref.mul (Eligible.forget g.property)) ((Eligible.forget f.property).ref.mul (Eligible.forget k.property))
lemma lin₁ (f g k : eligible K wide) : reading (f+g) k=reading f k+reading g k := by unfold cross thetaK; rw [AddSubmonoid.coe_add, ref_plus,add_mul]; exact h.add ((Eligible.forget f.property).ref.mul (Eligible.forget k.property)) ((Eligible.forget g.property).ref.mul (Eligible.forget k.property))
lemma scale₂ (f g : eligible K wide) (a : ℂ) : reading f (a•g)=a*reading f g := by unfold cross; rw [Submodule.coe_smul,Algebra.mul_smul_comm]; exact h.smul _ ((Eligible.forget f.property).ref.mul (Eligible.forget g.property))
lemma scale₁ (f g : eligible K wide) (a : ℂ) : reading (a•f) g=star a*reading f g := by unfold cross thetaK; rw [Submodule.coe_smul, ref_scale,Algebra.smul_mul_assoc]; exact h.smul _ ((Eligible.forget f.property).ref.mul (Eligible.forget g.property))

def form : eligible K wide →ₗ⋆[ℂ] (eligible K wide →ₗ[ℂ] ℂ) where
 toFun f:= ⟨⟨fun g=> reading f g,fun g k=>h.lin₂ f g k⟩,fun a g=>h.scale₂ f g a⟩
 map_add' f g:= LinearMap.ext fun k=>h.lin₁ f g k
 map_smul' a f:= LinearMap.ext fun g=>h.scale₁ f g a
lemma form_diagonal (f : eligible K wide) : 0 ≤ h.form f f := h.gram f.property
lemma herm (f g : eligible K wide) : star (h.form g f)=h.form f g := by
 -- as in ReflectTest, get hermitian only from the limit proof of positivity
 have x(f : eligible K wide) : (reading f f).im=0:= ((Complex.le_def.mp (h.gram f.property)).2).symm
 have ht:=x f; have hg:=x g; have h₁:=x (f+g); have h₂:=x (f+Complex.I • g)
 rw [h.lin₁,h.lin₂,h.lin₂] at h₁ h₂; rw [h.scale₁,h.scale₁,h.scale₂,h.scale₂] at h₂
 simp [ht,hg,Complex.mul_re,Complex.mul_im] at h₁ h₂; change star (reading g f)=reading f g; apply Complex.ext <;> simp <;> linarith
end Settled
namespace Corollary
variable {E : Family K → ℂ} (h : Settled P C wide E)
lemma form (f g : eligible K wide) : h.form f g=E (thetaK K f.val*g.val) := rfl
/-- The actual normalized limiting form on the specified sharp history. -/
theorem positive : E 1 = 1 ∧ (∀ f g:eligible K wide, star (h.form g f)=h.form f g) ∧ ∀ f:eligible K wide, 0 ≤ E (thetaK K f.val*f.val) := ⟨h.value,h.herm,fun f=>h.gram f.property⟩
include h
/-- Explicit Gram version: can test ANY finite list from the class with its admitted
cutoff limit then period limit. -/
theorem matrix {I : Type*} (F : I → eligible K wide) [Fintype I] :
    (Matrix.of (fun i j=> E (thetaK K (F i).val*(F j).val))).PosSemidef := by
 apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr; constructor
 · ext i j; exact h.herm _ _
 intro x; have he := h.form_diagonal (∑ j,x j • F j)
 rw [map_sum h.form,LinearMap.sum_apply] at he; simp_rw [map_sum,map_smulₛₗ (f:=h.form)] at he -- argument
 change 0 ≤ ∑ i, star (x i)*∑ j, h.form (F i) (F j)*x j
 simpa only [smul_eq_mul,starRingEnd_apply,map_smulₛₗ,LinearMap.smul_apply, RingHom.id_apply,Finset.mul_sum, mul_assoc,mul_comm,mul_left_comm] using he
end Corollary
end YM.CF.Buffered
#print axioms YM.CF.Buffered.Corollary.positive
#print axioms YM.CF.Buffered.Corollary.matrix
