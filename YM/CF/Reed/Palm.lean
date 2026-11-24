import YM.CF.Reed.Play
import YM.CF.Reed.Point

/-! # A result at cutoff (not a continuum existence theorem)

Volume-independent construction of chiral measures & reflection positive
finite-time regulators. Read `Reed.Finite` for common witness quantifiers.
All hypercubic tori of sizes in the scaling rule. See `Ave.Warranty` for
payroll and extensive log estimates. `supports` are paid in tiles/valid joint
fields, no estimate here on a running lattice with B itself tending to infinity.
Does not assert uniqueness/granularity of the regulator coefficients in m.
The flow for lens is in log increment *before* projecting to a variable frame,
not a statement of differentiability of the phase in link charts. None of these
results bound continuum fermion spectra.

The construction uses a pairing law and local phases,
with semigroup RP and no auxiliary singlets. No analytic input
assumed from those suggestions. Imports matrix/lattice/Wilson basics from YM.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Reed
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect Pastry RP Ave Delta
attribute [local instance] opCStarAlgebra
variable {B : Side} {β e k p K σ L : ℝ} {c : Room B e}
structure Cutoff (R : Reg β e B) (p K k L σ : ℝ) (c : Room B e) : Prop where
  bond : Warranty B e β k σ c K R
  transport (m : Side) : ∃ F w, Delta.Flow m B e p k L (R.c m) F w
  effective (m : Side) (U : Briar m B e) : (frame matter (links U.val) (R.c m)).overlap*lens m B (R.c m) U.val=cutM (upperP (CSide m B))*lens m B (R.c m) U.val
  kineticB (m : Side) (U : Briar m B e) (V : UNI (Elf m B)) (T : Finset (Elf m B)) (k:lens m B (R.c m) U.val=twist V (cutM T)) : let W:= (frame matter (links U.val) (R.c m)).overlap; chemical (n:=Elf m B) (W*V.val) (upperP _) T=chemical V.val (upperP _) T
  bareF (m : Side) (x : Briar m B e) (v : UNI (Elf m B)) (S : Finset (Elf m B)) (h : lens m B (R.c m) x.val=twist v (cutM S)) : ∃ z:ℂ, ‖z‖=1 ∧ ∀ (P:FC (Elf m B)), Plain P →
    let A := upperP (CSide m B); z*spell (syms A) v.val A S P=inner ℂ (linearB (CSide m B)) (acts ((think A).eval P) (sound m B (R.c m) x.val))
  positivity (m : Side) {f : Readers m B} {i b} (p : Region f i b) (y:Site (More m)) (n:ℕ) : 0 ≤ R.schwinger m n (squareR m B y (R.c m) i (fun x=>f x.1) b)
lemma Cutoff.awake (R : Reg β e B) (h : Warranty B e β k σ c K R) (U : ∀ m:Side,∃ F w, Delta.Flow m B e p k L (R.c m) F w) : Cutoff R p K k L σ c := by
  exact ⟨h,U,fun _ x=> kinetic x.property c _,fun m U v T t=> quotient_kin (x:=U) _ c v T _ t rfl,fun m x v S u=> chiral _ c x v S u, fun _ {_ _ _} h_ => rPos h_ R h.passesP⟩
lemma Finite (k : ℝ) (h : 0<k) : ∃ σ:ℝ,0<σ∧σ<1∧∃ N:ℕ,∀ B:Side,N≤B.val→∃ ε Y p K:ℝ,0<ε∧0<p∧∀ e:ℝ, 0<e→ e≤ ε→ ∃ b:Room B e,∀ β:ℝ, ∀ r:ℝ,0<r→ ∃ R:Reg β e B, 1-r<R.knob ∧ Cutoff R p Y k K σ b := by
  obtain ⟨s,p,H,y,G⟩:= Ave.major h
  obtain ⟨u,Q⟩:= Delta.flowerV k h
  refine ⟨s,p,H,u+y,fun B g=>?_⟩
  obtain ⟨v,Y,j,L⟩:= G B (by omega)
  obtain ⟨t,b,V,R⟩:= Q B (by omega)
  refine ⟨v,Y,t,b,j,V,fun e h w=>?_⟩; obtain ⟨c,A⟩:= L e h w; refine ⟨c,fun i r hr=>?_⟩; obtain ⟨Z,p,F⟩:= A i r hr; exact ⟨Z,p,Cutoff.awake Z F (fun m=>R e c m (Z.c m))⟩
end YM.CF.Reed
