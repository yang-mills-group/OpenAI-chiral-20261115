import YM.CF.Continuum.Algebra
/-! # A gauge probe and general scalar evaluation -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Function Finset Lattice Wilson SU Fock Lat Cube Mir Mir.Trip Phase RP Spire Scroll Tulip Reed Reflect Tenant
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 4096
variable {m B N : Side}

def bosonic (N : Side) (f : Bkg (More N) → ℂ) : Evaluation N := fun x=> f x • 1
lemma bosonic_local (f : Bkg (More N)→ ℂ) (h : Continuous f) (U : Finset (Edges (More N)))
    (hf : ∀ (x y : Bkg (More N)), (∀ i∈U,x i = y i) → f x = f y) (g : GaugeInvariant f) :
    bosonic N f ∈ localObs N U ∅ :=
  ⟨h.smul continuous_const, fun x y p=>by rw [bosonic,bosonic,hf x y p],
   fun _=>Fine.one.scale _, fun u x=>by rw [bosonic,bosonic,g u x,twist_scalar,map_one]⟩
lemma dagger_boson (f : Bkg (More N)→ℂ) (i : Axis) :
    dagger N i (bosonic N f)=bosonic N (star ∘ f) := by
  funext x; unfold dagger bosonic Function.comp; rw [theta_smul,theta_one]

def loopRead (N : Side) (p : Face (Per (More N))) : Evaluation N :=
  bosonic N fun x => (SU.group.chord (faceValue x p)^2 : ℝ)

def loopSupport {N : Side} (p : Face (Per N)) :=
  Tenant.leaks ((visits p.1 (square p.2.val.1 p.2.val.2)).toFinset)

lemma loop_local (p : Face (Per (More N))) : loopRead N p ∈ localObs N (loopSupport p) ∅ := by
  apply bosonic_local
  · exact Complex.continuous_ofReal.comp ((SU.group.continuous_chord.comp (by unfold faceValue; fun_prop)).pow 2)
  · intro x y h; rw [show faceValue x p = faceValue y p from (travel_local p.1 (square p.2.val.1 p.2.val.2) x y (fun e he hh=>h e (mem_filter.mpr ⟨mem_univ _,List.mem_toFinset.mpr he, List.mem_toFinset.mpr hh⟩)))]
  intro t U; simp [SU.group.chord_conj]
lemma loop_dagger (p : Face (Per (More N))) (i : Axis) : dagger N i (loopRead _ p)=loopRead N p := by
  unfold loopRead; rw [dagger_boson]; congr; ext x; simp
lemma loop_flip (p : Face (Per (Domain m B))) (i : Axis) :
    flipTime m B i (loopRead (CSide m B) p) =
      loopRead (CSide m B) (p.send (Signed.mirror i) 0) := by
  funext x; unfold flipTime; rw [mirrorPane_eq]; unfold loopRead bosonic; dsimp only
  rw [Face.send_price _ _ _ _ SU.group.chord SU.group.chord_inv (fun i k=>SU.group.chord_conj k i),theta_smul,theta_one]; simp

end YM.CF.Window
