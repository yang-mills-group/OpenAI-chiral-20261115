import YM.CF.BProof.Law.Product
import YM.CF.BProof.Angular.Janitor

/- Gap law on the torus, flat slice only. Overwrite normals with constants (rest use Haar).
Tag rotation may depend on gauge conditioned on normals; the final integrations are usual
bounded Borel tests on the common product measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular
open Function Lattice Gauge SU MeasureTheory Wilson Finset Law RG
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
local notation "G" => SU.group
namespace Yard
variable {A F: Type*}[MeasurableSpace A] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F][CompleteSpace F]
variable {s: Side}(Y:Yard s)(μ:Measure A)[IsProbabilityMeasure μ]

def Flat (U:Config G s) := Set.EqOn U 1 ↑Y.trunks
def squash := Law.patch (B:=SU.group.El) Y.trunks 1
lemma squash_c : Measurable Y.squash := (Law.patch_m (B:=SU.group.El) _).comp (f:=fun U:Config G s=> ((1:Config G s),U)) (by fun_prop)
lemma squash_flat (U:Config G s) : Y.Flat (Y.squash U):= patch_on ..
lemma flat_identity {U:Config G s}(h:Y.Flat U): Y.squash U=U:=by ext1 p; unfold squash Law.patch; split; rename_i he; exact (h he).symm; exact rfl

lemma gauge_pres (t:Site s→ E): MeasurePreserving (Lattice.gauge t : Config G s→ Config G s) (prior G s) (prior G s) := by
 apply measurePreserving_pi (α:=fun _ : Bond s=>SU.group.El) _ _ (f:=fun i u=>t i.1 *u*(t (i.1+ Lattice.step i.2))⁻¹)
 intro i; exact (measurePreserving_mul_right group.probHaar _).comp (measurePreserving_mul_left group.probHaar _)

/-- integrated gauge-invariance of the given entire mark. A lemma allowing use of
conditional representation and sum after Tag law. -/
lemma sweep_out (F: Config G s × A→F)(h:Envelope F)
    (τ:∀ t,Y.Frozen t→ ∀ U:Config G s,(∫ x,F (U,x) ∂μ)=∫ x,F (Lattice.gauge t U,x) ∂μ):
    (∫ X,F X ∂((prior G s).prod μ))=∫ W, ∫ x,F (Y.squash W,x) ∂μ ∂prior G s:=by
 let f(U:Config G s):=∫ x,F (U,x) ∂μ; have hf: Envelope f:=fund μ h
 rw [integral_prod F (Law.pay h)]
 change (∫ x,f x ∂Measure.pi (fun _ : Bond s=>SU.group.probHaar)) = _
 rw [Law.refresh (μ:=fun _:Bond s=> SU.group.probHaar) Y.trunks hf] -- may not match
 let q:=f ∘ Y.squash; have hg:Envelope q:=Law.pull hf Y.squash_c
 change (∫ A, ∫ V,f (Law.patch Y.trunks A V) ∂prior G s ∂prior G s) = ∫ V,q V ∂prior G s
 have H (A: Config G s): (∫ V,f (Law.patch Y.trunks A V) ∂prior G s) = ∫ V,q V ∂prior G s := by
   obtain ⟨t,e₁,e⟩:= Y.existsJanitor fun i=> A i
   let J:Config G s→Config G s:=Law.patch Y.trunks A
   have he(U:Config G s) : Lattice.gauge t (J U) = Y.squash (Lattice.gauge t U):=by
      ext1 p; by_cases h:p∈Y.trunks
      · exact (e _ (fun b h=> patch_on (B:=SU.group.El) Y.trunks A U h) h).trans (Y.squash_flat _ h).symm
      simp only [squash,J,Lattice.gauge,Law.patch,if_neg h]
   have hx(V) : f (Law.patch Y.trunks A V)= q (Lattice.gauge t V):=by
      change f (J V)=_; rw [show f (J V)=f (Lattice.gauge t (J V)) from τ t e₁ _,he]; rfl
   simp_rw [hx]; exact apply_pres (gauge_pres t) hg.meas
 simp_rw [H]; simp
end Yard
end YM.CF.BProof.Angular
