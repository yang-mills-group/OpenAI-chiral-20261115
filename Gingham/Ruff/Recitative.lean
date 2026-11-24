import Gingham.Ruff.Coronet
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Infinitesimal
import YM.CF.Thera.Jolt
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open AnalyticBridge.CouplingShape ProjectorNext.Equivariance

def bothway (u: SU.group.El)(x:Doub N) : Doub N:=
  (globalAd u x.1,globalAd u x.2)
lemma overall_pencil (u : SU.group.El) (x : Doub N) (s ρ : ℝ) :
    pencil ρ (s • bothway u x)= gauge (fun _=>u) (pencil ρ (s • x)) := by
  funext i
  simp only [pencil, Prod.smul_fst,Prod.smul_snd, Pi.smul_apply, Lattice.gauge,bothway,globalAd,←map_smul]
  rw [exp_adjoint,exp_adjoint]
  group

open Peaks

private lemma perlam(N:Side) (L:tangD N →ₗ[ℝ] ℝ)
    (z:∀ (u:SU.group.El) (x:tangD N), L (globalAd u x)=L x) (a:tangD N) :
    L a = 0:=by
  rw [← Finset.univ_sum_single a,map_sum]
  refine sum_eq_zero fun i _=>?_
  let v:= L ∘ₗ LinearMap.single ℝ (fun _ : Edge (Seat N) => SU.group.Color) i
  have hv : Maxwell.Free.irreduc (G:=SU.group) v := fun u x=>by
    change L (Pi.single i (SU.group.adjoint u x)) = L (Pi.single i x)
    nth_rw 2 [← z u]
    congr 1
    ext1 j;by_cases h:j=i
    · subst j; simp [globalAd]
    simp [globalAd,h]
  change v (a i)=_
  rw [Maxwell.Free.singles_inv Thera.yet_one v hv]; rfl


lemma both_screen(L:Doub N →ₗ[ℝ] ℂ) 
    (z:∀ (u:SU.group.El) (x:Doub N),L (bothway u x)=L x)
    (x:Doub N): L x=0:=by
 have h0(u:SU.group.El) :globalAd u (0:tangD N)= 0:= by ext; simp [globalAd]
 suffices s:∀ f:ℂ →ₗ[ℝ] ℝ, f (L x)=0 by
   exact Complex.ext (s Complex.reLm) (s Complex.imLm)
 intro f
 have hx:=perlam N (f ∘ₗ L ∘ₗ LinearMap.inl _ _ _) ?_ x.1
 have hy:=perlam N (f ∘ₗ L ∘ₗ LinearMap.inr _ _ _) ?_ x.2
 change f (L (x.1,0)) = 0 at hx
 change f (L (0,x.2)) = 0 at hy
 rw [show x=(x.1,0)+(0,x.2) from (Prod.ext (add_zero _) (zero_add _)).symm, map_add,map_add,hx,hy,zero_add]
 · intro u a; change f (L (0,_))=_; exact congrArg f (by simpa [bothway,h0] using (z u (0,a)))
 intro u a; change f (L (_,0))=_; exact congrArg f (by simpa [bothway,h0] using (z u (a,0)))


/-- G.Simple kills both kinds of tangents even on the wrapped torus. -/
lemma off_key(F:Doub N→ℂ)
   (hx: DifferentiableAt ℝ F 0)
   (z:∀ (u:SU.group.El)(x:Doub N)(s:ℝ),‖s • x‖<1→‖s • bothway u x‖<1→
      F (s • bothway u x)=F (s • x)): fderiv ℝ F 0=0:=by
 have q(x:Doub N): ∀ᶠ s:ℝ in 𝓝 0,‖s • x‖<1 :=
    (((show Continuous (fun i:ℝ=>i • x) from continuous_id.smul continuous_const)).norm.tendsto 0).eventually (gt_mem_nhds (by simp))
 refine ContinuousLinearMap.ext fun w=>?_
 apply both_screen (fderiv ℝ F 0).toLinearMap _ w
 intro u x
 refine ((Push.side F hx (bothway u x)).congr_of_eventuallyEq ?_).unique (Push.side F hx x)
 filter_upwards [q x,q (bothway u x)] with i h k using (z u x i h k).symm

#print axioms off_key

