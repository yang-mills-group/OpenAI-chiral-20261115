import YM.SU5.MacroSix.Pocket
import YM.SU5.FiniteGaugeData.Tapestry.Sandwich

/-! # Reflection of the endpoint account including conjugating the true Link pair coefficients

Reflection on each of the four axes, any cover height. (We check physical geometry &
use of the REG interface separately in the Spine.) Proof adapts
Tapestry/Sandwich's bounceEligible calculation. -/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Pockets
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure
  Next.SectorChange Common Fock Satin Tapestry Haro Tap Cascade Dial Mir Girt Nacre Pastry Phase RP
attribute [local instance] opCStarAlgebra
open Reed (Fine)
variable {K : Calibration}{S U V : Finset Cover}{b : Bool}{f : Family K}
variable (s : ℤ) (ai : Axis)
local notation "Y" => bounce K s ai
local notation "C" X:max => negativeSide X s ai

private lemma opposite_spin : twist (pinLift ai) (cutM plusHalf) = cutM plusHalfᶜ := by
 rw [dim_cut, raising,Fir.Adef.symm]; exact angleX (mirrorX ai) true
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (creation K x i b) = -Complex.I • ∑ j, star (Mir.pin ai j i) • removal K ((plane ai s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold bounce reflMark creation removal
 rw [(flips_basisC ai s (K.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (removal K x i b) = Complex.I • ∑ j, Mir.pin ai j i • creation K ((plane ai s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold bounce reflMark creation removal
 rw [(flips_basisC ai s (K.c m) x i b).2]; simp only [map_sum,map_smul]
lemma turns_seed (f : PairsC → ℂ) (p : Coeff true S f) :
    ∃ f' : PairsC → ℂ, Coeff true (negativeSide S s ai) f' ∧ Y (scalar K f)=scalar K f' := by
  let F := moveC ai s; let g (x : PairsC) := star (f (F x.1,F x.2))
  refine ⟨g,⟨fun _ ↦ by contradiction,Girt.pole_w _ star continuous_star
    (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),
    fun x y a b↦ congrArg star (p.locus _ _ (moved_agree _ _ a) (moved_agree _ _ b))⟩,?_⟩
  funext N x; unfold scalar bounce reflMark
  rw [theta_smul, theta_one]
  apply congrArg (fun z : ℂ ↦ z • 1); unfold g
  simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl

lemma turns_living (h : f ∈ living K b S) : Y f∈ dying K b (negativeSide S s ai) := by
  let V := dying K b (negativeSide S s ai)
  refine Submodule.span_induction (p:=fun f _ ↦ Y f∈ V) ?_
    (by rw [show Y 0=0 from funext fun _ ↦ funext fun _ ↦ theta_zero _]; exact V.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [bounce_plus]; exact V.add_mem p q)
    (fun a _ _ h ↦ by rw [bounce_scale]; exact V.smul_mem _ h) h
  rintro _ ⟨x,i,p,u,v,e,rfl⟩
  rw [reflected_creation_eq]; refine V.smul_mem _ (V.sum_mem (fun j _ ↦ ?_))
  by_cases w : j∉plusHalf
  · exact V.smul_mem _ (dying_letter _ _ _ _ w (mem_image.mpr ⟨_,v,Shape.mote ..⟩) e)
  rw [show Mir.pin ai j i=0 from Fine.entry (opposite_spin ai) u (by simpa using not_not.mp w),
      star_zero,zero_smul]; exact V.zero_mem

lemma turns_dying (h : f ∈ dying K b S) : Y f ∈ living K b (negativeSide S s ai) := by
  let V := living K b (negativeSide S s ai)
  refine Submodule.span_induction (p:=fun f _ ↦ Y f∈ V) ?_
    (by rw [show Y 0=0 from funext fun _ ↦ funext fun _ ↦ theta_zero _]; exact V.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [bounce_plus]; exact V.add_mem p q)
    (fun a _ _ h ↦ by rw [bounce_scale]; exact V.smul_mem _ h) h
  rintro _ ⟨x,i,p,u,v,e,rfl⟩
  rw [reflected_removal_eq]; refine V.smul_mem _ (V.sum_mem (fun j _ ↦ ?_))
  by_cases w : j∈plusHalf
  · exact V.smul_mem _ (living_letter _ _ _ _ w (mem_image.mpr ⟨_,v,Shape.mote ..⟩) e)
  have he : twist (pinLift ai) (cutM plusHalfᶜ)=cutM plusHalf:= by
    rw [dim_cut,map_sub,map_one,opposite_spin,dim_cut]; abel
  rw [show Mir.pin ai j i=0 from Fine.entry he (mem_compl.mpr u) w, zero_smul]; exact V.zero_mem

lemma turns_stamp (h : f ∈ stamp K b U V) : Y f ∈ stamp K b (C V) (C U) := by
  let T := stamp K b (C V) (C U)
  refine Submodule.span_induction (p:=fun f _ ↦ Y f∈ T) ?_
    (by rw [show Y 0=0 from funext fun _ ↦ funext fun _ ↦ theta_zero _]; exact T.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [bounce_plus]; exact T.add_mem p q)
    (fun a _ _ h ↦ by rw [bounce_scale]; exact T.smul_mem _ h) h
  rintro _ ⟨x,h,y,t,rfl|rfl⟩
  · rw [bounce_times]; exact stamp_rl (turns_dying s ai t) (turns_living s ai h)
  rw [bounce_times]; exact stamp_lr (turns_dying s ai t) (turns_living s ai h)

lemma turns_ribbon (h : f∈ ribbon K S b U V) : Y f ∈ ribbon K (C S) b (C V) (C U) := by
  let T := ribbon K (C S) b (C V) (C U)
  refine Submodule.span_induction (p:=fun f _ ↦ Y f∈ T) ?_
    (by rw [show Y 0=0 from funext fun _ ↦ funext fun _ ↦ theta_zero _]; exact T.zero_mem)
    (fun _ _ _ _ p q ↦ by rw [bounce_plus]; exact T.add_mem p q)
    (fun a _ _ h ↦ by rw [bounce_scale]; exact T.smul_mem _ h) h
  rintro _ ⟨x,h,y,q,rfl⟩
  obtain ⟨y',p,e⟩ := turns_seed (K:=K) s ai y q
  rw [bounce_times,e]; exact mixed_ribbon (turns_stamp s ai h) p
end YM.CF.Buffered.Afterglow.Pockets
#print axioms YM.CF.Buffered.Afterglow.Pockets.turns_ribbon
