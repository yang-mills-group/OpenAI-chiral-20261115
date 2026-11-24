import YM.CF.Char.Story
import YM.CF.Reef.Aqua
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
open AnalyticBridge.GaussianFieldAlignment Orthogonal Tensor PhysicalNext.OrderedAffine2B.SymRows
open Locations Gauges Channels AnalyticNext.QuarticMatch
section
open Reef
local notation "D"=> SU.group
variable {n:Side}(T:Tube SU.group S)(A:Stores S)(F:Forest S.ratio)(x:ℝ)(V:Config SU.group c)(k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray SU.group (Frozen A x F))
def shiftF (α:Type):ColorOrtho SU.group α:=fun _=>frolic
private abbrev fCL:Ox≃L[ℝ]Ox:=Tensor.ortho (shiftF Unit) ()
private lemma sumW {ι:Type*}(f:ι→Ox): fCL (∑' i,f i) = ∑' i,fCL (f i):=fCL.map_tsum
lemma reel (p: PathData SU.group)(U:Config SU.group f)(i: Cell f): p.ell (Reef.echo U) i=frolic (p.ell U i):=by
 unfold PathData.ell; change _= fCL _; rw [sumW]; apply tsum_congr; intro j; unfold PathData.ellTerms; rw [Reef.tollSlot, map_smul]; rfl
lemma clip_reel(h: Reef.Rare T.up)(U:Config SU.group f): mainTerm T.high (grainA T.up r) (Reef.echo U)=mainTerm T.high (grainA T.up r) U:=by
 let B:=grainA T.up r; have he(U:Config SU.group f): quadratic T.high B (Reef.echo U)=quadratic T.high B U:=by simp only [quadratic,faceValue,Reef.echo_t, cold,reel,frolic.norm_map]
 have hx{k:ℕ}(A:Atom SU.group k)(h:Reef.Prist A): Reef.Prist (if A.length ≤ r then A else dimA A):=by split; exact h; intro i; simp [dimA,Atom.poly]
 change mainTerm _ B _=mainTerm _ B _; unfold mainTerm; simp_rw [Reef.echo_p, he, echo_uncut B.cubic (fun i=> hx _ (h i).2.1), echo_uncut B.quartic (fun i=> hx _ (h i).2.2)]
lemma repE : replica S.ratio (Reef.echo V)=Reef.echo (replica S.ratio V):=by funext i; dsimp only [replica,Reef.echo]; split; exact (map_one qG).symm; rfl
lemma inc_re (a: Directions SU.group n)(U:Config SU.group n): increment (Reef.echo U) (Tensor.lifting (shiftF _) (Equiv.refl _) a)=Reef.echo (increment U a):=by funext i; change _ * _ = _; unfold Reef.echo increment; rw [map_mul]; exact congrArg (·*qG (U i)) (Reef.cool_a _)
lemma chartE(g:SU.group.El): qG g∈firstChart D ↔ g∈ firstChart D:=by
 have he(g:SU.group.El)(h:g∈firstChart D): qG g∈firstChart D := by obtain ⟨u,hu,rfl⟩:= h; exact ⟨frolic u, by simpa [firstBall] using hu,cool_a u⟩
 exact ⟨fun h=> q0 g ▸ he _ h,he _⟩
lemma patchE(z:SU.group.El): patched q d (qG z)=frolic (patched q d z):=by
 by_cases h:z∈firstChart D
 · obtain ⟨u,hu,rfl⟩:= h; have ht: frolic u∈firstBall D:= by simpa [firstBall] using hu
   rw [←cool_a]; unfold patched firstChart; rw [indicator_of_mem (mem_image_of_mem _ ht), indicator_of_mem (mem_image_of_mem _ hu)]
   change broad _ _ _ • _=frolic (broad _ _ _ • _); rw [over_ball hu,over_ball ht,map_smul]; simp only [broad,frolic.norm_map]
 rw [patched,indicator_of_notMem (mt (chartE _).mp h),patched,indicator_of_notMem h,map_zero]
lemma rollW (o:Signed) (a:Directions SU.group f): facade S o (Reef.echo V) (Tensor.lifting (shiftF _) (Equiv.refl _) a)=Reef.echo (facade S o V a):=by rw [facade,repE,inc_re,Reef.echo_p,facade]
lemma roll0(o:Signed): facade S o (Reef.echo V) 0=Reef.echo (facade S o V 0):= by simpa using! rollW (S:=S) V o 0
lemma barE (P: PathData SU.group)(U:Config SU.group n)(a:LogArray SU.group (Cell n))(i:Cell n)(r:ℕ): barrel P r (Reef.echo U) (fun i=>frolic (a i)) i=frolic (barrel P r U a i):=by
 unfold barrel; change _= fCL _; rw [sumW]; apply tsum_congr; intro i; dsimp only; split
 · rw [echo_t,map_smul]; exact congr_arg _ (dip ..).symm
 rw [map_zero]
lemma rolledb(o:Signed)(a:Directions SU.group f)(i:Cell f):plaquetteJet S (Reef.echo V) o i (Tensor.lifting (shiftF _) (Equiv.refl _) a)=frolic (plaquetteJet S V o i a):=by
 unfold plaquetteJet; refine derives _ fCL (fun a=>?_) a; rw [rollW,faceValue,echo_t]; exact swing _
lemma revolt(o:Signed)(a:Directions SU.group f)(i:Bond c)(hs:S.patch.Branches S.kernel SU.group): blockJet (Reef.echo V) k o i (Tensor.lifting (shiftF _) (Equiv.refl _) a)= frolic (blockJet V k o i a):=by
 unfold blockJet; refine derives _ fCL (fun a=>?_) a
 unfold predictorTurn predictGroup; rw [rollW,roll0,(proceeds hs _ _).1, (proceeds hs _ _).1]; change SU.group.curvature (qG _*(qG _)⁻¹) = _; rw [← map_inv, ← map_mul]; exact swing _
lemma brandE(h:S.patch.Branches S.kernel SU.group)(u:Directions SU.group f)(i:Slots S): Rows.bump T x (Reef.echo V) k (Tensor.lifting (shiftF _) (Equiv.refl _) u) i =frolic (Rows.bump T x V k u i):=by
 obtain ⟨s,i|i⟩:=i
 · unfold Rows.bump; dsimp only [Sum.elim_inl,Rows.faceKick]; simp_rw [roll0,rolledb]; split; exact barE ..; rw [map_smul]
 change -(Real.sqrt S.kernel.penalty • (_ : Ox)) =frolic (-(_ • _)); rw [revolt _ _ _ _ _ h,map_neg, map_smul]
end
end YM.CF.Char
