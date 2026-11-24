import YM.SU5.FiniteGaugeData.Tower.Roomer
import YM.SU5.Six.CoverLetters
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin

open Six
open Reed (Fine)
variable (K':Calibration) (W:Bool) (S T D:Finset Cover) (a:Axis)(z:ℤ)
section copy
local notation "Refl"=> mirror K' a z
variable {wide b:Bool}
private lemma pair_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : ∃ g,Coeff wide (reflectedBox a z S) g ∧ Refl (scalar K' f) = scalar K' g := by
 let F := Lifted.moveC a z; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Refl (scalar K' f)=scalar K' g:= by funext m x; unfold scalar mirror reflMark; rw [Fock.theta_smul,Fock.theta_one]; apply congrArg (fun u :ℂ=> u • (1:Fock.FC (Single _))); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 refine ⟨g,⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y c d=>?_⟩,ht⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ c) (moved_agree _ _ d))
private lemma six_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Refl (creation K' x i b) = -Complex.I • ∑ j, star (Mir.pin a j i) • removal K' ((plane a z).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K'.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma six_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Refl (removal K' x i b) = Complex.I • ∑ j, Mir.pin a j i • creation K' ((plane a z).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold mirror reflMark creation removal
 rw [(flips_basisC a z (K'.c m) x i b).2]; simp only [map_sum,map_smul]
private lemma sixDualizes(a:Axis): twist (pinLift a) (Fock.cutM plusHalf)=Fock.cutM plusHalfᶜ:= by
 open Fock in rw [dim_cut,raising,Fir.Adef.symm]; exact angleX (mirrorX a) true
end copy
local notation "Θ"=>Tower.mirror K' a z
local notation "σ" D:max=>reflectedBox a z D
private lemma mirZero : Θ 0=0:=funext fun _=>funext fun _=>Fock.theta_zero _
lemma mirror_pocket (b:Bool){f:Family K'}(p:f∈SinglePocket K' W S b): Θ f∈SinglePocket K' W (σ S) !b:= by
  let R:=SinglePocket K' W (σ S) !b
  refine Submodule.span_induction (p:=fun f _=> Θ f∈R) (fun f v=>?_) ?_ ?_ ?_ p
  · obtain ⟨x,i,k,h,t,r⟩:=v
    cases b
    · rw [if_neg Bool.false_ne_true] at r
      obtain ⟨g,rfl⟩:=r
      rw [six_removal_eq]; apply R.smul_mem
      apply R.sum_mem; intro j _; by_cases e:j∈plusHalf
      · apply R.smul_mem; exact pocket_creation K' W (σ S) (mem_image.mpr ⟨_,h,Shape.mote ..⟩) t e
      have ht: twist (pinLift a) (Fock.cutM plusHalfᶜ)=Fock.cutM plusHalf:= by
        open Fock in rw [dim_cut,map_sub,map_one,sixDualizes a,dim_cut]; abel
      rw [show Mir.pin a j i=0 from Fine.entry ht (by simpa only [mem_compl] using g) e, zero_smul]
      exact R.zero_mem
    rw [if_pos rfl] at r
    obtain ⟨g,rfl⟩:=r
    rw [six_creation_eq]; apply R.smul_mem
    apply R.sum_mem; intro j _; by_cases e:j∈plusHalf
    · rw [show Mir.pin a j i=0 from Fine.entry (sixDualizes a) g (by simpa using e),star_zero,zero_smul]
      exact R.zero_mem
    apply R.smul_mem; exact pocket_removal K' W (σ S) (mem_image.mpr ⟨_,h,Shape.mote ..⟩) t e
  · rw [mirZero]; exact R.zero_mem
  · intro f g _ _ h t; rw [mirror_plus]; exact R.add_mem h t
  intro c f _ h; rw [mirror_scale]; exact R.smul_mem _ h
private lemma reorder {f g:Family K'}(p:InTest K' true S true f)(h: InTest K' true T true g):f*g=(-1:ℂ) • (g*f) := by
  funext m x
  have ht:= ((p.support m).mono (subset_univ _)).allV x
  have hv:= ((h.support m).mono (subset_univ _)).allV x
  exact ht.sign_com hv
lemma mirror_raw {f:Family K'}(p:f∈RawPair K' W S T) : Θ f∈ RawPair K' W (σ T) (σ S) := by
  let R:=RawPair K' W (σ T) (σ S)
  refine Submodule.span_induction (p:=fun f _=> Θ f∈ R) (fun f v=>?_) ?_ ?_ ?_ p
  · obtain ⟨x,q,y,h,rfl⟩:=v
    rw [mirror_times,reorder K' (σ T) (σ S) (axial K' a z (pocket_test K' W T false q).1) (axial K' a z (pocket_test K' W S true h).1)]; apply R.smul_mem
    exact Submodule.subset_span (show _∈_ from ⟨Θ y,mirror_pocket K' W S a z true h,Θ x,mirror_pocket K' W T a z false q,rfl⟩)
  · rw [mirZero]; exact R.zero_mem
  · intro f g _ _ h t; rw [mirror_plus]; exact R.add_mem h t
  intro c f _ h; rw [mirror_scale]; exact R.smul_mem _ h
lemma mirror_dressed {f:Family K'}(p:f∈DressedPair K' W S T D) : Θ f∈ DressedPair K' W (σ T) (σ S) (σ D):= by
  let R:= DressedPair K' W (σ T) (σ S) (σ D)
  refine Submodule.span_induction (p:=fun f _=>Θ f∈ R) (fun f v=>?_) ?_ ?_ ?_ p
  · obtain ⟨g,q,x,v,rfl⟩:= v; obtain ⟨g',q',h⟩:=pair_scalar K' D a z g q
    rw [mirror_times,h]; exact Submodule.subset_span (show _∈_ from ⟨g',q',_,mirror_raw K' W S T a z v,rfl⟩)
  · rw [mirZero]; exact R.zero_mem
  · intro f g _ _ h t; rw [mirror_plus]; exact R.add_mem h t
  intro c f _ h; rw [mirror_scale]; exact R.smul_mem _ h
lemma relocate_dressed {f:Family K'}(p:f∈DressedPair K' W S T D) :
    SlabMark.relocate K' a z f ∈ DressedPair K' W (SlabMark.plow K' a z S) (SlabMark.plow K' a z T) (SlabMark.plow K' a z D):= by
  let d:= SlabMark.gaugeT K' z
  have ht:= mirror_dressed K' W _ _ _ a d (mirror_dressed K' W S T D a 0 p)
  rw [support_translation,support_translation,support_translation,sub_zero] at ht
  exact ht
end YM.CF.Buffered.Afterglow.Tower
