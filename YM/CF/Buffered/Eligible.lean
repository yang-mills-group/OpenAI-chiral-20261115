import YM.CF.Buffered.Probes

/-!
# Both reflected families, positive-half space and fits without approaching the plane
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted
open Reed (Fine)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {K : Calibration} {wide : Bool} {S : Finset Cover} {f g : Family K} {b : Bool}
variable (s : ℤ)
local notation "X" => plane (3:Axis) s
local notation "Y" => reflected K s
lemma ref_plus : Y (f+g)=Y f+Y g := funext fun _=> funext fun _=> theta_add ..
lemma ref_scale (a : ℂ) : Y (a • f)=star a • Y f := funext fun _=> funext fun _=> theta_smul ..
lemma ref_times : Y (f*g)=Y f*Y g := funext fun _=> funext fun _=> theta_mul ..
lemma ref_identity : Y 1=1 := funext fun _=> funext fun _=> theta_one _
private lemma opposite_spin : twist (pinLift 3) (cutM plusHalf) = cutM plusHalfᶜ := by
 rw [dim_cut, raising,Fir.Adef.symm]; exact angleX (mirrorX 3) true
private lemma reflected_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : InTest K wide (S.image ((plane 3 s).motion)) false (Y (scalar K f)) := by
 let F := moveC 3 s; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Y (scalar K f)=scalar K g:= by funext m x; unfold scalar reflected reflMark; rw [theta_smul,theta_one]; apply congrArg (fun u :ℂ=> u • 1); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 rw [ht]; refine .seed ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y a b=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ a) (moved_agree _ _ b))
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (creation K x i b) = -Complex.I • ∑ j, star (Mir.pin 3 j i) • removal K ((plane 3 s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold reflected reflMark creation removal
 rw [(flips_basisC 3 s (K.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (removal K x i b) = Complex.I • ∑ j, Mir.pin 3 j i • creation K ((plane 3 s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold reflected reflMark creation removal
 rw [(flips_basisC 3 s (K.c m) x i b).2]; simp only [map_sum,map_smul]
lemma InTest.reflection (p : InTest K wide S b f) : InTest K wide (S.image ((plane 3 s).motion)) b (Y f) := by
 induction p with
 | @creator x i b t v=>
   rw [reflected_creation_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∉ plusHalf
   · refine .smul _ (.remover b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   rw [show pin 3 j i=0 from Fine.entry opposite_spin t (by simpa using not_not.mp w),star_zero,zero_smul]; exact .zero
 | @remover x i b t v=>
   rw [reflected_removal_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∈ plusHalf
   · refine .smul _ (.creator b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   have ht: twist (pinLift 3) (cutM plusHalfᶜ)=cutM plusHalf:= by rw [dim_cut,map_sub,map_one,opposite_spin,dim_cut]; abel
   rw [show pin 3 j i=0 from Fine.entry ht (by simpa only [mem_compl] using t) w, zero_smul]; exact .zero
 | seed p=> exact reflected_scalar s _ p
 | zero=> rw [show Y 0=0 from funext fun _=>funext fun _=> theta_zero _]; exact .zero
 | one=> rw [ref_identity]; exact .one
 | add _ _ a b=> rw [ref_plus]; exact .add a b
 | mul _ _ a b=> rw [ref_times]; exact .mul a b
 | smul a _ ih=> rw [ref_scale]; exact .smul _ ih

private lemma AtTest.commute {S T : Finset Cover} {b : Bool} (p : InTest K wide S false f) (t : InTest K b T false g) : f*g=g*f := by
 funext m x
 have he:= ((p.support m).mono (subset_univ _)).allV x; have hg:= ((t.support m).mono (subset_univ _)).allV x; change f m x*g m x=g m x*f m x; rw [he.sign_com hg]; simp [Sector.grainB]
variable (K)
def goodSet (S : Finset Cover) := ∀ x ∈ S, K.plane0 + K.ℓ ≤ x 3
variable {K}
-- broad selects the mark grammar. In broad joint-E, Singlet isn't needed;
-- use the larger space (all bounded Borel two-field chiral tests).
structure TestFamily (K : Calibration) (wide : Bool) (f : Family K) : Prop where
 paid : ∃ S : Finset Cover, InTest K wide S false f
 allowed : wide=false → Singlet f
structure Eligible (K : Calibration) (wide : Bool) (f : Family K) : Prop where
 support : ∃ S : Finset Cover, InTest K wide S false f ∧ goodSet K S
 allowed : wide=false → Singlet f
namespace TestFamily
lemma oneT : TestFamily K wide 1 := ⟨⟨∅,.one⟩,fun _=>singlet_identity⟩
lemma zeroT : TestFamily K wide 0 := ⟨⟨∅,.zero⟩,fun _=>singlet_zero⟩
lemma add (p : TestFamily K wide f) (q : TestFamily K wide g) : TestFamily K wide (f+g) := ⟨
 (by obtain ⟨s,t⟩:=p.paid; obtain ⟨w,u⟩:= q.paid; exact ⟨s∪w,.add (t.mono subset_union_left) (u.mono subset_union_right)⟩), fun w=> singlet_add (p.allowed w) (q.allowed w)⟩
lemma scale (p : TestFamily K wide f) (z : ℂ) : TestFamily K wide (z • f) := ⟨(by obtain ⟨s,t⟩:= p.paid; exact ⟨s,.smul z t⟩),fun w=> singlet_smul (p.allowed w) z⟩
lemma mul (p : TestFamily K wide f) (q : TestFamily K wide g) : TestFamily K wide (f*g) :=⟨(by obtain ⟨s,t⟩:= p.paid; obtain ⟨w,u⟩:= q.paid; exact ⟨s∪w,.mul (t.mono subset_union_left) (u.mono subset_union_right)⟩), fun w=> singlet_mul (p.allowed w) (q.allowed w)⟩
lemma ref (p : TestFamily K wide f) : TestFamily K wide (thetaK K f) := by obtain ⟨x,u⟩:=p.paid; exact ⟨⟨_,u.reflection _⟩,fun w=> singlet_reflected f u (p.allowed w)⟩
lemma comm (p : TestFamily K wide f) (q : TestFamily K b g) : f*g=g*f := AtTest.commute p.paid.choose_spec q.paid.choose_spec
end TestFamily
namespace Eligible
lemma forget (p : Eligible K wide f) : TestFamily K wide f := ⟨⟨_,p.support.choose_spec.1⟩,p.allowed⟩
lemma oneT : Eligible K wide 1 := ⟨⟨∅,.one, by simp [goodSet]⟩,fun _=>singlet_identity⟩
lemma zeroT : Eligible K wide 0 := ⟨⟨∅,.zero, by simp [goodSet]⟩,fun _=>singlet_zero⟩
lemma addE (p : Eligible K wide f) (q : Eligible K wide g) : Eligible K wide (f+g) := ⟨(by
 obtain ⟨x,f,T⟩:=p.support; obtain ⟨y,h,U⟩:=q.support; exact ⟨x∪y,.add (f.mono subset_union_left) (h.mono subset_union_right), fun i v=> (mem_union.mp v).elim (T i) (U i)⟩), fun w=> singlet_add (p.allowed w) (q.allowed w)⟩
lemma smulE (p : Eligible K wide f) (a : ℂ) : Eligible K wide (a • f) := ⟨(by obtain ⟨x,t,v⟩:=p.support; exact ⟨x,.smul a t,v⟩),fun w=> singlet_smul (p.allowed w) a⟩
end Eligible
variable (K : Calibration) (wide : Bool)
def probes : Submodule ℂ (Family K) :=
 { carrier := {f| TestFamily K wide f}
   zero_mem':= TestFamily.zeroT
   add_mem' := fun p q=>TestFamily.add p q
   smul_mem':= fun z _ p=>TestFamily.scale p z }
def eligible : Submodule ℂ (Family K) :=
 { carrier := {f| Eligible K wide f}
   zero_mem':= Eligible.zeroT
   add_mem' := fun p q=>Eligible.addE p q
   smul_mem':= fun z _ p=>Eligible.smulE p z }
-- type of vectors; NO further generation is needed for positivity
lemma eligible_sub : eligible K wide ≤ probes K wide := fun _ p=> Eligible.forget p
lemma narrow_le : eligible K false ≤ eligible K true := fun _ (p : Eligible K false _)=> ⟨(by obtain ⟨x,t,v⟩:= p.support; exact ⟨x,t.widen,v⟩), fun w=>by contradiction⟩
end YM.CF.Buffered
