import YM.SU5.FiniteGaugeData.Tapestry.Junction
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-! # Reflection on all axes; widen, join, multiply on common sites. -/
section reflection
open Mir Phase RP Nacre Girt
open Reed (Fine)
-- direct variation of reflection proof in Buffered/Eligible.lean
def bounce (K : Calibration) (s : ℤ)(a:Axis)(f : Family K) : Family K := fun m => reflMark a s (f m)
variable {K : Calibration} {wide : Bool} {S : Finset Cover} {f g : Family K} {b : Bool}
variable (s : ℤ) (ai : Axis)
local notation "X" => plane (ai:Axis) s
local notation "Y" => bounce K s ai
lemma bounce_plus : Y (f+g)=Y f+Y g := funext fun _=> funext fun _=> theta_add ..
lemma bounce_scale (a : ℂ) : Y (a • f)=star a • Y f := funext fun _=> funext fun _=> theta_smul ..
lemma bounce_times : Y (f*g)=Y f*Y g := funext fun _=> funext fun _=> theta_mul ..
lemma bounce_identity : Y 1=1 := funext fun _=> funext fun _=> theta_one _
private lemma opposite_spin : twist (pinLift ai) (cutM plusHalf) = cutM plusHalfᶜ := by
 rw [dim_cut, raising,Fir.Adef.symm]; exact angleX (mirrorX ai) true
private lemma reflected_scalar (f : PairsC→ℂ) (p : Coeff wide S f) : InTest K wide (S.image ((plane ai s).motion)) false (Y (scalar K f)) := by
 let F := moveC ai s; let g(x:PairsC):=star (f (F x.1,F x.2))
 have ht: Y (scalar K f)=scalar K g:= by funext m x; unfold scalar bounce reflMark; rw [theta_smul,theta_one]; apply congrArg (fun u :ℂ=> u • 1); unfold g; simp only [reflFields,Prod.map_fst, Prod.map_snd,reflect_onC]; rfl
 rw [ht]; refine .seed ⟨fun v=> ?_, Girt.pole_w _ star continuous_star (Env.along (g:=Prod.map F F) p.env ((move_cont ..).prodMap (move_cont ..)).measurable),fun x y a b=>?_⟩
 · obtain ⟨c,h,e⟩:= p.narrow v; refine ⟨fun x=>star (c (F x)),(h.comp (move_cont ..)).star,?_⟩; rw [show g=fun x=>star (f (F x.1,F x.2)) from rfl,e]; rfl
 exact congrArg star (p.locus (F x.1,F x.2) (F y.1,F y.2) (moved_agree _ _ a) (moved_agree _ _ b))
private lemma reflected_creation_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (creation K x i b) = -Complex.I • ∑ j, star (Mir.pin ai j i) • removal K ((plane ai s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold bounce reflMark creation removal
 rw [(flips_basisC ai s (K.c m) x i b).1]; unfold Fock.remove; simp only [map_sum,map_smul,star_sum,star_smul]
private lemma reflected_removal_eq (x : Cover) (i : SpinIdx) (b : SU.Slot) :
    Y (removal K x i b) = Complex.I • ∑ j, Mir.pin ai j i • creation K ((plane ai s).flee x) j b := by
 funext m v; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.smul_apply]; unfold bounce reflMark creation removal
 rw [(flips_basisC ai s (K.c m) x i b).2]; simp only [map_sum,map_smul]
lemma bounceEligible (p : InTest K wide S b f) : InTest K wide (S.image ((plane ai s).motion)) b (Y f) := by
 induction p with
 | @creator x i b t v=>
   rw [reflected_creation_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∉ plusHalf
   · refine .smul _ (.remover b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   rw [show pin ai j i=0 from Fine.entry (opposite_spin ai) t (by simpa using not_not.mp w),star_zero,zero_smul]; exact .zero
 | @remover x i b t v=>
   rw [reflected_removal_eq]; refine .smul _ (InTest.sum _ _ (fun j _=> ?_)); by_cases w:j∈ plusHalf
   · refine .smul _ (.creator b w (mem_image.mpr ⟨_,v,Shape.mote ..⟩))
   have ht: twist (pinLift ai) (cutM plusHalfᶜ)=cutM plusHalf:= by rw [dim_cut,map_sub,map_one,opposite_spin,dim_cut]; abel
   rw [show pin ai j i=0 from Fine.entry ht (by simpa only [mem_compl] using t) w, zero_smul]; exact .zero
 | seed p=> exact reflected_scalar s ai _ p
 | zero=> rw [show Y 0=0 from funext fun _=>funext fun _=> theta_zero _]; exact .zero
 | one=> rw [bounce_identity]; exact .one
 | add _ _ a b=> rw [bounce_plus]; exact .add a b
 | mul _ _ a b=> rw [bounce_times]; exact .mul a b
 | smul a _ ih=> rw [bounce_scale]; exact .smul _ ih


end reflection
variable (K:Calibration) (S T U:Finset Cover)
def colorless : Swatch S := fabric S K (F:=1) .one -- depends on K only for size (maybe eq)
def rebolt (h:S⊆T) : Swatch S →ₗ[ℂ] Swatch T where
  toFun f:= fabric T K ((texture S K f).mono h)
  map_add' f g:= by apply render_inj T K; rw [render_fabric,map_add,map_add,render_fabric,render_fabric]
  map_smul' c f:= by apply render_inj T K; change render T K (fabric T K _) = render T K (c • fabric T K _); rw [render_fabric,map_smul,map_smul,render_fabric]
def broad (h:S⊆T) : Swatch S →L[ℂ] Swatch T:= (rebolt K S T h).mkContinuous (spread S) fun i=>by
  obtain ⟨m,p⟩:= (separates K T).exists
  refine sampling T K m ⟨p⟩ _ fun x=>?_ ; rw [←appearRender]; change ‖render _ _ (fabric _ _ ((texture S K i).mono h)) _ _‖ ≤ _; rw [render_fabric]; exact renderLe ..
lemma broadRender (h:S⊆T) (x): render T K (broad K S T h x)= render S K x:= render_fabric T K ((texture S K x).mono h)
lemma broadNorm (h:S⊆T) (x): ‖broad K S T h x‖≤ spread S*‖x‖:= by
  obtain ⟨m,p⟩:= (separates K T).exists; apply sampling T K m ⟨p⟩; intro u; rw [←appearRender,broadRender]; exact renderLe ..
lemma comparison₁ (h:S⊆T)(x:Swatch S): ‖x‖≤ spread T*‖broad K S T h x‖:=by
  obtain ⟨m,p⟩:= (separates K S).exists; apply sampling S K m ⟨p⟩; intro u; rw [←appearRender,←broadRender _ _ _ h]; exact renderLe ..
lemma broadInj (h:S⊆T): Injective (broad K S T h):=by intro x y p; apply render_inj S K; rw [←broadRender _ _ _ h x, ←broadRender _ _ _ h y,p]

def brocade (F:Swatch S)(G:Swatch S): Swatch S:= fabric S K (F:=render S K F * render S K G) (.mul (texture ..) (texture ..))
lemma bareUnit : render S K (colorless K S)=1:= render_fabric ..
lemma bareMult (F G: Swatch S) : render S K (brocade K S F G)=render S K F * render S K G:= render_fabric ..
lemma patternScale (a:ℂ)(F:Swatch S) : render S K (a • F)=a • render S K F:= map_smul .. -- tune
lemma brocadeBound (F G:Swatch S):‖brocade K S F G‖ ≤ (spread S)^2*‖F‖*‖G‖:=by
  obtain ⟨m,p⟩:=(separates K S).exists; refine sampling S K m ⟨p⟩ _ fun x=>?_; rw [←appearRender,bareMult,Pi.mul_apply,Pi.mul_apply]; exact (norm_mul_le ..).trans ((mul_le_mul (renderLe ..) (renderLe ..) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg F))).trans_eq (by ring))
lemma brocade₁ (F G J: Swatch S) : brocade K S (F+G) J = brocade K S F J+brocade K S G J:= render_inj S K <| by rw [map_add]; simp only [bareMult,map_add,add_mul] -- rw matches wrong Add
lemma brocade₂ (F G J: Swatch S) : brocade K S F (G+J) = brocade K S F G + brocade K S F J:= render_inj S K <| by rw [map_add]; simp only [bareMult,map_add,mul_add]
lemma brocadeScale₁ (z:ℂ)(F G:Swatch S): brocade K S (z • F) G=z • brocade K S F G:= render_inj S K (by rw [map_smul,bareMult,bareMult,map_smul,Algebra.smul_mul_assoc])
lemma brocadeScale₂ (z:ℂ)(F G:Swatch S): brocade K S F (z • G)=z • brocade K S F G:= render_inj S K (by rw [map_smul,bareMult,bareMult,map_smul,Algebra.mul_smul_comm])
def brocadeₗ : Swatch S→ₗ[ℂ] (Swatch S→ₗ[ℂ] Swatch S) where
  toFun x:= ⟨⟨brocade K S x,brocade₂ K S x⟩,fun z=>brocadeScale₂ K S z x⟩ -- syntax
  map_add' x y:= LinearMap.ext fun z=> brocade₁ ..
  map_smul' x y:= LinearMap.ext fun z=> brocadeScale₁ ..

def brocadeL : Swatch S →L[ℂ] (Swatch S →L[ℂ] Swatch S):= (brocadeₗ K S).mkContinuous₂ (spread S^2) (brocadeBound K S)
lemma brocadeL_eq (x y): brocadeL K S x y=brocade K S x y:= rfl

open Mir Phase RP Nacre Girt
variable (s:ℤ)(a:Axis)
def negativeSide := S.image ((plane a s).motion)
local notation "Ξ"=> negativeSide S s a
private def iceberg (F:Swatch S):= fabric (negativeSide S s a) K (bounceEligible s a (texture S K F))
private lemma iceberg_rule (F:Swatch S): render Ξ K (iceberg K S s a F)=bounce K s a (render S K F):= render_fabric _ _ (bounceEligible s a (texture S K F))
private lemma renderAdd (T:Finset Cover)(F G:Swatch T): render T K (F+G)=render T K F+render T K G:=map_add ..
def mirroredₗ : Swatch S →ₗ⋆[ℂ] Swatch (negativeSide S s a) where
  toFun f := iceberg K S s a f
  map_add' x y:= by apply render_inj Ξ K; rw [renderAdd,iceberg_rule,iceberg_rule,iceberg_rule,renderAdd,bounce_plus]
  map_smul' z x:=by apply render_inj Ξ K; change render Ξ K (iceberg K S s a (z • x))=render Ξ K (star z • iceberg K S s a x); rw [patternScale,iceberg_rule,iceberg_rule,patternScale,bounce_scale]

private lemma mirrorL_bound (x:Swatch S): ‖mirroredₗ K S s a x‖ ≤ spread S * ‖x‖:=by
  obtain ⟨m,p⟩:= (separates K Ξ).exists
  refine sampling Ξ K m ⟨p⟩ _ fun u=>?_ ; rw [←appearRender]; change ‖render Ξ K (iceberg K S s a x) m u‖≤_; rw [iceberg_rule,bounce,reflMark]; -- find theta_norm
  rw [Fock.theta,twist_norm, Scroll.norm_cc]; exact renderLe ..


def mirrorL : Swatch S →SL[starRingEnd ℂ] Swatch (negativeSide S s a) := (mirroredₗ K S s a).mkContinuous (spread S) (mirrorL_bound K S s a)
lemma mirrored_render (x:Swatch S): render Ξ K (mirrorL K S s a x)=bounce K s a (render S K x):= iceberg_rule ..
lemma mirror_twice (f: Swatch S): bounce K s a (bounce K s a (render S K f)) = render S K f:=funext fun x=> AtSupport.refl_refl a s ((texture S K f).support x)
lemma broadCompile {F:Family K} (p:InTest K true S false F): TestFamily K true F:=⟨⟨S,p⟩,by simp⟩
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.mirrorL
#print axioms YM.CF.Buffered.Afterglow.Tapestry.brocadeL
