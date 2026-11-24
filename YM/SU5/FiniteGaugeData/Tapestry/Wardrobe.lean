import YM.SU5.FiniteGaugeData.Tapestry.Levels
/-!
# Sup norm spaces also for each participating *finite* period

ALL supported even Mark tests of the gauge torus & matter volume. Visible & true
links. This norm is on the theory's Mark, **not** the cutoff-dependent space of
dressed functions of the gauge/aux law. In particular we don't set it from L^p
of any law. We will be able to take UV limits and comparisons on the whole torus
in terms of these spaces.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Pastry
open Reed (Fine think)
variable (N:Side)
abbrev MarkSpace := ↥(lp (fun _ : Fields N => FC (Single N)) ∞)
private lemma envPool (f:MarkSpace N) (h:Measurable (⇑f)): Envelope (⇑f) := ⟨h,‖f‖,lp.norm_apply_le_norm ENNReal.top_ne_zero f⟩

protected def tor : Subalgebra ℂ (MarkSpace N) where
  carrier := { f:MarkSpace N | AtSupport false univ (⇑f)}
  add_mem' := fun {_ _} p q=> AtSupport.addM p q
  mul_mem' := fun {_ _} p q=> AtSupport.mulM p q
  one_mem':= AtSupport.oneM _
  zero_mem':= AtSupport.zeroM
  algebraMap_mem' := fun z => by rw [Algebra.algebraMap_eq_smul_one]; exact (AtSupport.oneM (n:=N) univ).smulM _ -- explicit tune

abbrev Ward := ↥(Tapestry.tor N)
variable {N}
-- abbreviate for typeclass performance (structure is exactly inherited)
instance : NormedAddCommGroup (Ward N):= inferInstanceAs (NormedAddCommGroup ↥(Tapestry.tor N))
instance (priority := 5000): SeminormedAddCommGroup (Ward N):= (inferInstance : NormedAddCommGroup (Ward N)).toSeminormedAddCommGroup
instance (priority := high) : NormedSpace ℂ (Ward N):= inferInstanceAs (NormedSpace ℂ ↥(Tapestry.tor N))

def attire (x:Ward N) : Mark N:= ⇑(show MarkSpace N from x.val)
namespace Ward
variable (x y:Ward N)
lemma signs : AtSupport false univ (attire x):= x.property
lemma pay(u): ‖attire x u‖ ≤ ‖x‖:= lp.norm_apply_le_norm ENNReal.top_ne_zero (show MarkSpace N from x.val) u
lemma eval_cont(u:Fields N) :Continuous (fun x:Ward N=> attire x u):= (lp.lipschitzWith_one_eval ∞ u).continuous.comp continuous_subtype_val
lemma limit_at {I:Type*} {A:Filter I}{f:I→Ward N}{x:Ward N}(p:Tendsto f A (𝓝 x))(u) : Tendsto (fun i=> attire (f i) u) A (𝓝 (attire x u)):= (eval_cont u).continuousAt.tendsto.comp p
lemma save {B:ℝ}(h:∀ z,‖attire x z‖ ≤ B): ‖x‖ ≤ B:= lp.norm_le_of_forall_le' B h
end Ward
lemma tor_closed : IsClosed (Tapestry.tor N:Set (MarkSpace N)):=by
  apply IsSeqClosed.isClosed; intro f g hf e
  have h(n) : AtSupport false univ ⇑(f n):= hf n
  have t(u:Fields N): Tendsto (fun n=> f n u) atTop (𝓝 (g u)):= (lp.lipschitzWith_one_eval ∞ u).continuous.continuousAt.tendsto.comp e
  let Q : Submodule ℂ (FC (Single N)):=
      { carrier := {v|Fine (Tset N) (modesIn N univ) false v}
        add_mem':= fun {_ _} a b => Fine.add a b
        zero_mem':= Fine.empty _
        smul_mem':= fun z x a=> Fine.scale a z }
  exact ⟨envPool N g (measurable_of_tendsto_metrizable (fun n=>(h n).env.meas) (tendsto_pi_nhds.mpr t)), fun x y p w=> tendsto_nhds_unique_of_eventuallyEq (t x) (t y) (Filter.Eventually.of_forall fun i=>(h i).dep x y p w), fun x=> Q.closed_of_finiteDimensional.mem_of_tendsto (t x) (Filter.Eventually.of_forall fun n=>(h n).allV x)⟩
instance : CompleteSpace (Ward N):= tor_closed.completeSpace_coe
@[simp] lemma attire_unit : attire (1:Ward N)=1:=rfl
@[simp] lemma attire_none : attire (0:Ward N)=0:=rfl
@[simp] lemma attire_mul (x y:Ward N):attire (x*y)=attire x*attire y:=rfl
@[simp] lemma attire_add (x y:Ward N):attire (x+y)=attire x+attire y:=rfl
@[simp] lemma attire_scale (z:ℂ)(x:Ward N):attire (z • x)=z • attire x:=rfl
lemma attireL_inj : Injective (attire (N:=N)) := fun _ _ e=>Subtype.ext (lp.ext e)
def attireL (N:Side) : Ward N →ₐ[ℂ] Mark N where
  toFun:=attire
  map_add':= attire_add
  map_mul':= attire_mul
  map_zero':= attire_none
  map_one':= attire_unit
  commutes':= fun r=>by rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,attire_scale,attire_unit]
instance : CommRing (Ward N) where
  mul_comm x y:= by apply attireL_inj; funext u; change attire x u *attire y u= attire y u* attire x u; rw [(Ward.signs x).allV u|>.sign_com ((Ward.signs y).allV u)]; simp [Sector.grainB] -- tune pipe

def frock {f:Mark N} (v:AtSupport false univ f):Ward N := by
  have he: Memℓp f ∞:= by apply memℓp_infty; obtain ⟨C,h⟩:= v.env.cost; refine ⟨C,?_⟩; rintro i ⟨y,rfl⟩; exact h y
  exact ⟨(show MarkSpace N from ⟨f,he⟩),v⟩
@[simp] lemma attireFrock {f:Mark N}{v:AtSupport false univ f}: attire (frock v)=f:=rfl

-- Any side: EVERY supported even torus Mark is literally represented by a Swatch,
-- even if the support does not inject into the side. Take thick(T) for T the
-- fundamental tails. `eye` works on T even though edges leaving may wrap, and
-- coefficients extend as functions supported on tips T.
def fundamentalTails (N:Side) : Finset Cover:= (Finset.univ : Support (More N)).image (Rush.natural)
abbrev thick (N:Side) := tips (fundamentalTails N)
local notation "Φ" =>fundamentalTails N
lemma luscious (N:Side): region (fundamentalTails N) N = Finset.univ:= Finset.eq_univ_of_forall (fun i=> mem_image.mpr ⟨_,mem_image_of_mem _ (mem_univ i),Rush.nat_true i⟩) -- implicit N tune
lemma accommodates : Hosp (fundamentalTails N) N:= by
  constructor; intro x hx y hy h; obtain ⟨i,_,rfl⟩:= Finset.mem_image.mp hx; obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hy; rw [Rush.nat_true,Rush.nat_true] at h; rw [h]
lemma replantThick {x y: LinksC}(h: Agrees (thick N) x y) : graft (fundamentalTails N) N x=graft (fundamentalTails N) N y:= by
  funext u; rcases u with ⟨a,i⟩; obtain ⟨l,t,rfl⟩:=mem_image.mp (luscious N|>.symm ▸ mem_univ a)
  exact (onC_spec N (graft (fundamentalTails N) N x) (l,i)).symm.trans ((Satin.tail _ _ accommodates x (l,i) t).trans ((h (l,i) (tips_here _ t) (tips_there _ t i)).trans ((Satin.tail _ _ accommodates y (l,i) t).symm.trans (onC_spec N _ (l,i)))))

lemma replantThick_both (x y:PairsC)(p:Agrees (thick N) x.1 y.1)(q:Agrees (thick N) x.2 y.2): replant (fundamentalTails N) N x = replant (fundamentalTails N) N y := by
  apply Prod.ext <;> simp only [replant]
  · exact replantThick (x:=x.1) (y:=y.1) (N:=N) p
  exact replantThick (x:=x.2) (y:=y.2) (N:=N) q -- semicolon precedence? <;> scopes

variable (K:Calibration) (M:Side)
-- helper taking refutable N to ease reading
lemma attireAppear {f: Mark N}(e:K.c M=N) (h: AtSupport false univ f) : ∃ x:Swatch (thick N), arrange (K.c M) N e (appear (thick N) K M x)=f:=by
  subst N; let n:=K.c M; let Z:= fundamentalTails n; let F:= eye Z K M accommodates
  let A(i:Evens Z)(V:PairsC):= F i (f (replant Z n V))
  let g:Family K:=∑ i:Evens Z,note K (A i) (tagWord Z i.val)
  have hl : InTest K true (thick n) false g:= by
    refine InTest.sum univ _ (fun i _=>?_)
    have ht : Coeff true (thick n) (A i) := by
      refine ⟨fun _=>by contradiction,?_, fun x y p q=>congrArg (fun z=> F i (f z)) (replantThick_both (N:=n) x y p q)⟩
      exact Env.along (g:=replant Z n) (Girt.pole_w f (F i) (LinearMap.continuous_of_finiteDimensional _) h.env) (replant_b _ _)
    -- `brand` only on original Z. use monotonic bracket or `Tines` mono
    exact (by simpa only [i.property] using note_t K (tagWord Z i.val) ht (fun y p=> tips_here _ (brand Z i.val _ p)))
  refine ⟨fabric _ _ hl,?_⟩
  change appear (thick n) K M (fabric (thick n) K hl)=_
  have hZ : AtSupport false (region Z n) f:= (luscious n).symm ▸ h
  rw [←appearRender, render_fabric]; funext x; dsimp only [g]; simp_rw [Finset.sum_apply,note_v,spool_sing]
  rw [eye_rep Z K M accommodates (hZ.allV x)]; apply sum_congr rfl; intro i _
  exact congrArg (fun z=> F i z • spool n (tagWord Z i.val)) (hZ.dep _ _ (untack Z n accommodates x.1) (untack Z n accommodates x.2))

open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
local notation "Ω" => side Y i s
def wearStepₗ : Swatch S→ₗ[ℂ] Ward (side Y i s) where
  toFun x:= frock ((presented Y H s i S x).mono (subset_univ _))
  map_add' x y:= attireL_inj (map_add (present Y H s i S) x y)
  map_smul' z x:= attireL_inj (map_smul (present Y H s i S) z x)
def wearStep : Swatch S →L[ℂ] Ward (side Y i s):= (wearStepₗ Y H S s i).mkContinuous (spread S) fun x=> Ward.save (wearStepₗ Y H S s i x) (present_bound Y H s i S x)
lemma attire_wear (x:Swatch S): attire (wearStep Y H S s i x)= present Y H s i S x:=rfl
lemma wardrobeRange: Surjective (wearStep Y H (thick (side Y i s)) s i):= fun f=>
  (attireAppear (tent Y H) (momentm Y i s) (terrain Y H (Y.ir i) s) (Ward.signs f)).imp fun x h=> attireL_inj h
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.wardrobeRange
