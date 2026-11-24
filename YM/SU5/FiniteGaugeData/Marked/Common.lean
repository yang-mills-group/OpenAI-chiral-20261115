import YM.SU5.FiniteGaugeData.Marked.Chamber
import YM.CF.Vp929.Roof.Fit

/-!
# A fixed local accounting space for both link arguments
Uses the elected Nimbus. Its conditional law is a mixture over finite site
colors and independent frame Haar draws, with one deterministic rule at all
these periods and V. We pay **all** colors on just the needed local stencil;
no identification or estimate comparing the mixing weights across periods,
no conditional densities of the reconstruction w.r.t. Haar, and no
continuity requirement on the stencil rule.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Common
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal
open VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read

variable (C:Side)(D:ℕ→ℝ)(S:Finset Cover)
-- all possible channels used at the locations; the torus colors select one
-- such itinerary. No notion of compatible periods is needed for the colors.
abbrev Courses := ↥S→ Channel C

def porch := S ∪ S.biUnion (fun a:Cover=> univ.image (fun v:Zone (Fringe C)=> (v:Cover)+a))
lemma porch_here {a:Cover} (p:a∈ S) : a∈ porch C S := mem_union_left _ p
lemma porch_there {a b:Cover} (p:a∈ S) (v:Scope (Fringe C) b): b+a∈ porch C S := by
  classical
  exact mem_union_right _ (mem_biUnion.mpr ⟨a,p,mem_image.mpr ⟨⟨b,v⟩,mem_univ _,rfl⟩⟩)

abbrev Hall := (((porch C S):Type) × Axis→ E) × (((porch C S):Type)→ E)
def law: Measure (Hall C S) := (Measure.pi fun _=>group.probHaar).prod (Measure.pi fun _=>group.probHaar)
instance : IsProbabilityMeasure (law C S) := by unfold law; infer_instance

def strips (W:Hall C S): LinksC := fun e=> if h:e.1∈ porch C S then W.1 (⟨e.1,h⟩,e.2) else 1
def frame (W:Hall C S)(x:Cover): E := if h:x∈ porch C S then W.2 ⟨x,h⟩ else 1
@[fun_prop] lemma strips_m : Measurable (strips C S) := by
  apply measurable_pi_lambda; intro e; unfold strips; split; exact (measurable_pi_apply _).comp measurable_fst; exact measurable_const
@[fun_prop] lemma frame_m (x:Cover): Measurable fun W=> frame C S W x := by
  unfold frame; split; exact (measurable_pi_apply _).comp measurable_snd; exact measurable_const

def pairs (u:Courses C S)(W:Hall C S):PairsC :=
  let g:=frame C S W
  let V:=strips C S W
  (V,Lattice.gauge g⁻¹ (fun e=> if h:e.1∈ S then
    display C D (u ⟨e.1,h⟩) (translate e.1 (Lattice.gauge g V)) e.2 else 1))
lemma pairs_m (u:Courses C S): Measurable (pairs C D S u):= by
  let T (x:Cover)(W:Hall C S):LinksC:=translate x (Lattice.gauge (frame C S W) (strips C S W))
  have h(x):Measurable (T x):= by
    apply measurable_pi_lambda; intro e
    unfold T Lattice.translate Lattice.gauge
    fun_prop
  have ht(e:Edge Cover)(v:e.1∈ S): Measurable (fun W:Hall C S=> display C D (u ⟨e.1,v⟩) (T e.1 W) e.2):=(Cane.runsM ..).comp (h e.1)
  unfold pairs; apply (strips_m C S).prodMk
  apply measurable_pi_lambda; intro e; unfold Lattice.gauge; dsimp only [Pi.inv_apply]
  apply Measurable.mul _ ((frame_m C S _).inv.inv)
  apply Measurable.mul ((frame_m C S _).inv)
  split; exact ht _ _; exact measurable_const

variable (n : Side)
def crop (X:Pane n)(g:Borel.Aerial.Frame n):Hall C S:=
  (fun e=> X (wrap (More n) (e.1:Cover),e.2), fun p=> g (wrap (More n) (p:Cover)))
private lemma strips_crop (X:Pane n)(g:Borel.Aerial.Frame n)(i:Edge Cover)(p:i.1∈ porch C S):
    strips C S (crop C S n X g) i=onC n X i:= by
  unfold strips; rw [dif_pos p,onC_spec]; rfl
private lemma frame_crop (X:Pane n)(g:Borel.Aerial.Frame n){i:Cover}(p:i∈ porch C S):
    frame C S (crop C S n X g) i=g (wrap (More n) i):= by unfold frame; rw [dif_pos p]; rfl

def chooseCourse (w:Read.Wor (More n) C): Courses C S:=fun a=> fetch C (More n) w (wrap (More n) a.val)
lemma scene_pair (X:Pane n)(g:Borel.Aerial.Frame n)(w:Read.Wor (More n) C):
    let Q:PairsC:=pairs C D S (chooseCourse C S n w) (crop C S n X g)
    Agrees S Q.1 (onC n X) ∧ Agrees S Q.2 (onC n (Dream.sceneQ C D n X (g,w))) := by
  intro F; let W:=crop C S n X g
  constructor
  · exact fun i p _=> strips_crop C S n X g i (porch_here C S p)
  rintro ⟨a,i⟩ p t
  change (frame C S W a)⁻¹*(if h:a∈ S then display _ _ _ _ _ else 1)*((frame C S W (a+step i))⁻¹)⁻¹ = _
  change a∈ S at p; change a+step i∈S at t
  rw [dif_pos p,frame_crop C S n X g (porch_here C S (show a∈ S from p)),frame_crop C S n X g (porch_here C S (show a+step i∈ S from t)),onC_spec]
  let e:=wrap (More n) a
  rw [map_add,wrap_step]
  -- spell out to avoid costly defeq unfolding display
  let A:Realms:=translate a (Lattice.gauge (frame C S (crop C S n X g)) (strips C S (crop C S n X g)))
  let B:Realms:=expandAt e (Lattice.gauge g X)
  let F:=fetch C (More n) w e
  suffices he: display C D F A i=display C D F B i from
    congrArg (fun v:E=> (g e)⁻¹*v*((g (e+step i))⁻¹)⁻¹) he
  refine Cane.scope0 C D A B F ?_ i
  rintro ⟨b,j⟩ hx hv
  change frame C S (crop C S n X g) (b+a) * strips C S (crop C S n X g) (b+a,j) *
      (frame C S (crop C S n X g) (b+a+step j))⁻¹ = g (wrap (More n) b+e) * X (wrap (More n) b+e,j) * (g ((wrap (More n) b+e)+step j))⁻¹
  have h₀:= porch_there C S (a:=a) (b:=b) p hx
  have h₁:=porch_there C S (a:=a) (b:=b+step j) p hv
  rw [add_right_comm b] at h₁
  rw [frame_crop C S n X g h₀,strips_crop C S n X g (b+a,j) h₀,onC_spec,
      frame_crop C S n X g h₁]
  simp [e]
end YM.CF.Buffered.Afterglow.Common
