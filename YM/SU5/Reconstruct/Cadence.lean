import YM.SU5.Reconstruct.Sigma
set_option autoImplicit false
set_option maxHeartbeats 230000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.SelectionAnalysis.Regularizing
open Function Set Filter Metric MeasureTheory Measure InnerProductSpace
open CF.Buffered.Afterglow.Tower MeshClock Germ Vacancy Vacancy.Average Sunbelt Spectral OS Analysis Semigroup
open scoped Topology InnerProductSpace NNReal ENNReal
/-!
# Average time healing displacement stamp

For ANY Sunbelt with measurements and a commuting OS Semigroup, the
lemma records exactly the multivariable heat action obtainable after
smearing with offsets in **all axes**, evenly, using the same mesh. It
works even for the nonphysical clamp when ordering fails (don't use
signal identities in such a case).
-/
variable {A : Hilbert}(M : Mesh)
local notation "L₀" => marks M
noncomputable abbrev SceneGrid := Axis → marks M
def plain(M:Mesh) : SceneGrid M →+ (Axis → ℝ) where
 toFun u a:= Subtype.val (u a)
 map_zero':=rfl
 map_add' _ _:=rfl
abbrev SceneCut (l:FrameRef) := Axis → TilePoint M l
def pellet (l:FrameRef)(c:SceneCut M l):SceneGrid M:= fun i=> pencilMark M l (c i)
local notation "X₀"=> plain M
section sweep
variable {I:Type*}[Fintype I][DecidableEq I] (X: Alliance I (marks M) A) (t: List I)
lemma raw_below (u:I→ marks M)(x:A):‖X.raw t u x‖ ≤ ‖x‖:=by
 induction t with
 | nil=>exact le_refl _
 | cons i t ih=>rw [X.raw_step,ContinuousLinearMap.comp_apply]; exact ((X.crew i).pulls _ _).trans ih
lemma raw_for (u v:I→ marks M)(p:∀ i∈ t,u i=v i): X.raw t u=X.raw t v:= by
 induction t with
 | nil=>rfl
 | cons i t ih=> rw [X.raw_step,X.raw_step,p i (List.mem_cons_self),ih (fun x a=>p x (List.mem_cons_of_mem _ a))]
local notation "P" i:max=> X.crew i
variable (n:FrameRef)
local notation "K"=> TilePoint M n
local notation "p₀"=> pencilMark M n
lemma center_raw (p:t.Nodup)(y:A): Average.center (fun c:I→TilePoint M n=> X.raw t (fun i=>pencilMark M n (c i)) y)= Rides.first M X t n.1 n.2 y:=by
 induction t with
 | nil=> exact Average.constant (A:=I→K) y
 | cons i t ih=>
    obtain ⟨a,b⟩:= List.nodup_cons.mp p
    rw [splice i]
    have he (z:K)(w:I→K): X.raw (i::t) (fun k=>p₀ (Function.update w i z k)) y=
        ((X.crew i).play (pencilMark M n z)) (X.raw t (fun k=>p₀ (w k)) y):=by
       rw [X.raw_step, update_self,raw_for M X t _ (fun k=> p₀ (w k)) (by intro k p; rw [Function.update_of_ne (show k≠ i from fun h=>a (h ▸ p))])]; rfl
    change Average.center (fun u:K=>Average.center (fun w:I→K=> X.raw (i::t) (fun k=>p₀ (Function.update w i u k)) y))=_
    simp_rw [he,Average.natural, ih b]; rw [Rides.first_step,ContinuousLinearMap.comp_apply]; exact (avgvalue M (X.crew i) _ _ _).symm
-- multiple lists fine
lemma raw_on (p:t.Nodup)(x:A) : Tendsto (fun n:FrameRef=> Average.center (fun c:I→TilePoint M n=> X.raw t (fun i=>pencilMark M n (c i)) x)) zoom (𝓝 ((X.aviator t).starProjection x)):=by
 simp_rw [center_raw M X t _ p x]; rw [←stack_projection X t]; exact convergence _ _ _ (fun n=>Rides.consec M X t x n) (Rides.onwards M X t x)
end sweep

section setup
variable {j:Axis}(B: Sunbelt j (marks M) A) (S : OS.Semigroup A j)
local notation "R₀"=> B.track.aviator B.list
local notation "T"=> B.track.Realm B.list
local notation "Y"=> R₀.orthogonalProjectionOnto -- parse
local notation "Ψ"=> B.plane
-- G is continuous-sector restriction; use book Cl
-- equality B.heat=S.E needed for real semantics, not builds
variable (h : B.heat = S.E) (q : ∀ i, ∀ (v:marks M)(t:ℝ≥0), ((B.track.crew i).play v).comp (S.E t)=(S.E t).comp ((B.track.crew i).play v))
noncomputable def regionT : OS.Semigroup (B.track.Realm B.list) j:= glass B (daylight M) S q
local notation "G"=>regionT M B S q

-- abstract continuum version
def moor {j:Axis} (S:OS.Semigroup A j)(v:Axis→ℝ): A.Op:= (S.E (v j).toNNReal).comp (S.U (diameter v))
lemma moor_apply {j:Axis} (S:OS.Semigroup A j)(v:Axis→ℝ)(x:A): moor S v x=S.E (v j).toNNReal (S.U (diameter v) x):=rfl
include h
lemma plane_edit (v:SceneGrid M)(x:T): B.plane v x.val=((moor (G) (plain M v) x : R₀).val:A):=by
 unfold Sunbelt.plane; rw [h, moor_apply]
 rw [show (G)=glass B (daylight M) S q from rfl]; rw [glass_heat, show ((glass B (daylight M) S q).U (diameter (X₀ v)) x : R₀).val=_ from glass_move B (daylight M) S q x v]; rfl
lemma plane_cost (v:SceneGrid M)(x:A) : ‖B.plane v x‖≤‖x‖:=by unfold Sunbelt.plane; rw [ContinuousLinearMap.comp_apply,h]; exact (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))).trans (raw_below M B.track B.list _ x) -- include inherits q? no
omit h
lemma moor_cost {j:Axis} (S:OS.Semigroup A j)(v:Axis→ℝ)(x:A): ‖moor S v x‖≤‖x‖:=by rw [moor_apply]; exact (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))).trans (S.unitary _ x).le
lemma moor_visit {j:Axis} (S:OS.Semigroup A j)(x:A) : Continuous (fun v=>moor S v x):=by
 let X(v:Axis→ℝ):= S.U (diameter v) x; let Q(v:Axis→ℝ):= S.E (v j).toNNReal; let W(v:Axis→ℝ):= Q v (X v)
 have HX: Continuous X := (S.continuousU x).comp ((SEP j).continuous.comp (PiLp.continuous_toLp 2 _)) -- need name continuity SEP composition
 have h(y:A) : Continuous (fun v:Axis→ℝ=> Q v y):=(S.continuousE y).comp (continuous_real_toNNReal.comp (continuous_apply j))
 refine continuous_iff_continuousAt.mpr (fun v => ?_)
 change Tendsto W (𝓝 v) (𝓝 (Q v (X v)))
 refine tendsto_of_tendsto_of_dist ((h (X v)).tendsto v) ?_
 apply squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ (tendsto_iff_dist_tendsto_zero.mp (HX.tendsto v))
 refine Eventually.of_forall fun i=> ?_; change dist (Q i (X v)) (Q i (X i)) ≤ _
 rw [dist_comm (Q i _),dist_eq_norm,dist_eq_norm,←map_sub]; exact ((Q i).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))

variable {D:Type*}(L:Filter D)(f:D→ FrameRef)(P : Tendsto f L zoom)
include P in
lemma pellet_moves (a:∀i, SceneCut M (f i)) : Tendsto (fun i=> plain M (pellet M (f i) (a i))) L (𝓝 0):=
   tendsto_pi_nhds.mpr fun i=>pens L M (v:=fun b=> a b i) P
-- compute nested. `splice at t axis`. chosen time offset z. include same receipts.
local notation "O" n:max => TilePoint M n
-- axis DecidableEq? Trans instances synthesis
noncomputable def alone (i:FrameRef)(a:Axis)(b:TilePoint M i): SceneGrid M:= Function.update 0 a (pencilMark M i b)
include P in
lemma alone_moves(a : Axis)(c:∀i, TilePoint M (f i)): Tendsto (fun i=> plain M (alone M (f i) a (c i))) L (𝓝 0):=by
 apply tendsto_pi_nhds.mpr; intro d
 rcases eq_or_ne d a with rfl|p
 · unfold alone; change Tendsto (fun i=> (Function.update (0:Axis→marks M) d (pencilMark M (f i) (c i)) d).val) _ _; simp only [Function.update_self]; exact pens L M (v:=fun i=> c i) P
 unfold alone; change Tendsto (fun i=> (Function.update (0:Axis→marks M) a (pencilMark M (f i) (c i)) d).val) _ _; simp only [Function.update_of_ne p,Pi.zero_apply,AddSubgroup.coe_zero]; exact tendsto_const_nhds

lemma split_axis (i:FrameRef)(a:Axis)(b:TilePoint M i)(c:Other Axis a → TilePoint M i)(d:Axis)(v:d≠a): pellet M i ((Equiv.funSplitAt a _).symm (b,c)) d=pencilMark M i (c ⟨d,v⟩) :=by unfold pellet; simp [v]
local notation "K"=> {i:Axis // i≠j}
local notation "Φ" i:max v:max=> (Ψ) (alone M i j v)
lemma combined (v: SceneGrid M) (i:FrameRef)(x:A):
  Average.center (fun p:SceneCut M i=> B.plane (v+pellet M i p) x)=
    Average.center (fun p:TilePoint M i=> B.plane (v+alone M i j p) (Rides.first M B.track B.list i.1 i.2 x)):=by
 rw [stripe j]; apply Average.eq_of; intro a
 rw [←center_raw M B.track B.list i B.unique_list x,←Average.natural]
 apply Average.eq_of; intro b
 let c:= (Equiv.funSplitAt j (TilePoint M i)).symm (a,b)
 let w:SceneGrid M:= v+alone M i j a
 have he : (v+pellet M i c) j=w j:=by simp [c,w,pellet,alone]
 have hE : (fun i':K => (v+pellet M i c) (i':Axis)) = (fun i':K=> w (i':Axis))+(fun k:K=>pencilMark M i (b k)):= by
   funext k; unfold c; rw [Pi.add_apply,split_axis _ _ _ _ _ _ k.property]; simp [w, alone,Function.update_of_ne k.property]
 change B.plane (v+pellet M i c) x=B.plane w _; unfold Sunbelt.plane
 rw [he,hE,Germ.Alliance.travelR]; rfl
include h
-- Uniform application. parameter D ranges arbitrarily, even varying previous start.
include P

lemma across_pad (v:D→SceneGrid M)(u:Axis→ℝ)(d:Tendsto (fun i=> plain M (v i)) L (𝓝 u))(x:A) :
 Tendsto (fun i=> Average.center (fun c:SceneCut M (f i)=> B.plane (v i+pellet M (f i) c) x)) L (𝓝 ((moor (G) u ((R₀).orthogonalProjectionOnto x):R₀).val)) :=by
 simp_rw [combined]
 let U(i:D):=TilePoint M (f i); let J:= uniform L U; let K' := (R₀).orthogonalProjectionOnto x
 have e : Tendsto (fun z:Sigma U=> plain M (v z.1 + alone M (f z.1) j z.2)) J (𝓝 u):=by
    have hx:= alone_moves M J (fun z : Sigma U=>f z.1) (P.comp (at_uniform (A:=U) L)) j (fun z=> z.2); simp_rw [map_add]; rw [show u=u+0 from (add_zero u).symm]; exact (d.comp (at_uniform L)).add hx -- maybe rewrite add touches d variables
 apply avg_move L (F:=fun z:Sigma U=> Ψ (v z.1 + alone M (f z.1) j z.2) (Rides.first M B.track B.list (f z.1).1 (f z.1).2 x))
 let T'(i:D):= Rides.first M B.track B.list (f i).1 (f i).2 x
 let L'(z:Sigma U):= v z.1+alone M (f z.1) j z.2
 have he (z:Sigma U): (moor (G) ((X₀) (L' z)) K':R₀).val= Ψ (L' z) K'.val:= (plane_edit M B S h q _ _).symm
 have hu:Tendsto (fun z:Sigma U=> (Ψ) (L' z) K'.val) J (𝓝 ((moor (G) u K':R₀).val)) :=by simp_rw [←he]; exact (continuous_subtype_val.tendsto _).comp (((moor_visit (G) K').tendsto u).comp e)
 have hp:= ((raw_on M B.track B.list B.unique_list x).comp P).comp (at_uniform (A:=U) L)
 have hp':Tendsto (fun z:Sigma U=> T' z.1) J (𝓝 (K'.val:A)):= by
    simp_rw [center_raw M B.track _ _ B.unique_list x] at hp
    -- convert
    exact hp
 apply tendsto_of_tendsto_of_dist hu
 refine squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ (tendsto_iff_dist_tendsto_zero.mp hp')
 refine Eventually.of_forall fun i=> ?_; change dist (Ψ (L' i) _) (Ψ (L' i) (T' i.1)) ≤ _
 rw [dist_comm (Ψ (L' i) _),dist_eq_norm,dist_eq_norm,←map_sub]
 exact plane_cost M B S h _ _
end setup
end YM.SelectionAnalysis.Regularizing
