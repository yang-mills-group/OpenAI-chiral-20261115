import YM.SU5.FiniteGaugeData.Mist.Hike
import YM.SU5.FiniteGaugeData.Mist.AtlasX
/-!
# Genuine real arrangements
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist.Leda
open Function Filter Metric Finset Lattice Hills Hike
open scoped Topology BigOperators InnerProductSpace NNReal ENNReal
variable {H:Hilbert}{L:Side}{a:Axis}{σ T:Type*}[TopologicalSpace T]
variable (V: List σ)
section propag
variable (S:OS.Semigroup H a)(A:ℝ≥0)(u w:T→H.space)(p:T→ℝ≥0)
lemma steamV (h:Continuous p)(v:Continuous u) : Continuous (fun t=> S.E (p t) (u t)):=by
 refine continuous_iff_continuousAt.mpr fun x=> Metric.tendsto_nhds.mpr fun ε k=> ?_
 filter_upwards [Metric.tendsto_nhds.mp ((S.continuousE (u x)).comp h|>.tendsto x) (ε/2) (by positivity),Metric.tendsto_nhds.mp (v.tendsto x) (ε/2) (by positivity)] with t y z
 have he: dist (S.E (p t) (u t)) (S.E (p t) (u x)) ≤ dist (u t) (u x):=by rw [dist_eq_norm,←map_sub,dist_eq_norm]; exact ((S.E (p t)).le_of_opNorm_le (S.shrinks _) _).trans_eq (one_mul _)
 apply lt_of_le_of_lt (dist_triangle _ (S.E (p t) (u x)) _); dsimp only [Function.comp_apply] at y; linarith only [y,he,z]
-- packaging metric since Bool.Set inhabited. avoid slow GroupR resolution.
lemma payT {σ T:Type}[TopologicalSpace T](F:σ→ H.Op)(G:T→σ→σ→ H.Op)(C:∀ i j (x:T→H.space),Continuous x → Continuous (fun t=> G t i j (x t))) (w:H.space)(Z:List σ): Continuous (fun t=> TapeT F (G t) Z w) :=by
 cases Z with
 | nil=> exact continuous_const
 | cons i Z=> induction Z generalizing i with
    | nil=> exact continuous_const (X:=T) (y:= F i w)
    | cons j Z ih=> exact (F i).continuous.comp (C i j _ (ih j)) -- order arguments
end propag
-- with Δ  (real component maps preferred over E4? use axis→ℝ, assembled E4 when implementing). relation
abbrev Grid (σ:Type*)(E:Type) :=σ→ Axis→ E
variable (d:σ→ Axis→ℝ)
local notation "G"=> Grid σ ℝ
variable (z:G)(p:Grid σ (VistaQ L)) (u:ℝ)
abbrev pixels {σ:Type*}(L:Side) (x:Grid σ (VistaQ L)):Grid σ ℝ:=fun i j=>(x i j).val
abbrev page (a:Axis)(x:G)(i j:σ):Prop:=x i a +d i a < x j a
def Space (a:Axis): Set (Grid σ ℝ):={u| V.Pairwise (page d a u)}
variable (B:List Axis)
-- membership of rotations.Plan Support can meet only for requested axes.B. Notion requiring same depths? σ.Der.
lemma em_space (a:Axis)(i j:σ): IsOpen {x:Grid σ ℝ|page d a x i j}:=  isOpen_lt (f:=fun z:G=> z i a+d i a) (by fun_prop) (by fun_prop)
lemma pairwise_open (a:Axis) : IsOpen (Space V d a):=by
 classical
 induction V with
 | nil=> rw [show Space [] d a=Set.univ from Set.eq_univ_of_forall (fun i=>List.Pairwise.nil)]; exact isOpen_univ
 | cons i v ih=>
    have he:Space (i::v) d a = (⋂ j∈v.toFinset, {x | page d a x i j}) ∩ Space v d a:=by ext; simp [Space]
    rw [he]; apply IsOpen.inter ?_ ih; exact isOpen_biInter_finset (fun j _=> em_space d a i j) -- signature?
lemma pixel_wick : Continuous (pixels (σ:=σ) L):=continuous_pi fun i=> continuous_pi fun j=> continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i))
lemma pixel_dense (u:1<L.val): DenseRange (pixels (σ:=σ) L) := by
 exact (DenseRange.piMap (ι:=σ) fun _=> (DenseRange.piMap (ι:=Axis) (fun _=>(indicate L u).dense)))
-- axis motions
section
variable {σ:Type}[DecidableEq σ](v:Grid σ (VistaQ L))(Q:List σ) -- h selection
lemma aerate_C (a:Axis): Continuous (fun t=> Hike.aerate v Q a t):=by
 apply continuous_pi; intro j; unfold aerate; split; swap; exact continuous_const
 refine continuous_pi fun i=>?_ ; by_cases h:i=a; · subst i; simp only [Pi.add_apply,Pi.single_eq_same]; fun_prop
 simp_rw [Pi.add_apply,Pi.single_eq_of_ne h]; exact continuous_const
lemma aerate_home (a:Axis): Hike.aerate v Q a 0 = v:=by ext i k; by_cases h:i∈ Q <;> simp [aerate,h]
end
end YM.CF.Buffered.Afterglow.Hierarchy.Mist.Leda
