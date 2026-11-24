import YM.SU5.Selected.Hill.Valse
import YM.SU5.Selected.Hill.Freight
-- `pulse` defined in Skim; move to Valse later import for now
import YM.SU5.Selected.Hill.Skim
/-! Color throughput. coordinate price of the core lights. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
variable {G:Gauge}{n:Side}
variable {W:PathData G}{C:Clip}{σ X D θ:ℝ}
def colorup {I:Type*}(x:Scene G I) (i:I) : G.Color:= WithLp.toLp 2 (fun j=> x (i,j))
def colordown {I:Type*}(x:I→G.Color): Scene G I:= fun i=> x i.1 i.2
@[simp] lemma up_down {I:Type*}(x:I→G.Color): colorup (colordown x)=x:=rfl
@[simp] lemma down_up {I:Type*}(x:Scene G I) : colordown (colorup x)=x:=rfl
abbrev ListT(G:Gauge)(n:Side):= Scene G (EdgeT n)
-- polynomial root reckoning
def tin (x:ListT G n) := badge (colorup x) -- n inference with G?
lemma color_pi (x:ListT G n)(b:Plane n) (i:G.ColorIndex): faceCurl b (tin x) i = (curl ℝ n *ᵥ page x i) b:=by
 rw [curl_applyZ]; change ((d 1 n)*ᵥ parts G 1 (tin x) i) (b.1,plaquette b.2)= _; rw [d_plaquettes]; simp only [parts,tin, badge, colorup, show ∀ i:Axis,axisEquiv.symm (coord i)=i from fun i=>axisEquiv.symm_apply_apply _ ]; rfl -- adjust Exterior.prec names
lemma tinsel (x:ListT G n)(i:G.ColorIndex) (H:Bed): (page x i) ⬝ᵥ pasture (H.metric.acts n)*ᵥ page x i= let v:=parts G 1 (tin x) i; v ⬝ᵥ ((Precision.K (H.metric.acts n))*ᵥ v) :=by
 let v:= page x i; let e:=wheel n; have hv: parts G 1 (tin x) i= v ∘ e.symm:=rfl
 dsimp only; rw [hv,pasture,submatrix_mulVec_equiv]; let Q:=(K (H.metric.acts n))*ᵥ(v ∘ e.symm); change v ⬝ᵥ (Q ∘ e)= (v∘e.symm) ⬝ᵥ Q
 unfold dotProduct; rw [← Equiv.sum_comp e (fun x=> _*_ )]; simp only [Function.comp_apply, Equiv.symm_apply_apply]
lemma sail_down {I:Type*}[Fintype I](x:I→G.Color): colordown x ⬝ᵥ colordown x=sail x^2:=by
 rw [Tail.quadratic,dotProduct,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; rw [←real_inner_self_eq_norm_sq,inner_color]; rfl
variable (R:ℕ)
def drive(v:fieldDir G n 1) (C:Clip)(W: PathData G)(i:Twin n):G.Color:= if i.2 then curtailed W R i.1 v else Real.sqrt C.direct • faceCurl i.1 v
-- price pulse core(E)
def prize(E:Lots n)(C:Clip)(W:PathData G)(x:ListT G n):Twin n→G.Color:= fun j=> if j.1∈ E then drive R (tin x) C W j else 0
lemma applause (E:Lots n)(C:Clip)(W:PathData G)(x:ListT G n): pulse W C E R (tin x)=sail (prize R E C W x)^2:=by
 rw [Tail.quadratic,Fintype.sum_prod_type]; unfold pulse
 have he (b:Plane n): ∑ i:Bool, ‖prize R E C W x (b,i)‖^2= if b∈ E then pansy W R C b (tin x) else 0:=by
    unfold prize; split
    next hz=> rw [Fintype.sum_bool]; simp only [if_pos hz,drive,Bool.false_eq_true,↓reduceIte,pansy]; rw [norm_smul, mul_pow,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt C.quadratic_pos.le,add_comm] -- tune
    next hz=> simp [hz]
 simp_rw [he]; rw [←sum_filter]; congr; ext i; simp
variable (h: W.Bounds C σ X D)
include h
lemma trimmed_plus (x y:ListT G n)(b:Plane n): curtailed W R b (tin (x+y))= curtailed W R b (tin x)+curtailed W R b (tin y):=by
 unfold curtailed; rw [← (trim_sum h _ (tin x) R).tsum_add (trim_sum h _ (tin y) R)]; refine tsum_congr fun i=>?_ ; unfold trimmed; split; rw [add_zero]; rw [←smul_add]; congr 1; ext j
 rw [PiLp.add_apply,color_pi,color_pi,color_pi,show page (x+y) j=page x j+page y j from rfl,Matrix.mulVec_add,Pi.add_apply]
lemma trimmed_smul (x:ListT G n)(t:ℝ)(b:Plane n): curtailed W R b (tin (t • x))= t • curtailed W R b (tin x):=by
 unfold curtailed; rw [←tsum_const_smul'']; refine tsum_congr fun i=>?_ ; unfold trimmed; split; rw [smul_zero]; rw [smul_comm t]; congr 1; ext j; rw [PiLp.smul_apply,color_pi,color_pi,show page (t • x) j=t • page x j from rfl,Matrix.mulVec_smul,Pi.smul_apply] -- tune
-- store whole gram extends only for all links. minors via submatrix.
def roster (E:Lots n)(h: W.Bounds C σ X D) : ListT G n→ₗ[ℝ] Scene G (Twin n) where
 toFun:=colordown ∘ prize R E C W
 map_add' x y:=by
    funext i; change (prize R E C W (x+y) i.1) i.2= (prize R E C W x i.1) i.2+(prize R E C W y i.1) i.2; unfold prize; split
    next=> unfold drive; split; rw [trimmed_plus R h,PiLp.add_apply]; simp only [PiLp.smul_apply,color_pi]; rw [show page (x+y) i.2= page x i.2+page y i.2 from rfl, Matrix.mulVec_add, Pi.add_apply,smul_add]
    next=> simp
 map_smul' z x:=by
    funext i; change (prize R E C W (z • x) i.1) i.2= z • (prize R E C W x i.1) i.2; unfold prize; split
    next=> unfold drive; split; rw [trimmed_smul R h,PiLp.smul_apply]; simp only [PiLp.smul_apply,color_pi]; rw [show page (z • x) i.2=z • page x i.2 from rfl,Matrix.mulVec_smul, Pi.smul_apply,smul_comm]
    next=> simp
def tariff (E:Lots n)(h:W.Bounds C σ X D) := LinearMap.toMatrix' (roster R E h)
def flare (E:Lots n)(h:W.Bounds C σ X D) : Matrix (Pens G (EdgeT n)) (Pens G (EdgeT n)) ℝ:= (tariff R E h)ᵀ*(tariff R E h)
lemma flash_ok (x:ListT G n)(E:Lots n): x ⬝ᵥ (flare R E h*ᵥ x)= pulse W C E R (tin x):=by rw [flare, ←mulVec_mulVec, dotProduct_transpose_mulVec,tariff,LinearMap.toMatrix'_mulVec,applause]; exact sail_down _ -- tune
end YM.Hill.Box
#print axioms YM.Hill.Box.flash_ok
