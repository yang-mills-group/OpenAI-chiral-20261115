import YM.CF.BPress.Sea.Fizz
/- Real primary spec. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Nougat
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Pec Spin SpinSign Spin.Pledge Pledge.Costs Cube Lat SU Spin.Paint Nacre Laic Font Push.AbsoluteSums.Paths Tulip Tenant Dial Scroll Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper
attribute [local instance] opCStarAlgebra
variable {N:Side}(W:Pride N) (p:Post N)
local notation "₴"=> (Spark.card_page:ℝ)
def stencilℂ (σ:Signed)(A:Op (Single N)):= if Spire.detX σ then cc A else A
def opR(W:Pride N)(σ:Signed)(A:Post N):= (₴)⁻¹ • stencilℂ σ ((layer W (Yg (incX σ) A)).submatrix (names σ⁻¹ _) (names σ⁻¹ _))
abbrev mass_pr:= (Fintype.card Signed:ℝ)⁻¹
def pearls(W:Pride N)(A:Post N): Op (Single N):= mass_pr • (∑ i:Signed, opR W i A)
lemma pearl_motion(g:Mach (More N)): pearls W (gauge g p)= pearls W p:=by
 have he (i:Signed): layer W (Yg (incX i) (gauge g p))=layer W (Yg (incX i) p):= by unfold layer; rw [Nacre.van]; simp_rw [Pec.tag_g]
 unfold pearls opR; simp_rw [he]
variable (H:Pledge)
def bracelet_price(H:Pledge):Pledge:= (tax H).scales ‖(₴)⁻¹‖
def ζPearl:= ((bracelet_price H).scales (Fintype.card Signed)).scales ‖mass_pr‖
theorem ΞPearl (c:Lac W H.rate H.price): (ζPearl H).Costs (Sifting.outlook N).stage (pearls W):=by
 refine Pledge.Costs.scale (Pledge.Costs.sums (opR W) ?_) mass_pr; intro i; unfold bracelet_price; apply Pledge.Costs.scale; let p:= SpinSign.reindexing (i⁻¹) (cobase W H c); rw [inv_inv] at p; unfold stencilℂ; split; exact Pledge.Costs.stars p; exact p -- tune ^-1
private lemma contour_op(i:Signed) (S:Op (Single N)): (stencilℂ i S).trace=Pec.pays i S.trace:=by rw [Pec.complX]; unfold stencilℂ; cases h:Spire.detX i; rfl; exact (by simp [h,Matrix.trace,Matrix.diag,cSignX,Complex.conjCLE]) -- tune h cases
lemma layerR : (layer W p).trace=₴ • (Pec.zinger W p):=by
 let f(x):= Pec.tag (node x) (W x) p; let W(i:Single N):= f i.1.1; rw [layer,Matrix.trace_diagonal]; change (∑ i:Single N,W i)= ₴ •∑ i, f i; rw [← sum_fiberwise univ (Bias.penX (N:=N)) W]; simp_rw [Finset.smul_sum]; apply sum_congr rfl; intro i h; change (∑ x∈ Chalk.den i,W x)=_; rw [sum_congr rfl (g:=fun _=>f i) (fun j e=> congrArg f ((mem_filter.mp e).2)),sum_const,Spark.cardsJ]; exact (Nat.cast_smul_eq_nsmul ℝ _ _).symm -- tune
lemma pigment_c : pigment W p=(pearls W p).trace:=by
 unfold pigment lexn pearls; rw [Matrix.trace_smul,Matrix.trace_sum]; apply congrArg; apply sum_congr rfl; intro i _; rw [opR,Matrix.trace_smul,contour_op, show Matrix.trace _=Matrix.trace (layer W (Yg (incX i) p)) from ?_,layerR,map_smul]; rw [inv_smul_smul₀ (by unfold Spark.card_page; positivity : ₴≠0)]; -- tune
 exact Equiv.sum_comp (names i⁻¹ N) (fun j=> layer W (Yg (incX i) p) j j) -- tune
end YM.CF.BPress.Nougat
