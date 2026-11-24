import YM.CF.BProof.Mote.Glow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker Classical
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
namespace TripD
variable (j:ℕ) {n:ℕ}
variable (x:Bkg (More P))(y:Bkg (More N))(M:Male)
def turret (V:Bkg (More P)):= Peaks.cloth j M G (flag N V)
lemma flag_y (W Z:Coil N P)(u:W.1=Z.1)(a b:St G.count)(x:Cover)(i:ℂ)(o:Lattice.Order) :drag G true false a b x i o W= drag G true false a b x i o Z:=by unfold drag; rw [u]
lemma bonus_b (W Z:Coil N P)(u:W.1=Z.1)(f: Track G.count): mosaic G true false f W=mosaic G true false f Z:=by unfold mosaic douse; simp_rw [flag_y G W Z u]
lemma turret_eq: Peaks.cloth j M G (unionP (x,y))=turret G j M x:=by
 unfold turret Peaks.cloth; simp only; rw [bonus_b G (unionP (x,y)) (flag N x) rfl]
variable (ho:Odd G.count.val) (v:SetK j G.count n)
def plotCap (L:Side)(j:ℕ)(h: Odd L.val): Finset ℕ:=plot (Classical.choose (BasisRim.Sheet.sound L j h))
lemma many (o:Lattice.Order) : douse G true false (tub (brix j G.count)) o (flag N x)= ∑ r:St G.count,∑ t:St G.count,∑ i∈plotCap G.count j ho, drag G true false r t (names i) (tub (brix j G.count) (names i) r t) o (flag N x):=by -- remove a b
 unfold douse; refine sum_congr rfl fun a _=> sum_congr rfl fun b _=> tsum_eq_sum (fun i (u:i∉ plotCap G.count j ho)=>?_) -- tune args
 rw [(BasisRim.Sheet.sound G.count j ho).choose_spec (names i) (fun h=> u (Finset.mem_image.mpr ⟨_,h,names.symm_apply_apply _⟩))]; ext i' l; unfold drag panel; simp only [Matrix.sum_apply, Matrix.of_apply, Matrix.zero_apply,mul_zero,zero_smul,ite_self,sum_const_zero]
include ho v
lemma mosaicD (i l:Iota G): Portray G i l (units G.count n) (fun x=>mosaic G true false (tub (brix j G.count)) (flag N x) i l):=by
 unfold mosaic; simp only [Matrix.smul_apply, many G j _ ho, Matrix.sum_apply,Complex.real_smul]; apply Portray.mint; refine Portray.pool _ _ (fun o _=> Portray.pool _ _ (fun r _=> Portray.pool _ _ fun t _=> Portray.pool _ _ fun s _=> paint_t G j ho v r t _ o i l))
lemma affordable(M:Male)(i l:Iota G): Portray G i l (units G.count n) (fun x=> turret G j M x i l):=by
 let f(x):= mosaic G true false (tub (brix j G.count)) (flag N x)
 have hp(b:Bool): Portray G i l (units G.count n) (fun x=> (lobe G b*f x*lobe G b) i l):=by convert (mosaicD G j ho v i l).mint (lobe G b i i*lobe G b l l) using 1; funext x; nth_rw 1 [lobe_diag G b]; nth_rw 2 [lobe_diag G b]; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; unfold f; ring
 exact Portray.plus (hp true) (hp false) -- D-fin
lemma turbine (M:Male): Continuous (turret G j M):=by apply continuous_pi; intro i; apply continuous_pi; intro l; exact (affordable G j ho v M i l).cont
end TripD
end YM.CF.Peaks
