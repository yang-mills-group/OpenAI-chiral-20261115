import SatinThinWaves
import SatinThinSpoon
import SatinThinFlakes
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Pannier.Damask
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier Fixed.Extensive Pannier.Chancel Papyrus.Franc
variable {j m d r:ℕ}{N:Side}{A0:Loom N}{D β γ a C R δ v u t g:ℝ}
lemma cap_spend (W:Colts j N g R δ) (h:0 ≤ R) (U:Orbit N)(H: Roof N u t r A0)(T:t≤δ)(M:Tulip.Male)(L_:Op (Single N))(J:IsStarProjection (spar j M (A0 U))) : revE (Kennel.capT (spar j M (A0 U)) L_) ≤ ((1+R)*R*revE L_):=by
 let P:=spar j M (A0 U); let Z:= 1-P; have hz(i): ∑ k:Single N, ‖P k i‖ ≤ R:= W.c _ _ ((H.paid U).shrink T) _; change revE (Z*L_*P)≤_
 have he (i:Single N): (∑ k:Single N,‖P i k‖)=(∑ k:Single N, ‖P k i‖):=sum_congr rfl fun j _ => by nth_rw 1 [←(show star P=P from J.isSelfAdjoint)]; simp [Matrix.star_apply]
 apply (rev_tunders P _ R (fun i=> (he i).trans_le (hz _))).trans; have hp(i: Single N): (∑ k:Single N, ‖Z k i‖) ≤ 1+R:=by
    apply le_trans (b:= ∑ k:Single N,(‖(1:Op (Single N)) k i‖+‖P k i‖)) (sum_le_sum (fun j _=> norm_sub_le ..)) ?_; rw [sum_add_distrib]; apply add_le_add ?_ (hz i); simp [Matrix.one_apply,apply_ite (fun x:ℂ=>‖x‖)] -- tune
 refine (mul_le_mul_of_nonneg_left (rev_stock Z L_ _ hp) h).trans_eq ?_; ring
lemma arbor_foil (T:Toy m N)(p:CardK N m T C a)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e): revE (colorX T (A0 U)) ≤ 180^2 * storm U v e r d C m:=by
 let f(i:Signed):= Nacre.foil i (cavil T) (A0 U); let X:=Fintype.card Signed; have hX : (X:ℝ) >0:= by unfold X; exact_mod_cast Fintype.card_pos
 let A:=180^2*storm U v e r d C m; have he(s':Signed):revE (f s')≤ A:=(rev_foil ..).trans (mul_le_mul_of_nonneg_left (bolt_law U g ℓ s w l T p c e q s'⁻¹) (by positivity)) -- tune
 change revE ((X:ℝ)⁻¹ • ∑ i:Signed,f i)≤ A; rw [rev_smul, abs_of_nonneg (by positivity : 0≤(X:ℝ)⁻¹)]; apply (mul_le_mul_of_nonneg_left ((rev_storm ..).trans (sum_le_sum fun i _=> he i)) (show 0 ≤ (X:ℝ)⁻¹ from by positivity)).trans
 rw [sum_const,card_univ,nsmul_eq_mul]; exact (inv_mul_cancel_left₀ hX.ne' _).le
lemma revAct_b (R':GramM N)(L:Ledger D β γ a C R')(c:0≤C)(U:Orbit N)(g':Roof N u t r A0)(Q:t ≤ δ)(W:Colts j N g R δ)(p:IsStarProjection (spar j R'.J.M (A0 U)))(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(h:0≤R) : revE (actF j R' A0 U) ≤ 180^2*((1+R)*R)*(storm U v e r d C 1+storm U v e r d C 2):=by
 unfold actF Aim.den; rw [Pi.add_apply]; obtain ⟨A,B⟩:= L.field.1; apply (cap_spend W h U g' Q _ _ p).trans; refine (mul_le_mul_of_nonneg_left ((rev_add ..).trans (add_le_add (arbor_foil _ A U g' ℓ s w l c e q) (arbor_foil _ B U g' ℓ s w l c e q))) (by positivity : 0≤(1+R)*R)).trans_eq ?_; ring
end YM.CF.Pannier.Damask
#print axioms YM.CF.Pannier.Damask.revAct_b
