import YM.CF.Graph.Coif
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Nacre Font Pec
variable {n:Side}{v h b a:ℝ}{p:BudgetPoint}
structure HelpP (U:Bkg (More n))(e a:ℝ):Prop where
 fee (s:Signed)(x:Pec.Orig n)(j:Pec.Ok n):‖silt x j (Yg (incX s) U)‖ ≤ e* Real.exp (a*dial x j)
lemma railT(U:Pane n)(r:ℝ)(p:0≤r): HelpP U 2 r:=⟨fun s x j=> ((group.curvature_norm _).trans (group.chord_le_two _)).trans (le_mul_of_one_le_right (by norm_num) (Real.one_le_exp (by positivity)))⟩
lemma tile_p(U:Pane n)(w:v≥0)(r:0≤a)(g:flags v U=∅): HelpP U (v+2*Real.exp (-(a*(More n).val))) a:=by
 let N:=More n; let D:=v+2*Real.exp (-(a*N.val))
 constructor; intro s x j; let Y:= Yg (incX s) U
 cases j with
 | inl i=>
    have hp : flags v Y=∅:=by
       rw [show Y= _ from (show Y=pull s 0 U from Ywin s U)]
       have he:= Work.H03.flags_send (U:=U) -- tune
       simpa using (he s 0 v).trans g
    let y:=i.1; let P:Face (Per (More n)):= i; have he: group.chord (faceValue Y P) ≤ v:=by
       by_contra! t; have hf:y∈flags v Y:= (flags_spec ..).mpr ⟨P,by simp [P,RG.touched,visits,square,y],t⟩; rw [hp] at hf; exact Finset.notMem_empty _ hf
    apply (group.curvature_norm _).trans; let T:=shiftH x y; have ht:stop x T=y:=stopH ..; rw [boot, travel_append,travel_append,stop_append]; simp_rw [show stop x (shiftH x i.1)=i.1 from ht,square_stop]; rw [show travel Y i.1 _= _ from (show travel Y y (reverse T)=(travel Y x T)⁻¹ from (by nth_rw 1 [←ht]; rw [travel_reverse]))]; rw [group.chord_conj]; exact he.trans ((by unfold D; positivity : 0≤D)|> fun t=>le_trans (le_add_of_nonneg_right (by positivity)) (le_mul_of_one_le_right t (Real.one_le_exp (by positivity))))
 | inr i=>
    apply (group.curvature_norm _).trans; apply (group.chord_le_two _)|>.trans; rw [add_mul]; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg w (Real.exp_pos _).le)); change _≤ 2*Real.exp _ * Real.exp (a*(More n).val); rw [mul_assoc, ← Real.exp_add, neg_add_cancel,Real.exp_zero,mul_one]
lemma HelpP.rise(U:Pane n)(q: HelpP U b a)(k:a≤v)(e:b≤h)(g:0≤b):HelpP U h v:=⟨fun s x j=>(q.fee s x j).trans (by gcongr; exact g.trans e)⟩
end YM.CF.Graph
