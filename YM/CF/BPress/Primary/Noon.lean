import YM.CF.BPress.Primary.Ballad
/- final support cost. chooses hum anchors on each nonempty support. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Primary
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Brace Spire
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Voice
variable {s B m:Side}{N:Side}{A D C X Q K:Pledge}{U:Driver (CSide m B)} {a d k q p r b:ℝ}{G:Duet m B} (x:U.Pose)
def stageH : Harmony m B U.d U.p:= ⟨(x.val.G,x.val.X),x.property.glow,x.property.tuneK⟩
lemma tuneR : Continuous (stageH (U:=U)):= Continuous.subtype_mk ((Plain.cont_G.prodMk Plain.cont_X).comp continuous_subtype_val) _
variable {H : Hymn m B U.d U.p} (Y:Solo H G k Q.rate Q.price)
namespace Noon
variable {T:Support s}
def headT(T:Support s): Site s:= if h:T.Nonempty then h.choose else 0
lemma here_t (V:T.Nonempty): headT T∈T:=by rw [headT,dif_pos V]; exact V.choose_spec
abbrev hit (H : Hymn m B U.d U.p) (a:Tenor (More (CSide m B))):ℝ:=if headT a.2=a.1 then H.w a.2 else 0
abbrev hot_H (H : Hymn m B U.d U.p)(a:Tenor (More (CSide m B)))(x:U.Pose):ℂ:=if headT a.2=a.1 then Spire.zen (H.piece a.2 (stageH x)) else 0
include Y
variable (a:Tenor (More (CSide m B)))
lemma h_budget : Cash scaffold (hit H) Q.rate Q.price:=by -- drop N:=N?
 refine ⟨fun i=>ite_nonneg (Y.bills.pos _) le_rfl,fun x=>?_⟩; refine ⟨fun i=>?_ ,(hasSum_fintype _).summable,?_⟩; apply ite_nonneg; exact mul_nonneg (Real.exp_pos _).le (ite_nonneg (Y.bills.pos _) le_rfl); exact le_rfl
 rw [tsum_fintype]; apply le_trans _ (Push.AbsoluteSums.budget_sum (Y.bills.hits x) univ); rw [Fintype.sum_prod_type,sum_comm]; apply sum_le_sum; intro i _; by_cases q:x∈i; unfold Ledger.score; simp only [scaffold,id_eq,q,ite_true]; rw [←mul_sum]; unfold hit; simp only [sum_ite_eq', sum_ite_eq, mem_univ,ite_true,le_refl]; unfold Ledger.score; simp only [scaffold,id_eq,q,ite_false,sum_const_zero,le_refl]
lemma heat_ta : hit H a≠0→ a.1∈a.2 ∧ Grove (Grid.field 4 (More (CSide m B))) a.2:=by
 unfold hit; split; next h=> intro t; let x:= (Y.duet a.2).travel t; rw [←h]; exact ⟨here_t (Grid.inhabited_grove x), x⟩ -- tune dependency projection rw
 next h=> simp
lemma hit_n : ‖hot_H H a x‖≤ hit H a:=by
 unfold hot_H hit; split; next h=> apply le_trans _ ((Y.duet a.2).sumline (stageH x)); unfold Spire.zen; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact Complex.abs_im_le_norm _
 next h=> rw [norm_zero]
lemma hot_m : Measurable (hot_H H a):=by
 unfold hot_H; split; next h=> unfold zen; exact measurable_const.mul (Complex.measurable_ofReal.comp (Complex.measurable_im.comp (Continuous.measurable ((Y.duet a.2).cont.comp tuneR)))) -- tune
 next h=> exact measurable_const
lemma hot_read {y:U.Pose}(p:Along a.2 x.val y.val): hot_H H a x=hot_H H a y:=by
 unfold hot_H; split; next g=> rw [(Y.duet a.2).reads _ (stageH y) (show (Broc.pWorks m B U.d U.p).rel a.2 _ _ from ⟨p.up,p.rods⟩)]
 next g=> rfl
lemma hot_hold(g: Mach (More (CSide m B)))(V:Wish U A D C): hot_H H a (moveW x V g)=hot_H H a x:=by
 unfold hot_H; split; next h=> rw [show H.piece _ _=H.piece a.2 (stageH x) from ?_]; exact (Y.duet a.2).gauge (stageH x) g
 next h=> rfl
lemma hot_variation (P: Shell.plot q U.p U.d r k)(y:U.Pose)(Q: y.val.G=1) (V:Slow 1 (hook y.val.X) q) (S:Shell a.2 y.val.X x.val.G x.val.X b)(g:0<b)(z:b≤r): ‖hot_H H a x-hot_H H a y‖≤ hit H a * b := by
 have he:= soloH P (stageH x) (stageH y) S (Y.duet a.2) Q V g z; unfold hot_H hit; split; next h=> rw [←zen_a]; exact (by unfold zen; rw [norm_mul,Complex.norm_I,one_mul,Complex.norm_real]; exact (Complex.abs_im_le_norm _).trans he)
 simp
omit Y
lemma hot_imag : (hot_H H a x).re=0:=by unfold hot_H; split <;> simp [zen]
include Y
lemma hot_total : ∑ i:Tenor (More (CSide m B)), hot_H H i x=Spire.zen (Spire.hum m B G x.val.G x.val.X) :=by rw [Fintype.sum_prod_type,sum_comm]; unfold hot_H; simp_rw [sum_ite_eq,mem_univ,ite_true]; rw [show Spire.hum m B G x.val.G x.val.X=_ from (Y.prime (stageH x))]; unfold Spire.zen; rw [Complex.im_sum,Complex.ofReal_sum,mul_sum]
end Noon
end YM.CF.BPress.Primary
