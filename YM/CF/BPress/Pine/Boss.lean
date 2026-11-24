import YM.CF.BPress.Pine.Cabin
import YM.CF.BPress.Scale
/- API for lem:B-PfC. finite all inputs, uniform x delay by Stakes.calibration. Actual shape values can insert ANY permitted ordering of the selected lists; `totalU` reads them thru true intrinsic shape via `.projection`. Need trajectory issue O-expect from this API. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pine
open Function Filter NormedSpace MeasureTheory Finset Lattice Branch Ledger Push.AbsoluteSums Ursell Palmer Fock Pastry Pf EdgeD
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical
open Story
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]
variable {B J:Type}[Fintype B][DecidableEq B][Fintype J][DecidableEq J]
variable {a μ κ C z e:ℝ}{s:Side}
abbrev look_field (s:Side):= Grid.field 4 s
variable {P:EdgeD I B (Site s) (look_field s)}(S:Story J P)(T:J→ℝ)(b:B→ℝ)
abbrev Ξ(a:ℝ):= a+a+(a+a)
structure Slogan (σ μ a c:ℝ):Prop where
 h:0<σ
 v:0<μ
 u:0<c
 cap:Ξ μ ≤ min a σ
 buys: Stakes 1 μ (till_cost 1 (cPay σ*c))
 awake: Stakes 1 (μ+μ) (cPay σ*c)
abbrev logArc (σ κ:ℝ):= till_cost 1 (till_cost 1 (cPay σ*κ))
theorem issue (c:Slogan κ μ a z)(H:Enorm P (κ+κ) C b)(g:Cash S.base (fun i=>ahead S (T i) i (1+C)) a z)(t:J→ℂ)(f:B→ℂ)(l:∀ i,‖f i‖ ≤ b i)(h:∀ i,‖t i‖ ≤ T i) : S.table f t= Complex.exp (∑ p:Support s,S.report f t p) ∧ (∀p, ‖S.report f t p‖≤ S.taxes b T p)∧ Cash id (S.taxes b T) μ (logArc κ z) ∧ ∀p,S.taxes b T p≠0→ Grove (look_field s) p := S.B_PfC b T f t (FoldUnit s) H (g.chill (c.cap.trans (min_le_left ..))) c.buys (root_earn c.h s) c.awake c.u.le le_rfl (c.cap.trans (min_le_right ..)) (fun i=> (norm_nonneg _).trans (h _)) l h -- tune order
lemma art (u:ℝ→ℝ)(b:ℝ→ℝ)(v:NPL u)(s:∀ᶠ x in atTop,0<u x)(k:∀ᶠ x in atTop,0 < b x)(t:PL fun x=>(b x)⁻¹) (h:0<κ) : let f(x:ℝ):= (min (b x) κ)/4; PL (fun x=>(f x)⁻¹)∧ NPL (fun x=> logArc κ (u x))∧∀ᶠ x in atTop,Slogan κ (f x) (b x) (u x) :=by
 intro f; have hp : PL (fun x=> (f x)⁻¹):= by apply (((PL.const 4).mul (t.add (PL.const κ⁻¹)))).mono; filter_upwards [k] with x p; unfold f; rcases le_or_gt (b x) κ with t|t; rw [min_eq_left t,inv_div, abs_of_nonneg (by positivity : (0:ℝ)≤ _ / b x)]; apply (show 4/b x ≤4*((b x)⁻¹+κ⁻¹) from by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr h]).trans (le_abs_self _); rw [min_eq_right t.le,inv_div, abs_of_nonneg (by positivity : (0:ℝ)≤ _/κ)]; apply (show 4/κ ≤4*((b x)⁻¹+κ⁻¹) from by rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr p]).trans (le_abs_self _)
 have hg: NPL (fun x=>till_cost 1 (cPay κ*u x)):= ((v.const_mul (cPay κ)).const_mul (↑(1:Side).val)).const_mul _; refine ⟨hp,(hg.const_mul ((1:Side).val:ℝ)).const_mul _,?_ ⟩; let r(x):= till_cost 1 (cPay κ * u x); filter_upwards [k,s,(hg.mul hp).drop.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/8))] with x h' s v; change r x*(f x)⁻¹ ≤ _ at v; have ht:0<f x:=div_pos (lt_min h' h) (by norm_num); have hr:=root_κ h; let p:= cPay κ*u x; have e:0<p:= by unfold p; positivity
 have hz:r x=p+p:=by unfold r p till_cost; norm_num; ring
 have hx: Ξ (f x)=min (b x) κ:=by unfold Ξ f; ring
 rw [←div_eq_mul_inv, div_le_iff₀ ht] at v; refine ⟨h,ht,s,hx.le,⟨ht,show 0<r x from (by linarith),?_⟩,⟨add_pos ht ht,e,?_⟩⟩; all_goals rw [PNat.val_ofNat, Nat.cast_one]; all_goals first| (change (1:ℝ)* r x *8 ≤ _; linarith)| (change (1:ℝ)*p*8≤ _; linarith only [hz,e,v,ht]) -- tune casts
end YM.CF.BPress.Pine
#print axioms YM.CF.BPress.Pine.issue
