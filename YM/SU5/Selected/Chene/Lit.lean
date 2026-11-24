import YM.CF.Neige.Stop
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bed
import YM.Push.FREE_RESOLVENT.AffineGap
import YM.SU5.Selected.Chene.Melody
import YM.SU5.Selected.Chene.Row
/-! Pricing the uncut flat Gram against the actual precut Gram used in the step preparation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Chene.Tail
open Function Filter Matrix Lattice Wilson RG Tree SectorNext.Vacuum.FlatTree Precision Exterior Finset
open Next Next.SectorChange Next.SectorChange.Flat Pressure Pressure.Stores
open CF.Neige CF.Newt CF.Char FreeResolvent Next.Fluctuations Push.SectorMeasure MeasureTheory
open Rows AnalyticBridge.LocalGaussianLaws
open Work.F03 Bid
open scoped Topology BigOperators Matrix InnerProductSpace MatrixOrder
variable {c f:Side}{S:StepData c f}{G:Gauge}
variable (F:Forest S.ratio)(T:Tube G S)(K:Bed)(q:S.Choices){σ E X D u x:ℝ}
variable (t:T.up.Bounds T.high σ E D)(h:S.patch.Branches S.kernel G)
include T
local notation "V" => S.kernel.penalty
open SectorNext.Vacuum
open Next.SectorChange.Flat
omit T
lemma packer(v: Key F G→ℝ)(x:ℝ): Next.SectorChange.Flat.labels (CF.Char.trays S x F v)=stretch (S:=S) F (0, FreeResolvent.profile F v):=by
 let g:= stretch (S:=S) F (0,FreeResolvent.profile F v); let w:=CF.Char.trays S x F v; funext i; obtain ⟨⟨i,j⟩,rfl⟩:=(wheel f).surjective i; let e:=(i,j)
 change Next.SectorChange.Flat.labels w (wheel f (i,j))=collect G g (i,j); rw [wheel_app, show Next.SectorChange.Flat.labels w (i,coord j)=w (i,j) from ?_]; swap; · unfold labels; rw [show axisEquiv.symm (coord j)=j from axisEquiv.symm_apply_apply _]
 rw [show collect G g (i,j)=_ from Work.F01.collect_vertical ..]; rw [show w= _ from trays_b v]; unfold blank; split; rfl; rfl
include T t h
lemma vision (x:ℝ)(v:Key F G→ℝ): let W:= testD F T x q; sail (slip • bump T x 1 q (CF.Char.trays S x F v))^2 = v ⬝ᵥ (Wᵀ*W)*ᵥ v :=by
 classical
 intro W; rw [←mulVec_mulVec,Matrix.dotProduct_transpose_mulVec W,Next.SectorChange.price_square]; rw [show W *ᵥ v= _ from around F v]; simp_rw [moved _ _ _ _ _ _ _ t, selected_all T _ _ _ _ _ _ h,MeasurableEquiv.apply_symm_apply]; rw [quadratic] <;> rfl
section
include q
lemma radii (s:Signed)(u:Dir G f): (∑ i: Bond c, ‖zLin S (pulled u s) 0 i‖^2) = S.kernel.penalty* ∑ b, inner ℝ (bills S u b) (bills S u b):=by
 let D:= bills S (pulled u s); let U:= pulled (bills S u) s; have hx(i:Bond c): D (pole i)=U (pole i):= Next.SectorChange.Flat.bills_signed S s q i u h
 have hh:=FreeResolvent.Affine.pulled_inner s (bills S u) (bills S u); rw [flat_dot,flat_dot] at hh
 have he (a:Bond c): ‖zLin S (pulled u s) 0 a‖^2= V * inner ℝ (U (pole a)) (U (pole a)):=by rw [← hx]; unfold zLin; change ‖(_ :ℝ) • (0-D _)‖^2= _; rw [zero_sub,norm_smul,norm_neg,Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,Real.sq_sqrt S.kernel.penalty_pos.le, real_inner_self_eq_norm_sq]
 simp_rw [he,←mul_sum,←hh]; congr 1; exact Equiv.sum_comp (Work.E03.poleEquiv c) (fun x=> inner ℝ (U x) (U x))
variable (p:Attached K T.up)(a:Floor K T.high f X u)(s: Bid.Sworn K f G)
include p a s
lemma melody_s (w:Directions G f)(x:Signed): let v:= Next.SectorChange.Flat.labels w; ∑ i, ‖Next.SectorChange.Flat.ideal T w (x,i)‖^2=dotProduct (flatten v) (fullMatrix G S K.metric*ᵥ flatten v):=by
 intro v; let W:= pulled v x; rw [Fintype.sum_sum_type,fiscal_eq]; change (∑ i:Twin f, ‖xLin T.high T.up W i‖^2)+_= _ -- precedence need parens
 have hp: ∑ i:Twin f, ‖xLin T.high T.up W i‖^2= curlCharge K.metric v v := by
    rw [Fintype.sum_prod_type]; change _=gaugeFiscal K v v; rw [← s x v v, metric_pair K t p (pulled v x) (pulled v x) a]; apply sum_congr rfl; intro i _; rw [Fintype.sum_bool]; unfold xLin; simp [norm_smul, abs_of_nonneg (by positivity:(0:ℝ) ≤ Real.sqrt T.high.direct),mul_pow,Real.sq_sqrt T.high.quadratic_pos.le,W,v,add_comm]
 rw [hp,show ∑ i:Bond c, ‖ideal T w (x,.inr i)‖ ^ 2= _ from radii T q t h x v] -- implicit F T?
omit p a s T t h q in
lemma slip_square : slip^2 *(Fintype.card Signed:ℝ)=1:=by
 unfold slip; have hx:0<(Fintype.card Signed:ℝ):=Nat.cast_pos.mpr Fintype.card_pos; rw [inv_pow, Real.sq_sqrt hx.le, inv_mul_cancel₀ hx.ne']
lemma brilliant (x:ℝ)(v: Key F G→ℝ): sail (slip • Next.SectorChange.Flat.ideal T (CF.Char.trays S x F v))^2 = v ⬝ᵥ treeMatrix G S F K.metric *ᵥ v:=by
 let W:= CF.Char.trays S x F v; let Y := Next.SectorChange.Flat.labels W; let R:=flatten Y; let K':= treeMatrix G S F K.metric
 have he:R ⬝ᵥ fullMatrix G S K.metric *ᵥ R=v ⬝ᵥ K' *ᵥ v:=by unfold R Y W; rw [packer]; exact (tree_qf S F K.metric (profile F v) (profile F v)).symm
 rw [carries, mul_pow,Tail.quadratic,Fintype.sum_prod_type]; simp_rw [melody_s T K q t h p a s (CF.Char.trays S x F v)]; -- melody_s F T?
 rw [sum_const, card_univ,nsmul_eq_mul, ← _root_.mul_assoc, sq_abs,slip_square,_root_.one_mul]; exact he
end
end YM.Chene.Tail
#print axioms YM.Chene.Tail.brilliant
