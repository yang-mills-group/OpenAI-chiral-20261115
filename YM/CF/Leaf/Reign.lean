import YM.CF.Leaf.Veer
import YM.CF.Leaf.Jive
import YM.CF.Vow.Asset
set_option synthInstance.maxSize 24000
open YM.CF
attribute [local instance] opCStarAlgebra
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
variable {N:Side}{X Y Z:Aura N}{δ:ℕ}(K:Rinse (Seat N) (Copy N)){Γ: Aura N→ℝ}{M:Orbit N→ Aura N→ FC (Dwell N)}{H:ℝ}{P:BudgetPoint} (T:Pitch P H δ K Γ M)
abbrev go_K {X:Aura N}(Y:Aura N):= K X ∅ Y
abbrev Span_K (P:BudgetPoint)(H:ℝ)(X:Aura N)(F:Copy N)(l:ℝ):Prop:= Medal P X.val ∅ F H l
variable{a b c v w:ℝ}(hv:1 ≤ H)
include T hv
lemma pen_K (F:Copy N)(x:Y.val⊆X.val)(w:Span_K P H X F c): Span_K P H X (go_K (X:=X) K Y F) (Γ Y*c):=by
 refine (T.plays X ∅ (empty_subset _) Y x c F ⟨w,fun i q=>?_⟩).merit
 refine ⟨?_,empty_subset _⟩; simp [Lattice.halo] -- tune
abbrev ξA (X:Aura N) := go_K (X:=X) K X 1
abbrev ζA (X Y:Aura N)(F:Copy N):= let Z:=αK X Y; go_K (X:=Z) K X F-F*(go_K (X:=Z) K X 1) -- orientation
abbrev κA (X Y Z:Aura N)(F G:Copy N):= let V:=αK (αK X Y) Z; let K' :=go_K (X:=V) K X; (2:ℝ)⁻¹ • (((K' (F*G)- F*K' G) - G*K' F) + G* F*K' 1) -- minus rhs.B. goes formula 
lemma hoof_L {F G:Copy N}{c d:ℝ}(p:Span_K P H Y F c)(q:Span_K P H Z G d) : let L:= Vow.Medal P X.val ∅ (ξA K X) H (Γ X); L ∧ Span_K P H (αK X Y) (ζA K X Y F) (Γ X*c*2)∧ Span_K P H (αK (αK X Y) Z) (κA K X Y Z F G) (2*Γ X*c*d):=by
 intro L'; let V':=αK X Y; let W:= αK V' Z; have hx:X.val⊆V'.val:=subset_union_left; have hy:Y.val⊆ V'.val:=subset_union_right; have hw:V'.val⊆ W.val:=subset_union_left; have hk:Z.val⊆ W.val:=subset_union_right; have he:0 ≤ H:=zero_le_one.trans hv
 have hp{X Y:Aura N}{F:Copy N}{v:ℝ}(t:X.val⊆Y.val)(p:Span_K P H X F v):Span_K P H Y F v:= p.stretchB t le_rfl (sdiff_subset_sdiff t le_rfl)
 have ht{Y:Aura N}(y:X.val⊆Y.val):=pen_K K T hv 1 y (show Medal P Y.val ∅ (1:Copy N) H 1 from Medal.oneT); let U:=hp hy p; let Z:= hp hw U; let Yv:=hp hk q -- Z notation shadow implicit in ζA X Y uses variables.
 refine ⟨by simpa only [mul_one] using ht (show X.val⊆X.val from subset_refl _),?_,?_⟩
 · unfold ζA; rw [sub_eq_add_neg]; exact (pen_K K T hv F hx U|>.plus ((U.cross (ht hx) he).negT)).big (le_of_eq (by ring))
 dsimp only [κA]; rw [sub_eq_add_neg,sub_eq_add_neg]; let J:= hx.trans hw; exact (((pen_K K T hv _ J (Z.cross Yv he)).plus ((Z.cross (pen_K K T hv _ J Yv) he).negT)|>.plus ((Yv.cross (pen_K K T hv _ J Z) he).negT)|>.plus ((Yv.cross Z he).cross (ht J) he) |>.rum ((2:ℝ)⁻¹)).big (le_of_eq (by rw [Real.norm_of_nonneg (by positivity)]; ring)))
lemma palm_S(Y:Aura N):Span_K P H Y (ξA K Y) (2*Γ Y):=(hoof_L K T hv (X:=Y) (p:= show Span_K P H Y 0 0 from Medal.zeroT) (q:=show Span_K P H Y 0 0 from Medal.zeroT)).1.big (by linarith [(show 0 ≤ Γ Y from T.dice _)]) -- named p.Arg issue
lemma pen_A(F:Copy N)(v:Span_K P H Y F c)(T':True):Span_K P H (αK X Y) (ζA K X Y F) ((2*Γ X)*c):= ((hoof_L K T hv (X:=X) v (q:= show Span_K P H X 0 0 from Medal.zeroT)).2.1).big (le_of_eq (by ring))
omit T hv
-- Algebra financial.Sensor.coherence without masks
lemma rind_L(M:FC ι)(Y:Dough ι):Sault.rind (Y.val*M)=Y.val*Sault.rind M:=by
 apply Sault.sky (Sault.skit _) (Scree.spanT (fineShape Y).allP (Sault.skit _)); rw [tileL,act_mul,act_mul,tileL]
variable (x:Orbit N)(z: Rue.FleetS P.threshold x.1)(u:flags P.threshold x.1=∅) 
include T z u hv
lemma spark_U {F: Copy N}(w:Span_K P H X F c)(p:Y.val⊆X.val): (go_K (X:=X) K Y F x).val=Sault.rind (M x Y*(F x).val):=by
 have h: flags P.threshold x.1∩ X.val=∅:=by rw [u,empty_inter]
 let Q:= T.body X Y x z p c F; dsimp only at Q; rw [h] at Q; exact Q ⟨w,fun i u=> ⟨by simp [Lattice.halo],empty_subset _⟩⟩
lemma Ω_Q (X:Aura N): (ξA K X x).val=Sault.rind (M x X):=by
 rw [ξA,spark_U K T hv x z u (show Span_K P H X 1 1 from Medal.oneT) le_rfl]; change Sault.rind (M x X * 1)=_; rw [mul_one]
lemma Ω_u (F:Copy N)(Y X:Aura N)(p:Span_K P H Y F c): (ζA K X Y F x).val=Sault.rind (bump (M x X) (F x).val):=by
 let V:=αK X Y; have hu:X.val⊆V.val:= subset_union_left; have hp:= spark_U K T hv x z u (show Span_K P H V 1 1 from Medal.oneT) hu; rw [show ((1:Copy N) x).val=1 from rfl, mul_one (M x X)] at hp; have hl:Y.val ⊆V.val:=subset_union_right
 change (go_K (X:=V) K X F x).val-(F x).val*(go_K (X:=V) K X 1 x).val= _; rw [hp,spark_U K T hv x z u ((show Span_K P H V F c from p.stretchB hl le_rfl (sdiff_subset_sdiff hl le_rfl))) hu]; unfold bump Sault.rind; rw [map_sub,show (cane (Dwell N)).eval ((F x).val*M x X)= _ from rind_L (M x X) (F x)]
omit T z u hv
lemma bump_r(A:FC ι)(B C:Dough ι): bump (bump A B.val) C.val=A*(B.val*C.val)- B.val*(A*C.val)-C.val*(A*B.val)+C.val*B.val*A:=by
 unfold bump; rw [sub_mul,mul_sub]; simp only [mul_assoc]; abel
lemma rime_z(A:FC ι)(t:ℝ):rind (t • A)= t • rind A:=by
 let F:= (Pastry.cane ι).eval.restrictScalars ℝ; change F (t • A)= t • F A; rw [map_smul]
include T z u hv
lemma Ω_c (F G:Copy N)(Y Z X:Aura N)(p:Span_K P H Y F c)(q:Span_K P H Z G b): (κA K X Y Z F G x).val=Sault.rind ((2:ℝ)⁻¹ • bump (bump (M x X) (F x).val) (G x).val):=by
 let V:=αK X Y; let W:=αK V Z; have hx:X.val⊆V.val:=subset_union_left; have hy:Y.val⊆V.val:=subset_union_right; have hV:V.val⊆W.val:=subset_union_left; have hu:Y.val⊆W.val:=hy.trans hV; have ha:X.val⊆W.val:=hx.trans hV; have hb:Z.val⊆W.val:=subset_union_right; let L:= go_K (X:=W) K X
 let F':Span_K P H W F c:=p.stretchB hu le_rfl (sdiff_subset_sdiff hu le_rfl); let L':Span_K P H W G b:=q.stretchB hb le_rfl (sdiff_subset_sdiff hb le_rfl);
 let H'(U:Copy N)(d:ℝ)(u':Span_K P H W U d): (L U x).val=Sault.rind (M x X*(U x).val):=spark_U K T hv x z u u' ha
 rw [rime_z] -- tune section includes. 
 change (2:ℝ)⁻¹ • ((L (F*G) x).val - (F x).val*(L G x).val- (G x).val*(L F x).val+(G x).val*(F x).val*(L 1 x).val) = _
 rw [H' _ _ ((F').cross L' (zero_le_one.trans hv)),H' G _ L',H' F _ F',H' 1 1 (show Span_K P H W 1 1 from Medal.oneT),show ((1:Copy N) x).val=1 from rfl,mul_one (M x X),bump_r] -- tune.W.p implicit
 unfold Sault.rind; simp_rw [map_add,map_sub]; rw [show (Pastry.cane _).eval ((F x).val*(M x X*(G x).val))= _ from rind_L ..,show (Pastry.cane _).eval ((G x).val*(M x X*(F x).val))=_ from rind_L ..,show (Pastry.cane _).eval ((G x).val*(F x).val*M x X)= _ from rind_L _ (G x*F x)]; rfl
end YM.CF.Leaf
