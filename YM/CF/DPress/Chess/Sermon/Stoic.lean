import YM.CF.DPress.Chess.Sermon.Prong
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
structure Scope (L:Side)(K:Ratio n m)(S:StepData (More n) (More m))(P:Loom n)(ℓ d:ℕ):Prop where
 medi : K.count=L
 odd : Odd L.val
 hl : 4 ≤ L.val
 generalS : S.ratio=ratio K
 kernel : S.patch.Branches S.kernel SU.group
 reach : S.patch.J=4
 fix : S.patch.L=L
 goodP : ∃ (k:ℝ)(u:ℝ)(r:ℕ), Wall.wage d r ≤ ℓ ∧ Roof n k u r P ∧ Firm P k r
variable {L:Side}(X: Scope L K S P ℓ d)
namespace Scope
lemma fee_m(X:Scope L K S P ℓ d) : Measurable P:=by obtain ⟨k,u,r,p,q,f⟩:= X.goodP; exact q.bill
include X in
lemma ready : Nonempty (Forest (ratio K)):= Tree.select _ (show Odd K.count.val from X.medi.symm ▸ X.odd)
variable [Nonempty (Forest (ratio K))]
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V][MeasurableSpace V][BorelSpace V][SecondCountableTopology V]
local notation "R_" => W.crop n Wall.rail
local notation "Q_" => W.crop n ℓ
local notation "ΨA"=> W.boost K.count
include X
lemma journal {A:Fold K V}(h:Envelope A)(v:Hi W ℓ A)(x:Stage m): LocalOn (R_) (sum_T P A x) :=by
 obtain ⟨k,u,r,p,q,f⟩:= X.goodP; exact fun i j hq=> ears x i j (knowingX W v x) f X.fee_m h hq (agrees_mono hq (Finset.coe_subset.mpr (W.smart p _))) -- tune
lemma journey {A:Fold K V}(h:Envelope A)(v:∀ x:Stage m,Uses (fun z=> A (x,z)) (page_M K (W.negZ (R_)) (W.negZ (Q_))))(x:Stage m): LocalOn (W.negZ (R_)) (sum_T P A x):=by
 obtain ⟨k,u,r,p,q,f⟩:= X.goodP; intro i j l; apply ears x i j (v _) f X.fee_m h l; apply agrees_mono l (Finset.coe_subset.mpr (W.negativity (by have ht:= Wall.Lot_h p; omega) n))
lemma trip {A:Fold K V}(h: Envelope A)(v:Hi W ℓ A) (β:ℝ) : Lit (ΨA) ℓ (guide S β P A):=by
 intro i j t; let H:=focus ((ΨA).crop m Wall.rail) ((ΨA).crop _ (2*ℓ)); let J:=page_M K (R_) (Q_); let F := sum_T P A i; have hu(w:Stage m):(∫ z,F z∂ Ξ SU.group S β w.1)=(∫ z,id z ∂(Ξ SU.group S β w.1).map F):=expect F ⟨(scoreH X.fee_m h).meas.comp measurable_prodMk_left,rfl⟩ id measurable_id
 unfold guide; rw [show sum_T P A j=F from ?_]; change (∫ z,F z∂_)=_; rw [hu i,hu j]; rw [field_map (A:= R_) X.kernel i.1 j.1 F _ (X.journal W h v i) (((ΨA).crop m Wall.rail)) (W.window_p K S X.generalS X.reach (X.fix.trans X.medi.symm) (X.medi.symm ▸ X.hl)) (show Agrees _ i.1 j.1 from t.1)]; exact (scoreH X.fee_m h).meas.comp measurable_prodMk_left
 funext x; exact integral_congr_ae (Eventually.of_forall fun y=> v (j,(x,y)) (i,(x,y)) ⟨H.iseqv.symm t,J.iseqv.refl _⟩)
lemma pride (t:S.ratio=ratio K)(i:Pane n): MeasurePreserving (peer_T W t) (νticket P i) (νticket P (W.shine n i)):=by obtain ⟨k,u,r,p,v,h⟩:= X.goodP; exact (Turn.forest W t).prod (Robe.move W v i)
-- negative law identity on expectations/movement kernel: equality already post tag integration
lemma journey_peer {A:Fold K (ReOp m)}(v:S.ratio=ratio K)(h:Envelope A)(i:Stage m)(x:Pane n): sum_T P (retire W v A) i x= (ΨA).θ m (sum_T P A (wake (ΨA) i) (W.shine _ x)):=by
 let u:= wake (ΨA) i; let v':=W.shine n x; let F:= unc_N A u v'; let H:=(ΨA).θt m; let Z:=H ∘ F; unfold sum_T; letI:=tight (K:=K) X.fee_m v'; exact (expect _ (X.pride W v x) Z (H.continuous.measurable.comp (shelfK h u v').meas)).trans (H.integral_comp_comm (Env.integrableX (shelfK h u v') (νticket P v')))
lemma prism {A:Fold K (ReOp m)}(h:Envelope A)(β:ℝ)(u:Stage m) (t:S.ratio=ratio K) : guide S β P (retire W t A) u= (ΨA).θ m (guide S β P A (wake (ΨA) u)):=by
 let Z:= (ΨA).θt m; let F:= sum_T P A (wake (ΨA) u); let q:=(ΨA).shine m u.1; let Y:=Ξ SU.group S β q; let D:= Z ∘ F; unfold guide; rw [show sum_T P (retire W t A) u=D ∘ W.shine n from funext (fun i=>X.journey_peer W t h u i)]; letI:IsProbabilityMeasure Y:= paid X.kernel _; have he:Envelope F:= Env.along (scoreH X.fee_m h) (g:=fun i:Pane n=>(wake (ΨA) u,i)) measurable_prodMk_left; exact (expect _ (Turn.fields W X.generalS X.kernel β u.1) D (Z.continuous.measurable.comp he.meas)).trans (Z.integral_comp_comm (Env.integrableX he Y))
end Scope
end YM.CF.DPress.Chess.Sermon
