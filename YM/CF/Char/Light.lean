/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Newt.Amber
import YM.CF.Summit.Crews
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Watches
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Base
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymRows
/-! Gauging RG UV substitution closest local analogue of the exact implicit saddle. Extend to sectors,
 including (new here) Hessian perturbation on finite panel system. Gauge constants ONLY post-L.
 First file: numerical locality of H0, K0 and μ⁰. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Char
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric Newt Jet
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
 AnalyticBridge.NonflatCovarianceLocality.Matching
open Push.SectorMeasure Next.Fluctuations Next.SectorChange Next.SectorChange.Wisps Next.SectorChange.Schur PhysicalNext.JointLoad PatchReads
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{A A':Stores S}{F F':Forest S.ratio}{k k':S.Choices} {V W:Config G c}{x C:ℝ}{r l:ℕ}
 {Y: LinkArray G (Frozen A x F)}{Y':LinkArray G (Frozen A' x F')}{o:Site c}
lemma brick {i:Rows.Receipt G S} (hs:S.patch.Branches S.kernel G)(h:Scan S x (down S i) (2*span S.patch x) A A' F F' k k' V W Y Y'):
 Offset.fixedBase T x V k i.1=Offset.fixedBase T x W k' i.1:=by
 obtain ⟨⟨s,i⟩,b⟩:=i
 let R:=Stores.till x; let L:=span S.patch x; let y:=roots S (i.elim (fun p=>Sum.inl p.1) Sum.inr)
 let u:=pull s 0 V; let v:=pull s 0 W
 change Scan _ x (s.act y) .. at h
 have he:AgreeNear id y (2*R+4) u v :=coarse_turn (s:=s) (o:=y) (h.lower (by unfold R span; omega)).outer
 have hh (j:Twin c) (hx:separation y j.1.1≤ R) : T.Xn R u j=T.Xn R v j:=plotted_near id Work.E03.sep_step u v T.low T.down R S.patch.L.val j S.patch.L.property (he.shrink (by simp only [id_eq]; omega))
 have hp{I:Type}(i:I)(φ:Config G c→I→Twin c→Pay G)(h:∀j,(R<separation y j.1.1→ φ u i j = 0)∧ (AgreeNear id y R u v→φ u i j=φ v i j)):=Lift.zipAt R u v y i φ _ _ h (he.shrink (by simp only [separation_self]; omega)) hh
 cases i with
 | inl i =>
             change T.Xf R (facade S s V 0) i - _ = T.Xf R _ i - _
             rw [hp i (T.Φ R) (Lift.vBand T R u v i)]
             have hh:AgreeNear S.ratio.parent (S.ratio.parent i.1.1) (R+4) (facade S s V 0) (facade S s W 0):= facade_read (h.lower (by unfold R span; omega)).outer 0
             rw [show T.Xf R (facade S s V 0) i =T.Xf R (facade S s W 0) i from plotted_near S.ratio.parent (Work.E03.parent_step S) (facade S s V 0) _ _ _ _ _ _ le_rfl hh]
 | inr i =>
             change Tube.Z _ _ u i - _ = Tube.Z _ _ v i - _
             rw [hp i (T.Φ' R) (Lift.kickBand T R u v i)]
             unfold Tube.Z; rw [show S.prediction (facade S s V 0) _ i=S.prediction (facade S s W 0) _ i from predict_read hs (i:=i) (h.lower (by unfold span; omega)) 0,he i (show separation y y≤_ from by simp)]
lemma plinth {i:Rows.Receipt G S} (hs:S.patch.Branches S.kernel G)(h:Scan S x (down S i) (2*span S.patch x) A A' F F' k k' V W Y Y')(q:Chi)(d:ℝ) :
 Offset.f0 T x A F k V q d Y i=Offset.f0 T x A' F' k' W q d Y' i:=by
 have hp:=h.lower (r':=span S.patch x) (by omega); have he:Rows.keep x (shots S x) A F i.1 ↔Rows.keep x (shots S x) A' F' i.1:= ⟨cover_eq hp,cover_eq hp.turn⟩
 let v:=Rows.input x A F (autoShell q d V Y)
 unfold Offset.f0; rw [tape_read,tape_read]; unfold Rows.restrict; simp_rw [he, Pi.add_apply]; split
 · rw [brick hs h, bump_eq hs v hp, show Rows.bump T x W k' v i.1= Rows.bump T x W k' (Rows.input x A' F' (autoShell q d W Y')) i.1 from bump_dep _ _ _ _ i.1.1 i.1.2 _ _ hs (fun j hj=> input_eq hp ((contains ..).mp hj))]
 rfl
variable {i j:Rows.In x A F (G:=G)}{i' j':Rows.In x A' F' (G:=G)}
lemma plump (hr:Ready T x)(h : Scan S x (front A F i) (radiusB x/5) A A' F F' k k' V W Y Y')(he:PatchReads.lift i=PatchReads.lift i')(q:Chi)(d:ℝ):
 Offset.b T x k A F q d Y V i=Offset.b T x k' A' F' q d Y' W i':=by
 unfold Offset.b mulVec dotProduct; simp only [Matrix.transpose_apply]; refine Finset.sum_congr rfl fun j _=>?_
 by_cases hx: span S.patch x < separation (down S j) (front A F i)
 · rw [move_range hr.rules hx,move_range hr.rules (i:=j) (j:=i') (by rwa [←faces he]),zero_mul,zero_mul]
 have hj:= hr.inputs; rw [move_eq hr.rules (i:=j) (h.shrink (by rw [separation_comm]; omega)) he,plinth (i:=j) hr.rules (h.shrink (by rw [separation_comm]; omega))]
lemma meetX(hr:Ready T x)(h : Scan S x (front A F i) (radiusB x/3) A A' F F' k k' V W Y Y')(he:PatchReads.lift i=PatchReads.lift i')(q:Chi)(d:ℝ):
 Offset.mean T x k A F q d Y V i=Offset.mean T x k' A' F' q d Y' W i':=by
 unfold Offset.mean mulVec dotProduct; simp only [Matrix.neg_apply,Matrix.transpose_apply]
 refine PatchReads.sum_eq (h.lower (r':=radiusB x/20) (by omega)) (fun j hj=>?_) (fun j hj=>?_) fun j j' hj hj' =>?_
 · rw [per_zero (panels A F) _ (i:=i) (j:=j) (fun he=>hj.not_ge (ball_member he)),neg_zero,zero_mul]
 · rw [per_zero (panels A' F') _ (i:=i') (j:=j) (fun hv=>hj.not_ge ((faces he).symm ▸ ball_member hv)),neg_zero,zero_mul]
 rw [plump hr (i:=j) (h.shrink (by omega)) hj', per_eq hr (h.lower (by omega)) he hj']
end YM.CF.Char
