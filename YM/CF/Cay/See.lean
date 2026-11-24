import YM.CF.Cay.Zeal
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
open Work.E03
variable {X:Support c}
local notation "b"=>radiusB x
abbrev herald(S:StepData c f)(s:Signed): Along S → Site c := Sum.elim (orientZ S s) (Sum.elim (s.act ∘ S.ratio.parent) s.act)
abbrev horn(x:ℝ)(l:ℕ):=(l+76)*radiusB x
lemma turret(p:Site f→ Site c)(hp:∀ y (i:Axis),separation (p y) (p (y+step i)) ≤ 1)(A:PathData G)(i:Site f){U V:Config G f}(h:AgreeNear p (p i) (r+4) U V): turF A r U i=turF A r V i:=by
 have hh(y:RG.Slot)(hy:y.length≤r):y.atSite U i=y.atSite V i:=by
    let j:=Work.F03.slotFace y i; have hw:y.walk.length ≤ r:=by unfold RG.Slot.length at hy; omega
    have hi:j.1=stop i y.walk:=by unfold j Work.F03.slotFace RG.Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 2 [show i=i+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
    have hj:separation (p i) (p j.1)+4 ≤ r+4:=by rw [hi]; exact Nat.add_le_add_right ((sep_walk p hp ..).trans hw) _
    have he:faceValue U j=faceValue V j:= travel_near p hp U V j.1 (square j.2.val.1 j.2.val.2) 4 le_rfl (h.shrink hj)
    rw [Work.F03.atSite_path, Work.F03.atSite_path, he,travel_near p hp U V i y.walk _ (by omega) h]
 have hg{l:ℕ}(Z:ℕ→ Atom G l):gplot (batch Z r) U i=gplot (batch Z r) V i:=tsum_congr fun k=> by
    unfold batch; split
    next hy=> exact congrArg (Z k).poly (funext fun i'=> hh _ ((Finset.single_le_sum (f:=fun i=>(Z k|>.leg i).length) (fun _ _=>by omega) (mem_univ i')).trans hy)) -- tune
    simp only [dimU]
 exact congrArg₂ (·+·) (hg A.cubic) (hg A.quartic)
lemma calm (s:Signed)(i:Along S)(h:Ready T x)(hp:1000≤radiusB x)(u:Beat.shadows (o:=herald S s i) X (horn x l)): Virt S (fun M=>stars T x M q d l β s i) X:=by
 intro M N p; let R:=Stores.till x; have he:R ≤ radiusB x:= Nat.div_le_self ..
 rcases i with i|i|i
 · exact Slate.vary p h hp s i (aroundBk X u (by change separation _ (herald S s (.inl i))+_≤_; unfold horn; simp_rw [separation_self,Nat.add_mul]; omega)) -- tune infer
 · refine turret S.ratio.parent (parent_step S) _ _ ?_; apply pulled_near; intro e w; exact p.backF h hp e (aroundBk X u (by change separation (herald S s (.inr (.inl i))) _≤ R+4+1 at w; unfold horn; simp_rw [Nat.add_mul]; omega))
 have hw:Hors.cart x S.patch.L ≤ R:= Nat.div_le_self ..; change - turF _ _ (pull s 0 M.V) i=- turF _ _ (pull s 0 N.V) i; refine congrArg Neg.neg (turret id sep_step _ _ (coarse_turn ((p.scope (r:=Hors.cart x S.patch.L+4+1) (x:=x) ?_ u).outer))); unfold horn; simp_rw [Nat.add_mul]; omega
-- absorb overhead winding via reanchor.
lemma points_p(e:Bond f)(t:Site c){r:ℕ}(p:r< separation t (S.ratio.parent e.1)): S.ratio.parent e.1 ∉ halo r {t} :=by
 intro l; obtain ⟨i,h,u⟩:=halo_spec.mp l; rw [mem_singleton.mp h] at u; omega
lemma curt{Y:Monk G S→ℝ}{o:Site c}{Ω:Support c}(e:Bond f)(h:Virt S Y (halo r {o}))(p:Beat.shadows (o:=S.ratio.parent e.1) Ω (2*r)) : Virt S (spring Y e) Ω :=by
 by_cases hx:r<separation o (S.ratio.parent e.1)
 · intro M N v; rw [off h e (points_p e o hx),off h e (points_p e o hx)] -- tune
 intro M N v; exact stanza h e (v.mono (aroundBk Ω p (by rw [separation_comm]; omega)))
end YM.CF.Cay
