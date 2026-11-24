import YM.CF.Tarn.Plot
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
section
variable (T:Tube G S)(x:ℝ)
local notation "R"=>Stores.till x
local notation "L"=>S.patch.L
open Work.E03
def TaleX (α:ℝ)(V:Config G c)(U:Config G f) (i:Along S):ℝ:=match i with
 | .inl (.inr (.inr (.inl i)))=> -α * king ∅ T.down T.low R S.patch.L.val x V i
 | .inl _=>0
 | .inr (.inl i) => gplot (batch T.up.loop R) U i
 | .inr (.inr i)=> -gplot (batch T.down.loop (R/S.patch.L.val)) V i
def loreG(q:Chi)(d α:ℝ)(l:ℕ)(s:Signed)(i:Along S)(M:Monk G S):=TaleX T x α (pull s 0 M.V) (pull s 0 (M.sent x T q d l 0)) i
lemma agreeKing(c:Side)(r D:ℕ)(h:0<D)(t:ℝ)(i:Cell c)(A:PathData G)(p:Clip)(V W:Config G c)(hp:AgreeNear id i.1 (r+4) V W): king ∅ A p r D t V i=king ∅ A p r D t W i:=by
 have hv:faceValue V i=faceValue W i:=travel_near id Work.E01.sep_step_le V W i.1 _ _ (Nat.le_add_left ..) hp
 rw [manta,manta,hv]; congrm _+?_ ; refine sum_congr rfl fun j _=>?_ ; rw [plotted_near id Work.E01.sep_step_le V W p A _ _ (i,j) h hp] -- tune hp
lemma gpot{c f:Side}(p:Site f→ Site c)(hp:∀ y (i:Axis),separation (p y) (p (y+step i)) ≤ 1)(A:PathData G)(i:Site f){U V:Config G f}(h:AgreeNear p (p i) (r+4) U V):gplot (batch A.loop r) U i=gplot (batch A.loop r) V i:=by
 have hh(y:RG.Slot)(hy:y.length≤r):y.atSite U i=y.atSite V i:=by
    let j:=Work.F03.slotFace y i; have hw:y.walk.length ≤ r:=by unfold RG.Slot.length at hy; omega
    have hi:j.1=stop i y.walk:=by unfold j Work.F03.slotFace RG.Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 2 [show i=i+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
    have hj:separation (p i) (p j.1)+4 ≤ r+4:=by rw [hi]; exact Nat.add_le_add_right ((sep_walk p hp ..).trans hw) _
    have he:faceValue U j=faceValue V j:= travel_near p hp U V j.1 (square j.2.val.1 j.2.val.2) 4 le_rfl (h.shrink hj)
    rw [Work.F03.atSite_path, Work.F03.atSite_path, he,travel_near p hp U V i y.walk _ (by omega) h]
 have hg{l:ℕ}(Z:ℕ→ RG.Atom G l):gplot (batch Z r) U i=gplot (batch Z r) V i:=tsum_congr fun k=> by
    unfold batch; split
    next hy=> exact congrArg (Z k).poly (funext fun i'=> hh _ ((Finset.single_le_sum (f:=fun i=>(Z k|>.leg i).length) (fun _ _=>by omega) (mem_univ i')).trans hy)) -- tune
    simp only [dimU]
 exact hg _
lemma crisp (q:Chi)(d α:ℝ)(l:ℕ)(i:Along S)(p:Ready T x)(h:1000≤radiusB x)(k: Signed) : Virt S (loreG T x q d α l k i) (pavilion (horn x l) (herald S k i)):=by
 intro M N u; let Z:=pavilion (horn x l) (herald S k i); have hx:R ≤ radiusB x:= Nat.div_le_self ..; have ht:Hors.cart x L ≤ R:= Nat.div_le_self ..
 rcases i with (i | i | i|i)|i|i
 · rfl
 · rfl
 · refine congrArg (-α *·) (agreeKing _ _ _ S.patch.L.property _ _ _ _ _ _ (coarse_turn (u.scope (x:=x) (r:=R+4+1) ?_ (Subset.refl _)).outer)); unfold horn; simp_rw [Nat.add_mul]; omega
 · rfl
 · refine gpot S.ratio.parent (Work.E03.parent_step S) _ _ ?_; apply pulled_near; intro e w; exact u.backF p h e (aroundBk Z (r:=horn x l) (o:=herald S k (.inr (.inl i))) (Subset.refl _) (by change separation (herald S k (.inr (.inl i))) _≤ R+4+1 at w; unfold horn; simp_rw [Nat.add_mul]; omega)) -- tune
 refine congrArg Neg.neg (gpot id Work.E01.sep_step_le _ _ (coarse_turn ((u.scope (r:=Hors.cart x S.patch.L+4+1) (x:=x) ?_ (Subset.refl _)).outer))); unfold horn; simp_rw [Nat.add_mul]; omega
end
end YM.CF.Tarn
