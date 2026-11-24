import YM.SU5.FiniteGaugeData.Lapis.Amuse
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Artis
open Affiche
variable {n:Side}{G:Gauge}(s:Signed)(o:Site n) {L:ℕ}{a C Δ:ℝ}{P:Bed}{u:Stage} {R:PathData G}
local notation "H"=> LogField G n
-- orientation whole tangent Ward
open Bid
def stow (o:Site n)(x:LogField G n): LogField G n:= fun v=>x (v.1+o,v.2)
lemma stow_root (x:LogField G n)(t:ℝ): Lattice.translate o (represent (t • x))= represent (t • stow o x):=rfl
abbrev harbor(X:H): H:= Bid.pulled (stow o X) s
lemma tilt_node (X:H)(t:ℝ): pull s o (represent (t•X))= represent (t•harbor s o X):=by
 rw [harbor,← represent_pulled,← stow_root,← pull_one,pull_pull]; simp [affine] -- tune implicit
lemma turnZero (U:Config G n): expandAt (0:Site n) (pull s o U) = pull s 0 (expandAt o U):=by rw [expandAt_pull]; simp [affine]
lemma tilt_inverse(U:Config G n): pull s o (pull s⁻¹ (-(s⁻¹).act o) U)=U:=by rw [pull_pull,inv_mul_cancel]; simp [affine]
-- Cargo variation through all unfiltered covariance channels from exact derivative.
lemma slot_trace (o p:Site n)(a: RG.Slot)(X:H) : faceCurl (slotFace a p) (stow o X)= faceCurl (slotFace a (p+o)) X:=by
 have he:=slot_deriv a p (stow o X); have ht(U:Config G n): expandAt p (Lattice.translate o U) = expandAt (p+o) U:=by funext i; simp only [expandAt,Lattice.translate,add_assoc]
 have hv(t:ℝ): a.atSite (represent (t• stow o X)) p=a.atSite (represent (t• X)) (p+o):=by rw [← stow_root, Slot.atSite, ht]; rfl
 simp_rw [hv] at he; exact he.unique (slot_deriv ..)
abbrev onward(o:Site n):Equiv.Perm (Cell n):=(Equiv.addRight o).prodCongr (Equiv.refl PlaqAxes)
variable (D:Floor P u.clip n a C)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(c:Sworn P n G)
lemma stowZ (p:Cell n)(j:Bool)(X:H): xLin u.clip R (stow o X) (p,j)= xLin u.clip R X (onward o p,j):= by
 cases j 
 · have he(y:Site n): slotFace ⟨[],p.2⟩ y=(y,p.2):=by simp [slotFace,Slot.offset,stop]
   unfold xLin; simp only [Bool.false_eq_true,↓reduceIte]; apply congrArg; have hp:= slot_trace o p.1 ⟨[],p.2⟩ X; rw [he,he] at hp; exact hp
 · unfold xLin ellLine; simp only [if_true]; exact tsum_congr fun i=> congrArg ((R.row p.2 i).1 • ·) (slot_trace ..) -- tune
include D W A c
lemma chalice(X:H): gaugeFiscal P (harbor s o X) (harbor s o X)=gaugeFiscal P X X :=by
 rw [harbor,c s, ←wholeC D W A, ←wholeC D W A]; unfold accepts; simp_rw [stowZ (u:=u) (R:=R) o]; exact Equiv.sum_comp (onward o) (fun i=> ∑ t:Bool,‖xLin u.clip R X (i,t)‖^2) -- tune
end Artis
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Artis.chalice
