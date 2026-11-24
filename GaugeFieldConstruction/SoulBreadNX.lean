import GaugeFieldConstruction.Marrow
import YM.SU5.Assay.Wipe
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3200
set_option linter.unusedSectionVars false
set_option maxHeartbeats 140000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup Ballad Six Glaze
/-!
 Own small presentation at every height, before mean Slabs compression. Packs with width at that very step, not Assert on general F no support.
-/
abbrev corneaNX (P:Spine)(i:Axis)(s d:ℕ)(F:P.Test): P.Slabs i:= P.HabBox i s (d+d) (P.shifts i d F)
abbrev hearthNX (P:Spine)(i:Axis)(a:ℝ): P.Slabs i:= P.Eucl i a.toNNReal
def grantGapNX (P:Spine)(i:Axis)(s d:ℕ)(F:P.Test)(a b:ℝ): P.Slabs i:= P.hearthNX i (a-P.tock s d)*P.corneaNX i s d F*P.hearthNX i (b-P.tock s d)
variable {P:Spine}(i:Axis)(s d:ℕ){F:P.Test}{A B:P.meshPin}
lemma grantCoreNX (w:P.BEntry i (d+d) (P.shifts i d F)): P.Habitable i F s (- P.stampPin s d) (P.stampPin s d) (P.corneaNX i s d F):=by
 have hk:= Habitable.direct (a:= -(d:ℤ)) (by rw[neg_neg]; exact w) s
 convert hk using 1; · rw [minted_neg]
 · congr 1; omega
 rw[neg_neg]
lemma hearthPayNX (w:P.BEntry i (d+d) (P.shifts i d F))(p:P.tock s d≤ (A:ℝ))(q:P.tock s d≤ (B:ℝ)): P.Habitable i F s (-A) B (P.grantGapNX i s d F (A:ℝ) (B:ℝ)):=by
 have he:P.tock s d=(P.stampPin s d:ℝ):=rfl
 have hx:((↑(-P.stampPin s d):ℝ)-(↑(-A):ℝ))=(A:ℝ)-P.tock s d:=by rw [he]; change -_ - -_= _; ring
 have hp: (↑(-A):ℝ)≤ (↑(-P.stampPin s d):ℝ):= neg_le_neg (he ▸ p)
 unfold grantGapNX hearthNX; convert (grantCoreNX i s d w).pad hp (he ▸ q) using 2
 -- tune
 · rw[hx]
 · rw[he]
lemma mantleNX (a:ℝ) : (P.hearthNX i a).1= (P.publicH i).Time.wax a:=rfl
lemma grantAcrossNX (F':P.Test)(a b:ℝ): (P.grantGapNX i s d F' a b).1=
  (P.publicH i).Time.sand ((P.corneaNX i s d F').1:P.Hil i→L[ℂ]P.Hil i) (a-P.tock s d) (b-P.tock s d):=rfl -- coe.Hil tuning
-- extends real pads.Be mindful Habit supplies every pin stance.
lemma grantLargeNX (f g:ℕ)(G:P.Test) (u:P.BEntry i (f+f) (P.shifts i f G))(v:P.BEntry i (g+g) (P.shifts i g G)){a b:ℝ}(hp:P.tock s f≤a)(hh:P.tock s f≤b)(hP:P.tock s g≤a)(hH:P.tock s g≤b) : P.grantGapNX i s f G a b=P.grantGapNX i s g G a b:=by
 let M:= max (P.tock s f) (P.tock s g)
 have he:∃ K:P.meshPin,(K:ℝ)= M:=by
   rcases le_total (P.tock s f) (P.tock s g) with l|l
   · exact ⟨P.stampPin s _,(max_eq_right l).symm⟩
   exact ⟨P.stampPin s _,(max_eq_left l).symm⟩ -- implicit infer d impossible
 obtain ⟨K,hk⟩:=he
 have hf:P.tock s f ≤ (K:ℝ):= hk.symm ▸ le_max_left _ _; have hg:P.tock s g≤(K:ℝ):=hk.symm ▸ le_max_right _ _; have p: (K:ℝ)≤a:=hk.symm ▸ max_le hp hP; have q: (K:ℝ)≤ b:=hk.symm ▸ max_le hh hH
 have hu:=((hearthPayNX i s f u hf hf).same (hearthPayNX i s g v hg hg))
 have h0(n:ℕ)(u:P.tock s n≤(K:ℝ)): P.grantGapNX i s n G a b=P.hearthNX i (a-(K:ℝ))* P.grantGapNX i s n G (K:ℝ) (K:ℝ) * P.hearthNX i (b-(K:ℝ)):=by
   let J:=P.tock s n; have hs(x y:ℝ)(p:0≤x)(q:0≤y): P.hearthNX i x*P.hearthNX i y=P.hearthNX i (x+y):=Subtype.ext ((P.publicH i).Time.wax_sq p q)
   unfold grantGapNX; conv_rhs=>rw[←mul_assoc _ _ (hearthNX _ i _),←mul_assoc,hs _ _ (sub_nonneg.mpr p) (sub_nonneg.mpr u),mul_assoc _ (hearthNX _ i _) _,hs _ _ (sub_nonneg.mpr u) (sub_nonneg.mpr q)]
   rw [sub_add_sub_cancel,add_comm ((K:ℝ)-_),sub_add_sub_cancel]
 rw[h0 f hf,h0 g hg,hu]
#print axioms grantLargeNX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
