import YM.CF.BProof.Floral.Tolls
import YM.CF.Bloom.Apse
import YM.CF.Song.Full
import YM.CF.Sere.Ward
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open YM.CF.Floral Ione Haro Beau Siete PhysicalNext.JointLoad Heir Vow
open Tap Next.Free Bloch
open scoped YM.CF.Mew
variable {n:Side}{L j:ℕ}{R R':RegBudget n}{P:BudgetPoint}{h b c:ℝ}{M:Male}
-- Note Mint projection included independently of Beacon's sym
lemma smooth_i (p:Books P R h b)(k:1≤h)(i:Scree.Hub n):ContDiffAt ℝ (↑(2:ℕ):WithTop ℕ∞) (Beau.pot (n:=n) ∅ ∘ R i ∘ increment 1) 0:= (press_high (Books.here p k i) k 1 (ping_f P i.val.2) ∅).paid.of_le (Nat.cast_le.mpr (show 2≤ P.order from (by have y:=P.order_ge; omega)))
lemma ionic_plus (t:Ionic P L R)(u:Ionic P L R')(A:Books P R h b)(B:Books P R' h c)(k:1≤h):Ionic P L (R+ R'):=by
 intro i p q; constructor; · change pot _ (R i 1+R' i 1)= _; rw [map_add,(t i p q).1,(u i p q).1,add_zero]
 intro x y h g
 have he: Beau.pot (n:=n) ∅ ∘ (R+R') i ∘ increment 1= (Beau.pot (n:=n) ∅ ∘ R i ∘ increment 1)+(Beau.pot (n:=n) ∅ ∘ R' i ∘ increment 1):= funext fun _=>map_add .. -- parse precedence +
 rw [he,iteratedFDeriv_add_apply (smooth_i A k i) (smooth_i B k i),_root_.add_apply,(t _ p q).2 _ _ h g,(u _ p q).2 _ _ h g,add_zero]
lemma ionic_z (t:Ionic P L R)(a:Books P R h b)(k:1≤h)(z:ℂ): Ionic P L (z • R):=by
 intro i p q; constructor
 · change Mew.chipV ∅ (z • R i 1)= _; rw [map_smul,show Mew.chipV (n:=n) ∅ (R i 1)=0 from (t i p q).1,smul_zero]
 intro x y h g; have he: Beau.pot (n:=n) ∅ ∘ (z • R) i ∘ increment 1=z • (Beau.pot (n:=n) ∅ ∘ R i ∘ increment 1):= funext fun w=>map_smul (Mew.chipV (n:=n) ∅) z (R i (increment 1 w))
 rw [he,iteratedFDeriv_const_smul_apply (smooth_i a k i),_root_.smul_apply, (t _ p q).2 _ _ h g,smul_zero]
lemma ionic_sub (t:Ionic P L R)(u:Ionic P L R')(A:Books P R h b)(B:Books P R' h c)(k:1≤h): Ionic P L (R-R'):=by simpa [sub_eq_add_neg] using ionic_plus t (ionic_z u B k (-1)) A (Books.σ B (-1)) k
structure Copper (P:BudgetPoint)(L:ℕ)(j:ℕ)(R:RegBudget n)(M:Male):Prop where
 cred : Cred R (treeΘ P L)
 mint : Sour.BondL.mintv (treeΘ P L) j M R
lemma Copper.sub (A:Copper P L j R M)(B:Copper P L j R' M): Copper P L j (R-R') M:=by
 constructor; · intro s x l i p; exact (congrArg₂ (·-·) (A.1 s x l i p) (B.1 s x l i p)).trans (map_sub ..).symm
 let S:= treeΘ (X:=n) P L; let f(R:RegBudget n):=Tap.potion j M (heroP (StackL R S)); have he: f (R-R')=f R-f R':=by
    have ht:StackL (R-R') S= StackL R S-StackL R' S:= (eq_sub_of_add_eq (by rw [←mark_T,sub_add_cancel])); unfold f potion; funext x; rw [ht,Exa.weights,mul_sub,sub_mul]; rfl -- notation capture
 change NullW (f (R-R')); rw [he]; refine ⟨?_,fun i=>?_⟩; · change f R 0-f R' 0=0; rw [show f R 0=0 from A.mint.still,show f R' 0=0 from B.mint.still,sub_self]
 -- f t uses bout.Tr
 have ht:= (A.mint.free i).sub (B.mint.free i); rw [sub_self] at ht; exact ht
end YM.CF.Py
