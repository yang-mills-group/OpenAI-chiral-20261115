import YM.CF.Hive.Punt
set_option maxHeartbeats 500000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Hive
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
open Acorn Nacre Skye
variable {N B m L:Side}{k j:ℕ}{a b d c e p H:ℝ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{P:Grasp Y B e}{I:Aim (CSide m B)}{M:Male}{S:Seal (Skye.Seat (CSide m B))}
local notation "N₀"=>CSide m B
def summit_g(k:Sweep N₀)(T: Seal (Skye.Seat N₀))(X: Finset (Seal (Skye.Seat N₀))):= X.image (actS k)
structure Lend (m B:Side) (e:ℝ)(R:Seal (Skye.Seat (CSide m B))) where
 slots: Type
 holder: Fintype slots
 crew: slots → Axx (Skye.Seat (CSide m B)) (Single (CSide m B)) (Castle m B e R)
attribute [instance] Lend.holder
structure Vista(P:Grasp Y B e)(M:Male)(X:Aim N₀)(U:∀ S:Seal (Skye.Seat N₀),Lend m B e S)(k:ℕ)(K z t a:ℝ):Prop where
 carry(R:Seal (Skye.Seat N₀))(q:Grove (terr _) R): (∀ j,fits (landX k K R e) (home_n _) R ((U R).crew j))∧ (∑ i:(U R).slots,hireC a z R ((U R).crew i))≤Real.exp (t*R.card*z^2) ∧ ∀ y, acts (∑ i:(U R).slots,vowC ((U R).crew i) y) (nest P X M (y.val false))=nest P X M (y.val true)
lemma shining(h: ∀ (S: Broc.Table m B), Grove (terr _) S→ ∃ F:Castle m B e S→FC (Single N₀), CookC (landX k H S e) (home_n _) S a b F (Real.exp (c*S.card*b^2))∧∀ x,acts (F x) (nest P I M (x.val false))= nest P I M (x.val true)):∃ Q,Vista P M I Q k H b c a:=by
 classical
 have hf(S:Seal (Skye.Seat N₀)):∃ X:Lend m B e S,Grove (terr _) S→ (∀ j,fits (landX k H S e) (home_n _) S (X.crew j)) ∧ (∑ j:X.slots,hireC a b S (X.crew j)) ≤ Real.exp (c*S.card*b^2) ∧∀ x,acts (∑ j:X.slots,vowC (X.crew j) x) (nest P I M (x.val false)) =nest P I M (x.val true):=by
    by_cases p:Grove (terr _) S; swap; · exact ⟨⟨Empty,inferInstance,fun j=>j.elim⟩,fun u=>(p u).elim⟩
    obtain ⟨F,⟨i,y,W,u,l,z⟩,j⟩:= h S p; exact ⟨⟨i,y,W⟩,fun _=> ⟨u,l,fun x=> (z x ▸ j x)⟩⟩
 choose Q H using hf; exact ⟨Q,⟨H⟩⟩
abbrev TagTrees (Q: ∀ S:Seal (Skye.Seat N₀),Lend m B e S):= (R:Seal (Skye.Seat N₀)) ×' (Q R).slots -- PSigma type? prefer Sigma
variable (V:∀ S:Seal (Skye.Seat (CSide m B)),Lend m B e S)
def hula (S: Seal (Skye.Seat N₀))(x:Castle m B e S) (U:Ids N₀)(X: Finset (Seal (Skye.Seat N₀))): FC (Single N₀):=by
 classical
 let k:=chip S U; let Z:= strideH S U x; let P:=actS k S
 exact mallC S U (∑ i:(V P).slots, if actS k⁻¹ ((V P).crew i).1 ∈ X then vowC ((V P).crew i) Z else 0)
lemma chore (h:Vista P M I V k H b c a) {S:Seal (Skye.Seat N₀)}(hx:Grove (terr _) S)(x:Castle m B e S)(U:Ids N₀)(X: Finset (Seal (Skye.Seat N₀))): Keys (hula V S x U X) :=by
 classical
 unfold hula; dsimp only; apply mauled; let L:=(V (actS (chip S U) S)).slots
 refine Keys.all_s (ι:=L) univ _ fun j _=>?_ ; split; swap; · exact Keys.null
 exact Keys.col _ (Keys.roll _ ((h.carry _ (grove_t _ _ hx)).1 j).2.2.1)
-- sum consumed exact
lemma baseS (h:Vista P M I V k H b c a)(h':Pearl P)(p:Stamped j L o Y)(v:P.roundZ≤(N₀).val)(w:1≤j){A B' C D:ℝ}(W:I.toll A B' C D)(f:Reef.Cry I)(X:Seal (Skye.Seat N₀))(q:Grove (terr _) X)(x:Castle m B e X)(U:Ids N₀):acts (hula V X x U univ) (nest P I M (x.val false)) = nest P I M (x.val true):=by
 classical
 unfold hula; dsimp only; simp_rw [mem_univ,if_true]; let y:=strideH X U x; let S:=actS (chip X U) X; have hx:= h.carry S (grove_t _ _ q); let Q:=∑ i:(V S).slots,vowC ((V S).crew i) y; have hs: Keys Q:= by
   refine Keys.all_s (ι:=(V S).slots) univ _ fun i _=> Keys.col _ (Keys.roll _ (hx.1 i).2.2.1)
 exact roll_u U h' p v w W f _ _ Q hs (hx.2.2 y)
end YM.CF.Hive
