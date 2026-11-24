import YM.CF.Buffered.Subst

/-!
# Through the actual carrier

Adapt `Volume.marked_project`, use checked letter theorems.
Density indexing, color/flavor, particle order and ket all still FiniteGaugeData's.
-/
set_option autoImplicit false
set_option maxHeartbeats 580000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree
open Reed (Fine think)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {M H B L : Side} {j : ℕ} {ho : Odd L.val} {Y : Pricing j L ho (Thread j)}{e : ℝ} {P : Grasp Y B e}
local notation "Nc" => mid M B
local notation "Nf" => mid H B
variable (G : Ratio (mid M B) (mid H B))
include G
def placeL (Q : Op Slot) (R : Male) (x : nomA M H B) (j : ℕ) : Phys Nf →ₗ[ℂ] Phys Nc where
  toFun := Volume.placeOp (j:=j) G Q R x
  map_add' a b:= by unfold Volume.placeOp scaleZ fire effectK cartsL; dsimp only; rw [map_add,map_add,map_add,smul_add,map_add,smul_add]
  map_smul' a b:= by unfold Volume.placeOp scaleZ fire effectK cartsL; dsimp only; simp only [map_smul, RingHom.id_apply]; rw [smul_comm (_:ℂ) a, smul_comm (_:ℂ) a]
#print axioms placeL
lemma through (x : nomA M H B) (R : Male) (p : G.count=L) (h : P.roundZ ≤ (Nc).val) (k : JointB G x e) (v : 0<e) (Q : Haro.SpaceM) (w : Odd G.count.val)
    {S : Finset (Single Nc)} {b : Bool} {A : FC (Single Nc)} (a : Fine (Tset (mid M B)) S b A) (y : Phys Nf) :
    acts A (placeL G Q.val R x j y) = placeL G Q.val R x j (acts (subF G j Q.val R w x A) y) := by
  induction a generalizing y with
  | empty=> rw [map_zero,act_zero,act_zero,map_zero]
  | one=> rw [sub_one]; simp
  | seed i u=> by_cases g:i∈ Tset (mid M B)
               · rw [show (think (Tset (mid M B))).term i=put i from if_pos g,← create_put, sub_create _ _ _ _ _ _ (within_basis _ _ g)]; exact Volume.letter_p G x R p h k v Q _ ((touchP _).symm ▸ within_basis _ _ g) _
               rw [show (think (Tset (mid M B))).term i= -takeF i from if_neg g,← remove_take, map_neg, act_neg,act_neg, map_neg, sub_remove _ _ _ _ _ _ (within_basis _ _ (mem_compl.mpr g))] -- order
               exact congrArg Neg.neg (Volume.letter_r (j:=j) G x R p ho Q _ ((touchP _).symm ▸ within_compl.mp (within_basis _ _ (mem_compl.mpr g))) _)
  | add _ _ ih it=> rw [map_add,act_add,act_add,map_add,ih,it]
  | scale _ _ ih=> rw [map_smul,act_smul,act_smul,map_smul,ih]
  | grow e p ih it=> rw [sub_mul _ _ _ _ _ _ e p,act_mul,act_mul,it,ih]

variable {R:Scree.Loom (mid M B)} {X:Scree.GramM (mid H B)}{R':Scree.Loom (mid H B)}{d:ℝ}{q:Chi}
theorem projected (E:Girt.BaseL P G X R R' q d) (T:RG.StepData (More Nc) (More Nf))
    (Q:Haro.SpaceM)(w : Odd G.count.val) (F:Forest (ratio G))(V:Orbit Nc)(W:Orbit Nf) {S : Finset (Single Nc)} {b : Bool} {A : FC (Single Nc)} (p : Fine (Tset (mid M B)) S b A) :
    let x:nomA M H B:=(seine G F q d (R' W) (R V),R V)
    beamL Nc (acts A (carrier P R X R' G T q d Q.val F V W)) =
         T.density X.beta W.1 V.1 • beamL Nf (acts (subF G j Q.val X.J.M w x A) (denZ X P R' W)) := by
  intro x; let y:= denZ X P R' W; let y':=acts (subF G j Q.val X.J.M w x A) y
  change beamL Nc (acts A (T.density X.beta W.1 V.1 • placeL G Q.val X.J.M x j y))=_
  have hp:JointB G x e:= E.trial F (R' W) V
  rw [show acts A (T.density X.beta W.1 V.1 • placeL _ _ _ _ _ _) = T.density X.beta W.1 V.1 • acts A _ from map_smul ((acts A).restrictScalars ℝ) _ _,map_smul,
    through G _ _ E.power E.size hp E.pe Q w p y]
  apply congrArg (fun z :ℂ=> T.density X.beta W.1 V.1 • z)
  change beamL Nc (Volume.placeOp (j:=j) G Q.val X.J.M x y')=beamL Nf y'
  unfold Volume.placeOp; rw [shoulderL]
  change inner ℂ (mateK Nc) _=beamZ _ y'
  rw [show inner ℂ _ _=_ from (Spire.shuttle G E.power E.size x hp E.pe X.J.M).2 (cartsL (switchG G).symm y')]
  exact Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _
end YM.CF.Buffered.Advance
#print axioms YM.CF.Buffered.Advance.projected
