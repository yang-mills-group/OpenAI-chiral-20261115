import GaugeFieldConstruction.GazelleX
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Grotto
section firm
variable {n:Side}{I:Type}[LinearOrder I][Fintype I]
-- Jew fold.Abstract3004. Realm.Econom prove at ALL subsequent paths & all constant History.
structure Rio (I:Type)(n:Side) where
 X : XE I (InkD n) n
 Y : XE I (InkD n) n
 B : KK I (Copy n) n
namespace Rio
instance : Zero (Rio I n):=⟨⟨0,0,0⟩⟩
instance:Add (Rio I n):=⟨fun x y=> ⟨x.X+y.X,x.Y+y.Y,x.B+y.B⟩⟩
structure CashI (I:Type)(n:Side) where
 W : XE I ℝ n
 M : XE I ℝ n
 F : KK I ℝ n
instance : Zero (CashI I n):=⟨⟨0,0,0⟩⟩
instance:Add (CashI I n):=⟨fun x y=> ⟨x.W+y.W,x.M+y.M,x.F+y.F⟩⟩
structure Weighted (p:BudgetPoint)(σ:I→ Seat n)(r h:ℝ)(k:ℕ)(X:Rio I n)(Y:CashI I n):Prop where
 white: BillX p σ h r Y.W X.X
 active: BillX p σ h r Y.M X.Y
 bank: BillF p σ h r k Y.F X.B
abbrev Origin (n:Side):= List (Site (More n)) → Site (More n)→ℝ
section
variable {p:BudgetPoint}{σ:I→ Seat n}{a b r h:ℝ}{k d:ℕ}{x y:Rio I n}{V W:CashI I n}
lemma Weighted.free:Weighted p σ r h k 0 0:=⟨ReefX.registry_zero σ _ (T:=PitR (n:=n) _ _ _) ReefxR,ReefX.registry_zero σ _ (T:=PitR (n:=n) _ _ _) ReefxR,ReefX.registry_zero σ _ (T:=PitF (n:=n) _ _ _ _) (ReefxF _)⟩
lemma Weighted.merge (u:Weighted p σ r h k x V)(v:Weighted p σ r h k y W):Weighted p σ r h k (x+y) (V+W):=⟨ ReefX.registry_plus σ cloudP (T:=PitR p h r) ReefxR u.white v.white, ReefX.registry_plus σ cloudP (T:=PitR p h r) ReefxR u.active v.active, ReefX.registry_plus σ cloudK (T:=PitF p h r k) (ReefxF k) u.bank v.bank⟩

def Paw (d:ℕ)(a b:ℝ)(V:CashI I n) : Origin n :=fun L=>pointX cloudP V.W (RedB d a b L)
def Band (d:ℕ)(a b:ℝ)(V:CashI I n) : Origin n :=fun L i=>pointX cloudP V.M (RedB d a b L) i + pointX cloudK V.F (ColdB d a b L) i

def SumAll (d:ℕ)(a b:ℝ)(X:Origin n)(V:CashI I n) : Origin n:=X+Paw d a b V+Band d a b V
lemma CashI.planted:Paw d a b (I:=I) (n:=n) 0=0:=funext fun i=>funext fun j=>pointX_0 .. -- P extra
lemma CashI.Padd: Paw d a b (V+W)=Paw d a b V+ Paw d a b W:=funext fun i=>funext fun j=>pointX_add ..
lemma CashI.V0: Band d a b (I:=I) (n:=n) 0=0:=by funext i j; change pointX _ 0 _ _+pointX _ 0 _ _=0; rw[pointX_0,pointX_0, add_zero]
lemma CashI.Badd: Band d a b (V+W)=Band d a b V+ Band d a b W:=by funext L i; change pointX cloudP (V.M+W.M) _ _ + pointX cloudK (V.F+W.F) _ _=_; rw[pointX_add,pointX_add]; simp only [Pi.add_apply,Band]; ring
lemma pointX_up {α:Type}[Fintype α](σ:α→ Support (More n))(V:dues I α→ℝ)(h:∀ i,0≤V i)(H R:Support (More n)→ℝ)(v:∀ i,H i≤ R i)(i: Site (More n)):
 pointX σ V H i ≤ pointX σ V R i:=by unfold pointX postG postY; refine sum_le_sum (fun j e=> mul_le_mul_of_nonneg_left (v _) ?_); exact sum_nonneg fun _ _=>h _
lemma Weighted.estate (v:Weighted p σ r h k x V) (t:0≤ b) (L:List (Site (More n)))(i:Site (More n)) : 0≤Paw d a b V L i ∧ 0≤Band d a b V L i ∧∀ o:Site (More n),Paw d a b V L i≤ Paw d a b V (o::L) i∧Band d a b V L i≤Band d a b V (o::L) i:=by
 refine ⟨pointX_gene _ _ v.white.gist _ (fun _=>Temp_p ..|>.le) i,add_nonneg (pointX_gene _ _ v.active.gist _ (fun _=>Temp_p ..|>.le) i) (pointX_gene _ _ v.bank.gist _ (fun _=>Temp_p ..|>.le) i),?_⟩; -- tune missing args underscores
 intro o; exact ⟨pointX_up cloudP _ v.white.gist _ _ (fun x=>Temp_mono d _ b L x t o) _,add_le_add (pointX_up cloudP _ v.active.gist _ _ (fun x=>Temp_mono d _ b L x t o) _) (pointX_up cloudK _ v.bank.gist _ _ (fun x=>Temp_mono d _ b L x t o) _)⟩
end
end Rio
end firm
end YM.CF.Scree.Ing
end
