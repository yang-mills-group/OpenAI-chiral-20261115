import Merino.Coin.Power

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Rive Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
variable {N B:Side}
variable {I:Type}[Fintype I][LinearOrder I]
local notation "X"=>mid N B

variable {D:Key I→RegBudget (mid N B)}{F:Key I→ForceBudget (mid N B)}
open NormedSpace Spire Stax Tulip
variable {L:Side}{j:ℕ}{odd:Odd L.val}{Y:Pricing j L odd (Thread j)}{e:ℝ}

def serum (U:Grasp Y B e)(R:GramM (mid N B))(A:Scree.Loom (mid N B))
 (D:Key I→RegBudget (mid N B))(F:Key I→ForceBudget (mid N B))
 (w:Orbit (mid N B))(z:Key I):Phys (mid N B):=
 denZ (color_b R R.beta (R.F+D z) R.slip (R.K + F z) R.v) U A w
attribute [local instance] opCStarAlgebra

-- transport pressure probes between live Fit and its sparse replacement
theorem blush (U:Grasp Y B e) (R:GramM (mid N B))
 (A:Scree.Loom X)(w:Orbit (mid N B))(p:IsStarProjection (spar j R.J.M (A w)))
 (o:I→Site (mid N B))(t:Notice o D F)
 (l:List I)(z:ψS (node∘o) l):
      tipI (serum U R A (reduce o D) (reduceK o F) w) l=
      tipI (serum U R A D F w) l:=by
 let f(z:Key I):=exp (exponentL R.p (D z) w.1)*fueled R.p (R.K + F z) w
 let g(z:Key I):=exp (exponentL R.p (reduce o D z) w.1)*fueled R.p (R.K+reduceK o F z) w
 let σ:=node∘o
 have he(i:I):νTip D i=νΦX D {i}:= funext₂ fun _ _=>(cue_1 ..).symm


 have a:=castEra (P:=R.p) σ D (νTip D) t.roll.1
     (fun i=>(displayE t i).2) (fun i _=>by rw [he]) l z w.1
 have b:=castFuel (P:=R.p) σ F (fun i=>(displayK t i).2) l z R.K w
 rw [t.roll.2] at b
 simp only [sub_zero] at b
 have c:=uS_b σ z
 have d:Soft l f g:=(a.expΩ c).mul b c
 let H:=pilotH U R A w p
 let K:Cipher X→ₗ[ℂ] Phys X:=⟨⟨fun i=>H (Cadre.poseL _ i),fun x y=> (congrArg (fun v=>H v) (act_add ..)).trans (map_add ..)⟩,fun x y=> (congrArg (fun v=>H v) (act_smul ..)).trans (map_smul ..)⟩
 let M:=K.toContinuousLinearMap
 have hf:serum U R A D F w=fun z=>M (f z):=funext fun z=> showUp U A w p _ _
 have hg:serum U R A (reduce o D) (reduceK o F) w=fun z=>M (g z):=
    funext fun z=> showUp U A w p _ _
 rw [hf,hg]
 exact ((d.graph M).tip l (List.Sublist.refl _)).symm
end YM.CF.Merino.Coin

