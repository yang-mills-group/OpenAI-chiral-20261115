import YM.SU5.Selected.Twirl.Floss
import YM.SU5.Selected.Cor.Clasp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
namespace Mezz
open Payroll Caste Silks
local notation "ⅈ" => Complex.I
open Stencil
open Nacre
open Afterglow Afterglow.Tower.SlabMark
variable {N:Side}(n:ℕ)(A:Mezz)(b:Bool)
variable {u:Type}[Fintype u][DecidableEq u](P:Society u)(i:A.Lot)(U:Pane N)
variable (v:A.ride=0)(g:n ≤ A.passW){X Y:Coast→ Wq A.marks} (Z:Coast→ Wq A.marks)(t:Crest.Airy.Lift A.marks n X Y)(C:ℝ)
local notation "A'"=> A.pumped n
local notation "χ" y:max=> shuffleG n y
local notation "Ω" => wrap (More N) (A.grape i.1 true)
local notation "κ" => (shuffleW n N)
local notation "λ₀" => (twist (quantU (shuffleW n N)))
open Lantern
private lemma tape_I {n q:Type*}[Fintype n][LinearOrder n][Fintype q][DecidableEq q](X:WRect n q)(i:Fintype.card q=10): tape true (ⅈ • X)= -tape true X:=by
 have he: tape true (ⅈ • X)= tone true (ⅈ ^ Fintype.card q) • tape true X :=by
    calc _ = tape true (X*(ⅈ • (1:Op q))):= by rw [Matrix.mul_smul,Matrix.mul_one]
         _ = tone true (ⅈ ^ Fintype.card q) • tape true X:=by rw [wave_det,Matrix.det_smul,Matrix.det_one,mul_one]
 apply he.trans; rw [i,show (10:ℕ)=2*5 from rfl,pow_mul,Complex.I_sq]; change star ((-1:ℂ)^ (5:ℕ)) • _=_; norm_num
private lemma tape_scaled {n q:Type}[Fintype n][LinearOrder n][Fintype q][DecidableEq q](X Z:WRect n q)(k:pulseNode): rune k (ⅈ • X) (ⅈ • Z)= ⅈ • rune k X Z:=by unfold rune; rw [smul_add,smul_comm]
include t g v
lemma plays : ((A').spanOne P true i Y Z C U) = - (λ₀ (A.spanOne P true i X Z C (χ U))):=by
 unfold spanOne; simp_rw [loreP _ _ _ P.club_card,map_sum,twist_scalar]; rw [←sum_neg_distrib]; apply sum_congr rfl; intro j _; rw [honed n A true _ _ _ v g Z t,honed n A false _ _ _ v g Z t,tape_scaled,tape_I _ P.club_card,tape_cov,smul_neg]; unfold rune; rw [Matrix.mul_add,Matrix.mul_smul]
#check plays
omit t g v in
lemma settles : (A').matinee (N:=N) P false i Y Z C=A.matinee P false i X Z C:=by funext ⟨z,i⟩; unfold matinee spanOne; rw [honor_early,honor_early] -- lean chooses X? Y implicit output uninstantiated; fix
lemma hindsight {M:Tulip.Male}{w:ℕ}{ε:ℝ}(c:A.Caste (N:=N) M C ε w X Z): (A').matinee (N:=N) P true i Y Z C= -reflMark 3 (n:ℤ) (reflMark 3 0 (A.matinee P true i X Z C)):=by funext x; rw [Pi.neg_apply, hover n _ x (A.marquee_one P true i X Z C c) ]; exact plays n A P i x.1 v g Z t C
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms plays
#print axioms settles
#print axioms hindsight
