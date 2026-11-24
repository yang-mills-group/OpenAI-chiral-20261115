import YM.SU5.Selected.Cairn.Mint
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Silks
namespace Giant
variable (A:Giant) {N:Side}
local notation "S" t:max=> modesIn N (park N t)
local notation "Π" => cutM (Tset N)
variable (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T] (P:Society T) (b:Bool)(C:ℝ)(M:Tulip.Male) (U:Pane N)
def patio (b:Bool):= if b then A.ascX else A.ascY
local notation "hp" t:max=> hand t Π
local notation "α" => A.hub
local notation "u'" => (wrap (More N) α)
local notation "Y"=> A.powerL
local notation "L"=> A.LHS P b C
local notation "Rh"=> A.RHS Z P C
local notation "W"=> A.bW
noncomputable def filmL := dressedK (wrap (More N) (anchorX A b)) (A.LHS P b C) U
noncomputable def filmR := dressedK (wrap (More N) (anchorY A)) (A.RHS Z P C) U
noncomputable def filmV := dressedK (wrap (More N) A.anchorY) (A.RES Z P M C) U
variable (a:Year A Z)(n:A.tokenS < N.val)
lemma labelL : Contained (labelQ N P.qu.kin) (filmL A P b C U):=by
 unfold filmL LHS; rw [starb]; exact holds_label _ _ _ ((A.clan P _).smul _)
lemma labelR : Contained (labelQ N P.qu.kin) (filmR A Z P C U):= holds_label _ _ _ ((A.clan P _).smul _)
lemma floraN : Contained (S A.ascX) (filmL A P b C U):=holdsK _ _ _ U ((shore_x A P b).smul _)
include a in
lemma floraY : Contained (S A.ascY) (filmR A Z P C U):=holdsK _ _ _ _ ((horn_y A Z P a).smul _)
lemma floraH : Contained (S A.Core) (filmV A Z P C M U):= holdsK _ _ _ U ((horns A Z P).smul _)
lemma floral (i:A.Block)(t:Bool): Contained (S (A.Knot t)) (yoke (A.filmL P b C U) i t):= by
 unfold filmL; rw [show yoke (dressedK _ _ _) _ _= dressedK _ (yoke (L) i t) U from Matrix.mul_assoc ..]; apply holdsK; unfold LHS yoke; rw [Matrix.smul_mul]; exact (shoreX A P b i t).smul _ -- tune ν
lemma flora_pitch : hp true * filmL A P b C U = filmL A P b C U:= by apply holdsT; unfold LHS; rw [Matrix.mul_smul,pitchN]
variable {M C} {δ γ:ℝ} (g:Pride A Z C δ γ M N)
include g
lemma snow : Π* filmV A Z P C M U= filmR A Z P C U:=by unfold filmV filmR dressedK; rw [←peels_m Π _ (tradew N _) (gauge_frostT ..),highPitch A Z P g] -- peels_m orientation? inspect
lemma fluf : hp false * filmR A Z P C U= filmR A Z P C U:=by unfold hand; rw [if_neg Bool.false_ne_true, ←snow A Z P U g,←Matrix.mul_assoc,(cutM_idp _).isIdempotentElem]
omit g
variable {p q:Pane N}
include n
lemma widest : 4*W < (More N).val:= by unfold tokenS at n; change _< N.val * 2; omega
lemma evenL (c:ℝ): LocalOn (R:=Per (More N)) ↑(park N A.ascX) (filmL A P b c):= fun x y h=>parks_at _ _ _ (stamps_loc W (A.anchor_here b) ((A.nudge.trans A.portS).trans A.portT) (A.widest n) h) ((shore_x A P b).smul _)
include a
lemma evenR (c:ℝ): LocalOn (R:=Per (More N)) ↑(park N A.ascY) (filmR A Z P c):=fun x y h=> parks_at _ _ _ (stamps_loc W A.anchor_dawn ((A.nut.trans A.portS).trans A.portT) (A.widest n) h) ((horn_y A Z P a).smul _)
omit a n
variable (i:A.Block)(c:ℝ)(t:Bool)
local notation "uL"=> wrap (More N) (A.anchorX b)
local notation "uR"=> wrap (More N) A.anchorY
lemma yoke_spin {Idx β κ : Type}[Fintype Idx][DecidableEq Idx][Fintype β][DecidableEq β][Fintype κ][LinearOrder κ] (i:Idx)(t:Bool)(Q:Op κ)(F:Mint.Pull κ (Idx × β)): Q*yoke F i t=yoke (Q*F) i t:= (Matrix.mul_assoc ..).symm
lemma aweL (G:Seat N → SU.E) : yoke (filmL A P b c (gauge G U)) i t*(P.arm (G (uL))).val=(tradew N G).val*yoke (filmL A P b c U) i t:=by
 unfold filmL dressedK; rw [← yoke_spin, ←yoke_spin i]; apply (pennant (uL) G _ U _); unfold yoke LHS; rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul]; congr 1; rw [starb]; exact yoke_court A P i t _ _
lemma aweR (G:Seat N → SU.E) : yoke (filmR A Z P c (gauge G U)) i t*(P.arm (G (uR))).val=(tradew N G).val*yoke (filmR A Z P c U) i t:=by
 unfold filmR dressedK; rw [← yoke_spin, ←yoke_spin i]; apply (pennant (uR) G _ U _); unfold yoke RHS; rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul]; exact congrArg (fun q:WRect _ _=> (Up c:ℂ) • q) (yoke_court ..)
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms evenL
#print axioms evenR
#print axioms fluf
#print axioms aweL
#print axioms aweR
#print axioms floral
#check @aweL
