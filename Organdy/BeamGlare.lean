import YM.SU5.Exchange.Stack.Racket
import Organdy.MixGlare
/- Adapted from YM/SU5/Exchange/Stack/Racket, strengthening fences to movers. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Palace
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Organdy
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v s t Nτ:ℝ}{l q B:ℕ}{p:BudgetPoint}
local notation "Ω"=> Single N
open Sault Leaf
variable {P W:SOp N}{K:Scree.Loom N}{V M:phy N}{h:ℝ}
-- static emission reach. tail activation by shared strict mask on CORE Λ≥shell
variable {O : Site N}
local notation "Θt"=> (offsetMask p.B O)
local notation "Bτ"=> (grooveB l p (node O))
variable {J T:Axis→SOp N}{k:ℕ}(Hx:CrownCar P W O k B a d b)(CV:DockPulse p K t d a h s l q)(HP:Staffer P W d)
variable (hJ:∀ i:Axis,Trunk (node O) (J i) k a b d) (vJ:∀ i:Axis,Soak (node O) (T i) a v d) (hX:Trunk (node O) X k a b d) (hY:Soak (node O) Y a v d)
variable (kV: ∀ i:Axis,∀ z:Openc (More N) d,spur (millIntro P W) O i B z.val=J i z.val+T i z.val)
variable (zV: ∀ z:Openc (More N) d,(P z.val-tickA N)*windmill O B=X z.val+Y z.val)
variable (xP:Solo a c P d)(wP:Solo a c W d)
variable (wB:p.B+2*B ≤ l*p.B)
include CV xP wP
lemma barSale :let L:= treeEarnings l p s h a c*wζ a B + huePay l p s h a B; Fence P W K p q l (node O) h s (barS0 N B O) L L:=by
 intro L; let V:=voidΛ N B O; let A:= windmillCost (d:=d) O B CV.hint.le
 have ht:= (trimQ h CV xP wP A).sub (glowTrace h CV (aura_Y A (Tap.soil_tick (N:=N) a d) CV.hint.le)); -- tune
 simp only [List.length_ofFn] at ht; exact ht

omit xP wP
include HP kV zV
include CV HP kV zV wB
include xP wP hJ hX hY vJ
lemma taught : let L:=veilPay l p s h a c b B; let S:=tailPay l p s h a c v B
 Fence P W K p q l (node O) h s (puffLine K p O J X B) (κfront l p s h a c B+S+(L+L)) S:=by
 intro L S; let Yx:=puffLine K p O J X B; let V:=frontK P W B O K; have hp: Fence P W K p q l (node O) h s V (κfront l p s h a c B) 0:= spinPlasma h CV xP wP (windmill O B) (show Soak _ _ a (wζ a B) _ from (show Soak _ _ _ _ _ from windmillCost O B CV.hint.le)) -- tune
 let g:=squarePerk (B:=B) O CV xP wP vJ
 have hz: Fence P W K p q l (node O) h s (houseK p Bτ Yx) (κfront l p s h a c B+S) S:=by
    rw [show houseK p Bτ Yx= _ from attachLamp CV HP kV zV wB]; have H:= (hp.sub ((glowTrace h CV hY).arc g)).aft (Subset.refl _)
    rw [zero_add] at H; exact H
 have hv: Fence P W K p q l (node O) h s Yx L L:= (((glowTrace (P:=P) (W:=W) h CV hX.pay).sub (barSale CV xP wP)).aft (offsetFit O O (by rw [separation_self]; omega) wB)).arc (mantlet O CV xP wP wB fun x=> (hJ x).pay)
 have hx: houseK p Bτ Yx+(Yx-houseK p Bτ Yx)=Yx:=by abel
 have HE:= hz.arc (hv.tee (Subset.refl _)); rw [hx,add_zero] at HE; exact HE
end YM.CF.Swell.Palace
