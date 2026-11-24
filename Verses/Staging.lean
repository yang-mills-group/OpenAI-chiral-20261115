import Verses.Billing
import Verses.Fusing
import LusterS.Husk
import YM.SU5.Velvet.Hemline
import Refrain.Seismic
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
-- align block.Log. horizon.
lemma cap_physic :∀ᶠ s in atTop,∀ i:ℕ,let N:= More (P.Ctor (Y.ir i) s);∃ w:ℕ,cliffsF (ℶ s)≤ 2*w+1 ∧ 2*w+1≤ wallsF pio (ℶ s)∧∃ (c:Side)(r: Lattice.Ratio c N),r.count.val=2*w+1∧2*(w+1)<N.val:=by
 let L:=P.R.L; have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 have he:= Flint.elevation.and (stake_block L)
 filter_upwards [high_physical P,(turnover P).eventually he] with s u v i N
 let x:=ℶ s; let b:=cliffsF x
 have he0:0<b:=v.1.1
 have hl: b≤ wallsF L x:=Nat.le_mul_of_pos_left _ L.property
 obtain ⟨a,p,g,w⟩:= powers_cover he0 ht (p:= ((hl.trans v.2).trans ((Nat.le_mul_of_pos_left _ (by decide: (0:ℕ)<8)).trans u)))
 let W:=L^a; have he:W.val=L.val^a:=rfl; obtain ⟨z,hz⟩:=Odd.pow P.R.odd_side (n:=a)
 let c:= More (P.Ctor (Y.ir i) (s-a)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-a)*P.R.L^a by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q:Lattice.Ratio c N:=⟨W,congrArg Subtype.val H⟩
 rw [show L.val^a=2*z+1 from hz] at g w
 refine ⟨z,g,w,c,Q,hz,?_⟩
 change 2*(z+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh (Y.ir i) L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ (Y.ir i).property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 2*z+1 ≤ wallsF L x at w; have he: 2*z+1 ≤ walls L x:= w.trans v.2; change 8*walls L x ≤ L.val^s at u; omega

abbrev metro (j:ℕ)(w:ℕ):ℝ := ((4*((j+4)*2+1:ℕ)^4:ℕ):ℝ)*((w+1)+(w+1)+1:ℕ)^4*(2*(w:ℝ)+1)^4
lemma metro_mono (j:ℕ){v w:ℕ}(t:v≤w):metro j v≤ metro j w:=by unfold metro; gcongr
lemma metro_budget (j:ℕ)(L:Side)(c:ℝ):∀ᶠ x in atTop,c*metro j (wallsF L x) ≤ ((walls L x:ℕ):ℝ)^4:=by
 let K:=caps_grade L
 have hh:= (block (1:ℝ)).grow (b:=ratioV) (by norm_num [ratioV,tauA])
 let v:= K.plus hh; let g:= (v.plus v).plus hh; let f:=(K.scaleB 2).plus hh
 let D(x):= (fun x=>metro j (wallsF L x)) (x:ℝ)
 have hp: Grade (ratioV*8) D:=by
    unfold D metro; push_cast
    apply Grade.cash (Grade.grow (Grade.scaleB (4*((j:ℝ)+4)^0*(((j:ℝ)+4)*2+1)^4) ((g.pwr 4).mul (f.pwr 4))) (by norm_num [ratioV,tauA]))
    filter_upwards with x; apply le_of_eq; congr 1; change _= (4*((j:ℝ)+4)^0*((_+_)*2+1)^4)* ( ( ((wallsF L x:ℕ):ℝ)+1+((((wallsF L x:ℕ):ℝ)+1))+1)^4*((2*(wallsF L x:ℝ)+1)^4)); unfold wallsF cliffsF; push_cast; ring
 filter_upwards [((hp.scaleB c).cost_p (b:=tauA*4) (by norm_num [ratioV,tauA])),eventually_gt_atTop (0:ℝ)] with x h hx
 apply (le_abs_self _).trans (h.trans _)
 rw [Real.rpow_mul hx.le]; norm_num; have hu: x^tauA≤ (walls L x:ℝ):= (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_mul_of_pos_left _ L.property))
 exact pow_le_pow_left₀ (by positivity) hu _
lemma sticker_mono {m n:ℕ}(p:m≤n){t:ℝ}(v:0≤t):sticker m t≤ sticker n t:=by unfold sticker Circa; have h:=BPress.Spin.sphereRate_cost.positive; gcongr

end Papal
end LocalLimit
end Rate
end YM.CF.Py
