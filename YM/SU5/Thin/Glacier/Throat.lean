import YM.SU5.Thin.Glacier.Slopes
import YM.SU5.Thin.Press.Pink
import YM.SU5.Thin.Glacier.Solar
import YM.SU5.Gleam.Stow
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open clocks
variable {L':Side}
structure Portal {c n:Side} (r: Ratio c n)(x:ℝ)(L:Side) : Prop where
 odd : Odd r.count.val
 span : starSpan x r.count.val L
 ample : 2*(r.count.val+1)< n.val
lemma gearing {L:Side} (h:1<L.val){s x:ℕ}(x0:0<x)(p:x ≤ L.val^s):∃ i ≤ s, x ≤ L.val^i ∧ L.val^i≤ L.val*x:=by
 induction s with
 | zero=> exact ⟨0,le_rfl,p,by rw [pow_zero]; change 0<L.val*x; positivity⟩ -- nat positivity?
 | succ s ih =>
    by_cases f:x≤ L.val^s
    · obtain ⟨i,p,h,v⟩:= ih f; exact ⟨i,by omega,h,v⟩
    exact ⟨_,le_rfl,p,pow_succ' .. |>.trans_le (Nat.mul_le_mul_left _ (le_of_not_ge f))⟩
lemma winters_port (P:Preparation): ∀ᶠ s in atTop,∀ m:Side, let N:=More (P.Ctor m s); ∃ c:Side,∃ R': Ratio c N, Portal R' (hat P.R.L P.x s) P.R.L:=by
 -- requirement x≥0 only unused? change grows_spread
 let L:=P.R.L; let X(s):= ⌈averge (hat P.R.L P.x s)⌉₊; have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 have he:1<(L.val:ℝ):=by exact_mod_cast ht
 have hh:Tendsto (fun i:ℕ=> (16*L.val:ℝ)* (hat P.R.L P.x i/(L.val:ℝ)^i)) atTop (𝓝 0):=by simpa only [zero_add,mul_zero] using (head_geo he P.R.L P.x 0).const_mul (16*L.val:ℝ)
 filter_upwards [(stage_slope P.V P.x).eventually_ge_atTop 1, hh.eventually (ge_mem_nhds zero_lt_one)] with s k h m N
 let x:=hat P.R.L P.x s; let f:=averge x; have hp:1≤f:=Real.one_le_rpow k (by norm_num)
 have h0:0<X s:= Nat.ceil_pos.mpr (zero_lt_one.trans_le hp); have hl:(X s:ℝ)≤ 2*f:= (Nat.ceil_lt_add_one (zero_le_one.trans hp)).le.trans (by linarith only [hp]); have hc: f≤ x:=(Real.rpow_le_rpow_of_exponent_le k (show (1/200:ℝ)≤1 by norm_num)).trans (by change _≤x; unfold x; rw [Real.rpow_one]); have u:8*L.val*X s ≤ L.val^s:=by
    apply Nat.cast_le (α:=ℝ)|>.1; push_cast; change 16*(L.val:ℝ)*(x/(L.val:ℝ)^s) ≤ 1 at h; field_simp at h; nlinarith only [h,mul_le_mul_of_nonneg_left hl (show 0≤(L.val:ℝ) by positivity),mul_le_mul_of_nonneg_left hc (show 0≤(L.val:ℝ) by positivity)]
 obtain ⟨i,p,g,w⟩:= gearing ht h0 ((show X s ≤8*L.val* X s from le_mul_of_one_le_left (by positivity) (by omega)).trans u)
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨c,Q, (by change Odd W.val; rw [show W.val=L.val^i from he]; exact Odd.pow P.R.odd_side), ⟨Nat.le_ceil f|>.trans (Nat.cast_le.mpr g),?_⟩,?_⟩
 · apply le_trans (Nat.cast_le (α:=ℝ) |>.mpr w); rw [Nat.cast_mul]; refine (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α:=ℝ) L.val)).trans_eq ?_; change _ = 2*(L.val:ℝ)*f; ring
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 8*L.val*X s ≤ L.val ^s at u
 have hp: L.val^i≤ L.val*X s:= w
 have hl: L.val^i≥1:= one_le_pow₀ ht.le
 nlinarith only [hl,hp,u]

end LocalLimit
end Rate
end YM.CF.Py