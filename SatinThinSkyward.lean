import YM.SU5.Gleam.Stow
import SatinThinOver
/-! # city qualifies arbitrarily high. Variant of Stow. -/
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
open Gleam.Tempest Worth 
private lemma grows_city (d:Grace K R L) (x:ℝ)(t:ℕ): ∀ᶠ s in atTop, t*(Worth.Pays.terrace (hat R.L x s)).val ≤ R.L.val^s:=by
 let a:= billX R.L; let b(s:ℕ):= R.L.val ^ s
 let V(s):= hat R.L x s; let h:= stage_slope d x
 -- compare r^3 ≤ V at even huge s. pay arbitrary linear ≤ b
 have hz:∀ᶠ y:ℝ in atTop, ((Worth.Pays.terrace y).val:ℝ)≤ y:= by
    filter_upwards [Worth.Pays.leap (p:=0) (q:=0) Worth.Pays.terrace_size (Or.inl (by norm_num [r_width] : r_width < 1)),eventually_gt_atTop (0:ℝ)] with y hy ht; exact hy.trans_eq (BProof.coinY ht)
 have hf:1 < (R.L.val:ℝ):= by exact_mod_cast (show 1 < R.L.val by have t:=d.tallX; omega)
 have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hf
 have hp':Tendsto (fun i:ℕ=> (t:ℝ)* V i / (R.L.val:ℝ)^i) atTop (𝓝 0):=by
    have hh := ht.const_mul a; have hl:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=> x) (tendsto_pow_atTop_atTop_of_one_lt hf); let H := (hl.add hh).const_mul (t:ℝ); have he: Tendsto (fun i:ℕ => (t:ℝ)*(x/(R.L.val:ℝ)^i + a*((i:ℝ)/(R.L.val:ℝ)^i))) atTop (𝓝 0):=by simpa only [pow_one,mul_zero,add_zero] using H
    refine he.congr ?_; intro i; unfold V hat a; ring
 filter_upwards [h.eventually_gt_atTop (0:ℝ),h.eventually hz,hp'.eventually (ge_mem_nhds zero_lt_one)] with s w v f
 exact_mod_cast (mul_le_mul_of_nonneg_left (show ((Worth.Pays.terrace (V s)).val:ℝ) ≤ V s from v) (Nat.cast_nonneg (α:=ℝ) t)).trans ((div_le_one (by positivity)).mp f)
lemma send_lure_side {L:Side} (h:1<L.val){s x:ℕ}(x0:0<x)(p:x ≤ L.val^s):∃ i ≤ s, x ≤ L.val^i ∧ L.val^i≤ L.val*x:=by
 induction s with
 | zero=> exact ⟨0,le_rfl,p,by rw [pow_zero]; change 0<L.val*x; positivity⟩ -- nat positivity?
 | succ s ih =>
    by_cases f:x≤ L.val^s
    · obtain ⟨i,p,h,v⟩:= ih f; exact ⟨i,by omega,h,v⟩
    exact ⟨_,le_rfl,p,pow_succ' .. |>.trans_le (Nat.mul_le_mul_left _ (le_of_not_ge f))⟩
lemma ciViGeometry (P:Preparation): ∀ᶠ s in atTop,∀ m:Side, let N:=More (P.Ctor m s); ∃ W:Side, Odd W.val ∧ respire (hat P.R.L P.x s) P.R.L W.val ∧ ∃ c:Side,∃ R': Ratio c N, 2*(R'.count.val+1)< N.val ∧ R'.count=W:=by
 -- requirement x≥0 only unused? change grows_city
 let L:=P.R.L; let Xc(s):= Worth.Pays.terrace (hat P.R.L P.x s); have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 filter_upwards [grows_city P.V P.x (8*L.val)] with s u m N
 obtain ⟨i,p,g,w⟩:= send_lure_side ht (Xc s).property ((show (Xc s).val ≤8*L.val* (Xc s).val from le_mul_of_one_le_left (by positivity) (by omega)).trans u)
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨W, (by rw [he]; exact Odd.pow P.R.odd_side), ⟨g,w⟩, c,Q,?_,rfl⟩
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 8*L.val*(Xc s).val ≤ L.val ^s at u
 have hp: L.val^i≤ L.val*(Xc s).val:= w
 have hl: L.val^i≥1:= one_le_pow₀ ht.le
 nlinarith only [hl,hp,u]
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.ciViGeometry
