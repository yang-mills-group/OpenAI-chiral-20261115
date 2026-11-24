import YM.SU5.Gleam.Stow
import GaugeFieldConstruction.Sierra
import YM.SU5.FiniteGaugeData.Pannier.Sketch
import YM.SU5.Fineness.Stitch
set_option autoImplicit false
set_option maxHeartbeats 35000
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
open BProof.PricePort Gleam.clocks
private lemma grows_pan (d:Grace K R L) (x:ℝ)(t:ℕ): ∀ᶠ s in atTop, t*⌈clocks.tileN (hat R.L x s)⌉₊ ≤ R.L.val^s:=by
 let a:= billX R.L; let b(s:ℕ):= R.L.val ^ s
 let V(s):= hat R.L x s; let h:= stage_slope d x
 -- compare r^3 ≤ V at even huge s. pay arbitrary linear ≤ b
 have hf:1 < (R.L.val:ℝ):= by exact_mod_cast (show 1 < R.L.val by have t:=d.tallX; omega)
 have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hf
 have hp':Tendsto (fun i:ℕ=> ((t:ℝ)*2)* V i / (R.L.val:ℝ)^i) atTop (𝓝 0):=by
    have hh := ht.const_mul a; have hl:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=> x) (tendsto_pow_atTop_atTop_of_one_lt hf); let H := (hl.add hh).const_mul ((t:ℝ)*2); have he: Tendsto (fun i:ℕ => ((t:ℝ)*2)*(x/(R.L.val:ℝ)^i + a*((i:ℝ)/(R.L.val:ℝ)^i))) atTop (𝓝 0):=by simpa only [pow_one,mul_zero,add_zero] using H
    refine he.congr ?_; intro i; unfold V hat a; ring
 have hw: ∀ᶠ s in atTop,clocks.tileN (V s) ≤ V s:=by
    filter_upwards [h.eventually_gt_atTop 1] with s q; have hh:0 < V s:=zero_lt_one.trans q
    rw [clocks.tileN,Rrp_out _ (V s) hh]; exact (Real.rpow_le_self_of_one_le q.le (by norm_num [gratuity])) -- tune
 filter_upwards [hw,h.eventually_gt_atTop 1,hp'.eventually (ge_mem_nhds zero_lt_one)] with s v w p
 have hp: (⌈clocks.tileN (V s)⌉₊:ℝ) ≤ 2* V s:= by have ht:= (Nat.ceil_lt_add_one (show 0≤ clocks.tileN (V s) from (BProof.coin_pos ..).le)).le; linarith only [ht,v,w]
 have hD:(t:ℝ)*(⌈clocks.tileN (V s)⌉₊:ℝ) ≤ (R.L.val:ℝ)^s:= by have ht:= (div_le_one (show 0< (R.L.val:ℝ)^s by positivity)).mp p; change _ * V s ≤ _ at ht; linarith only [ht,mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (α:=ℝ) t)]
 exact_mod_cast hD

lemma send_wall_side {L:Side} (h:1<L.val){s x:ℕ}(x0:0<x)(p:x ≤ L.val^s):∃ i ≤ s, x ≤ L.val^i ∧ L.val^i≤ L.val*x:=by
 induction s with
 | zero=> exact ⟨0,le_rfl,p,by rw [pow_zero]; exact Nat.mul_pos (by omega) x0⟩ -- nat positivity?
 | succ s ih =>
    by_cases f:x≤ L.val^s
    · obtain ⟨i,p,h,v⟩:= ih f; exact ⟨i,by omega,h,v⟩
    exact ⟨_,le_rfl,p,pow_succ' .. |>.trans_le (Nat.mul_le_mul_left _ (le_of_not_ge f))⟩
private lemma canopy_Q (P:Preparation): ∀ᶠ s in atTop,∀ m:Side, let N:=More (P.Ctor m s); ∃ W:Side, Odd W.val ∧ clocks.Marked (hat P.R.L P.x s) W P.R.L ∧ ∃ c:Side,∃ R': Ratio c N, 2*(R'.count.val+1)< N.val ∧ R'.count=W:=by
 -- requirement x≥0 only unused? change grows_pan
 let L:=P.R.L; let X(s):= ⌈clocks.tileN (hat P.R.L P.x s)⌉₊; have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 filter_upwards [grows_pan P.V P.x (8*L.val), ((BProof.PricePort.Rrp_high (p:=show 0<gratuity by norm_num [gratuity])).comp (stage_slope P.V P.x)).eventually_ge_atTop 1] with s u v m N
 obtain ⟨i,p,g,w⟩:= send_wall_side ht (x:=X s) (Nat.ceil_pos.mpr (BProof.coin_pos ..)) ((show X s ≤8*L.val* X s from le_mul_of_one_le_left (by positivity) (by omega)).trans u)
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨W, (by rw [he]; exact Odd.pow P.R.odd_side), ⟨?_,?_⟩, c,Q,?_,rfl⟩
 · exact (Nat.le_ceil (clocks.tileN (Vale.hat P.R.L P.x s))).trans (show (X s:ℝ) ≤ W.val from Nat.cast_le.mpr g)
 · let z:= clocks.tileN (Vale.hat P.R.L P.x s); have hz: (W.val:ℝ) ≤ L.val*(X s:ℝ):=by exact_mod_cast w
   have hc:(X s:ℝ) ≤ 2*z:=by
      have hi:(X s:ℝ) ≤ z+1:=(Nat.ceil_lt_add_one (BProof.coin_pos ..|>.le)).le
      change 1 ≤ z at v; linarith only [hi,v]
   change (W.val:ℝ) ≤ 2* (L.val:ℝ)*z
   linarith only [hz,mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (α:=ℝ) L.val)]
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 8*L.val*X s ≤ L.val ^s at u
 have hp: L.val^i≤ L.val*X s:= w
 have hl: L.val^i≥1:= one_le_pow₀ ht.le
 nlinarith only [hl,hp,u]


namespace Papal
open BProof.PricePort
local notation "Xq" s:max => Vale.hat P.R.L P.x s
-- tile independently of beta but on same periods. Do not choose alternative histories.
theorem autumn_poses : ∀ᶠ s:ℕ in atTop,∀ i:ℕ,∃ c:Side, ∃ R:Ratio c (More (count Y s i)), clocks.Marked (Xq s) R.count P.R.L ∧ Odd R.count.val ∧ 2*(R.count.val+1)<(More (count Y s i)).val ∧ Nonempty (Forest R):=by
 filter_upwards [canopy_Q P] with s x i; obtain ⟨W,g,t,c,r,u,hX⟩:= x (Y.ir i); exact ⟨c,r,hX.symm ▸ t,hX.symm ▸ g,u,Tree.select r (hX.symm ▸ g)⟩
abbrev receipt_P (s i k:ℕ):= Real.exp (Fineness.gaugedBase P.L (gram Y s i k).beta (More (count Y s i)) (P.V.L.H (Y.uv k-s)) + saveZ (Xq s) *sites (count Y s i))
-- At height over tilted emissaries. retain identity cliff for the full glyph.
lemma actual_pan : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤Y.uv k→
 let N:= count Y s i; let X:= Xq s; let H:=P.V.L.H (Y.uv k-s); let G:=gram Y s i k
 ∃ (B:G.path.Bounds G.funds P.K.top.width P.K.top.paths P.V.W.bar)(Za:Attached H G.path),
  ∀ {c:Side}(Q: Ratio c (More N)), clocks.Marked X Q.count P.R.L → Odd Q.count.val → 2*(Q.count.val+1)< (More N).val→
   ∀ (T:Forest Q) (κ τ ξ z w:ℝ)(φ: Pane N→ ℝ), Envelope φ →
     κ ≤ tauTicket P.K.top.clip G.beta X/8 → τ ≤ boldTicket P.K.top.clip G.beta X/8 → ξ ≤ tauTicket P.K.top.clip G.beta X/8 → z ≤ boldTicket P.K.top.clip G.beta X/8 →
     ModerateP B Za G.p T (clocks.height X) (badgeDust X) G.beta (suitCost P.R.L X) w ξ z φ →
   (∫ V:Pane N, aggregateA G.path G.p G.funds G.beta κ τ (badgeDust X) T φ V∂prior SU.group (More N)) ≤ receipt_P Y s i k * Real.exp w:=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a:=|K|; let h:= P.chart; let J:= P.L
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le
 filter_upwards [(stage_slope P.V P.x).eventually (harvest_volume (R:=R') P.chart P.K.top.clip (V.L.mood 0).width hv V.W.bar a (abs_nonneg K) P.R.L)] with s q i k p N X H G
 let n:= More N; let F:=Y.uv k - s; let A:= gram Y s i k
 obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k p; have hV: G.p.threshold=temp X:= he ▸ (Y.meter.boot s).1
 have hm:=P.V.L.roof F; let Q:=V.L.path F; have hJ: ∀ i: Exterior.Body 1 n,(Precision.K (H.metric.acts n)) i i ≤ a :=fun i=> (YM.Fineness.stairEstimate H P.K.width.le hm.1.2.1 i).trans (le_abs_self K)
 let B:=V.L.mood F; let Z:= V.L.tied F; change G.path=Q at hT; change G.funds=P.K.top.clip at e
 rw [hT,e]
 refine ⟨B,Z,?_⟩
 intro c R i' g h T κ τ ξ z w φ u hκ hτ hξ hz Y'
 apply (q G.beta f.1 f.2 R i' g h G.p hV Z B V.W.reserve (hm.2.1 n) hJ T κ τ hκ hτ ξ z w φ u hξ hz Y').trans_eq
 unfold receipt_P; rw [← Real.exp_add]; exact congrArg Real.exp (by unfold Gleam.Roof Fineness.gaugedBase; rw [Pannier.shadowLie,sites_as_price])
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
