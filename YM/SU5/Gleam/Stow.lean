import YM.SU5.Gleam.Innate
import YM.SU5.FiniteGaugeData.Pannier.Sketch
import YM.SU5.Fineness.Stitch
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
private lemma grows_spread (d:Grace K R L) (x:ℝ)(t:ℕ): ∀ᶠ s in atTop, t*(radiusB (hat R.L x s))^3 ≤ R.L.val^s:=by
 let a:= billX R.L; let b(s:ℕ):= R.L.val ^ s
 let V(s):= hat R.L x s; let h:= stage_slope d x
 -- compare r^3 ≤ V at even huge s. pay arbitrary linear ≤ b
 have hz: Tendsto (fun i:ℕ=> (radiusB (V i):ℝ)^3/(V i)) atTop (𝓝 0):=by simpa only [Real.rpow_one,Function.comp_def,V] using (Work.E09.radiusB_small 1 zero_lt_one 3 |>.tendsto_div_nhds_zero).comp h
 have hf:1 < (R.L.val:ℝ):= by exact_mod_cast (show 1 < R.L.val by have t:=d.tallX; omega)
 have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hf
 have hp':Tendsto (fun i:ℕ=> (t:ℝ)* V i / (R.L.val:ℝ)^i) atTop (𝓝 0):=by
    have hh := ht.const_mul a; have hl:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=> x) (tendsto_pow_atTop_atTop_of_one_lt hf); let H := (hl.add hh).const_mul (t:ℝ); have he: Tendsto (fun i:ℕ => (t:ℝ)*(x/(R.L.val:ℝ)^i + a*((i:ℝ)/(R.L.val:ℝ)^i))) atTop (𝓝 0):=by simpa only [pow_one,mul_zero,add_zero] using H
    refine he.congr ?_; intro i; unfold V hat a; ring
 filter_upwards [h.eventually_gt_atTop (0:ℝ),hz.eventually (ge_mem_nhds zero_lt_one),hp'.eventually (ge_mem_nhds zero_lt_one)] with s w v f
 exact_mod_cast (mul_le_mul_of_nonneg_left (show (radiusB (V s):ℝ)^3 ≤ V s from ((div_le_one w).mp v)) (Nat.cast_nonneg (α:=ℝ) t)).trans ((div_le_one (by positivity)).mp f)
lemma send_width_side {L:Side} (h:1<L.val){s x:ℕ}(x0:0<x)(p:x^3 ≤ L.val^s):∃ i ≤ s, x^3 ≤ L.val^i ∧ L.val^i≤ L.val*x^3:=by
 induction s with
 | zero=> exact ⟨0,le_rfl,p,by rw [pow_zero]; change 0<L.val*x^3; positivity⟩ -- nat positivity?
 | succ s ih =>
    by_cases f:x^3≤ L.val^s
    · obtain ⟨i,p,h,v⟩:= ih f; exact ⟨i,by omega,h,v⟩
    exact ⟨_,le_rfl,p,pow_succ' .. |>.trans_le (Nat.mul_le_mul_left _ (le_of_not_ge f))⟩
private lemma canopy_part (P:Preparation): ∀ᶠ s in atTop,∀ m:Side, let N:=More (P.Ctor m s); ∃ W:Side, Odd W.val ∧ clocks.moder (radiusB (hat P.R.L P.x s)) W.val P.R.L ∧ ∃ c:Side,∃ R': Ratio c N, 2*(R'.count.val+1)< N.val ∧ R'.count=W:=by
 -- requirement x≥0 only unused? change grows_spread
 let L:=P.R.L; let X(s):= radiusB (hat P.R.L P.x s); have ht:1<L.val:=by unfold L; have h:=P.V.tallX; omega
 filter_upwards [grows_spread P.V P.x (8*L.val), (stage_slope P.V P.x).eventually (Work.E08.eventual_radiusB 1)] with s u v m N
 obtain ⟨i,p,g,w⟩:= send_width_side ht v ((show X s^3 ≤8*L.val* X s^3 from le_mul_of_one_le_left (by positivity) (by omega)).trans u)
 let W:=L^i; have he:W.val=L.val^i:=rfl
 let c:= More (P.Ctor m (s-i)); have H: N=c*W:=by
    unfold c N W Ctor cell Vale.mesh CSide Cube.More; simp only [L]; rw [show P.R.L^s=P.R.L^(s-i)*P.R.L^i by rw [←pow_add,Nat.sub_add_cancel p]]; ac_rfl
 let Q: Ratio c N:=⟨W, congrArg Subtype.val H⟩
 refine ⟨W, (by rw [he]; exact Odd.pow P.R.odd_side), ⟨g,w⟩, c,Q,?_,rfl⟩
 change 2*(L.val^i+1)< N.val; apply lt_of_lt_of_le _ (show L.val^s≤N.val from (by let D:=Vale.mesh m L s; have h:L.val^s≤ D.val:=Nat.le_mul_of_pos_left _ m.property; change _ ≤ D.val*2 * P.block.val *2; exact h.trans (((Nat.le_mul_of_pos_right D.val two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)).trans (Nat.le_mul_of_pos_right _ two_pos))))
 change 8*L.val*X s^3 ≤ L.val ^s at u
 have hp: L.val^i≤ L.val*X s^3:= w
 have hl: L.val^i≥1:= one_le_pow₀ ht.le
 nlinarith only [hl,hp,u]
-- usable geometry
namespace Papal
def landedCost (Y:Course P (VolumeCape.Dream.Nimbus l))(s i k:ℕ)(κ x:ℝ) : Prop:=
 let M:= count Y s i; let A:=gram Y s i k; let Z:=P.V.L.H (Y.uv k - s)
 (∫ V: Pane M, Real.exp ( -(A.path.inChannels P.K.top.clip A.p A.beta V) + κ* Pannier.flakes A.p.threshold V ) ∂prior SU.group (More M))≤ Real.exp (Fineness.gaugedBase P.L A.beta (More M) Z + x* sites M) -- P.L name
lemma pilot_clock (κ ε:ℝ)(p: ε>0) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k→ landedCost Y s i k κ ε:=by
 let T:=P.K; let V:=P.V; let R':= (Next.Rank.Spindle.charts SU.group).some; let K:= Progress.StationaryScenes.Green.kinetic P.K.η P.K.C; let a:=|K|; let h:= P.chart; let J:= P.L; -- P.L chart?
 have hv:0 ≤ P.K.top.paths:=P.K.top.paths_pos.le -- tune
 filter_upwards [(stage_slope P.V P.x).eventually (clocks.serial P.K.top.clip R' P.chart a P.R.L (V.L.mood 0).width hv V.W.bar (abs_nonneg K) κ ε p),canopy_part P] with s q H i k ht
 let N:= count Y s i; let G:=More N; let F:=Y.uv k - s; let A:= gram Y s i k
 obtain ⟨W,g,t,c,r,u,hX⟩:= H (Y.ir i)
 obtain ⟨he,hT,e,f,_⟩:= prices_plot Y s i k ht
 have hV: A.p.threshold=temp (hat P.R.L P.x s):= he ▸ (Y.meter.boot s).1
 let Z:= P.V.L.H F; have hm:=P.V.L.roof F; let Q:=V.L.path F; have hx:T.top.clip=P.K.top.clip:=rfl
 have Hs := q W g t A.p A.beta f hV G c r u hX (V.L.tied F) (V.L.mood F) (hm.2.1 G) V.W.reserve (fun i=>?_); -- gauge align
 · unfold landedCost; have hg : ∀ V:Pane N,Gleam.angBill Q P.K.top.clip A.p A.beta κ V= Real.exp (- (A.path.inChannels P.K.top.clip A.p A.beta V)+κ* Pannier.flakes A.p.threshold V):=fun U=> by unfold Gleam.angBill; change A.path=Q at hT; rw [← hT]; rfl
   change (∫ V:Pane N,Gleam.angBill Q P.K.top.clip A.p A.beta κ V ∂prior SU.group (More N))≤ _ at Hs; simp_rw [hg] at Hs; exact Hs.trans_eq (congrArg Real.exp (show _=_ from (by unfold Gleam.Roof Fineness.gaugedBase; rw [Pannier.shadowLie,sites_as_price])))
 exact (YM.Fineness.stairEstimate Z P.K.width.le hm.1.2.1 i).trans (le_abs_self K)
lemma gauge_whole (ε:ℝ)(hε:0<ε)(κ:ℝ) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤ Y.uv k → let G:= gram Y s i k; let N:=count Y s i; ∀ (f:Orbit N→ℂ)(t:ℝ), Integrable f (city N) →
 (∀ x:Orbit N, ‖f x‖ ≤ Real.exp (-(G.path.inChannels G.funds G.p G.beta x.1) + κ*Pannier.flakes G.p.threshold x.1 + t)) → (∫ x:Orbit N,‖f x‖∂city N)≤ Real.exp (Fineness.gaugedBase P.L G.beta (More N) (P.V.L.H (Y.uv k-s))+ ε*sites N+t):=by
 filter_upwards [pilot_clock Y κ ε hε] with s q i k ht G N f t h hu
 obtain ⟨g,W,e,_⟩:= prices_plot Y s i k ht
 let ℒ:=P.K.top.clip; let H:= Real.exp t; let F(U:Pane N):=angBill G.path ℒ G.p G.beta κ U*H
 let X:= prior SU.group (More N); have hf: Integrable F X:=by
    change G.path= _ at W; unfold F; rw [W]; exact ((env_ang (P.V.L.mood (Y.uv k-s))).integrable _).mul_const _
 let kP(x:Orbit N):= F x.1; have hL:Integrable kP (city N):= ((measurePreserving_fst (μ:=X) (ν:=depot N)).integrable_comp hf.aestronglyMeasurable).mpr hf
 apply le_trans (b:=∫ u,kP u ∂city N)
 · apply integral_mono h.norm hL; intro x; apply (hu x).trans; change G.funds=_ at e; rw [e,Real.exp_add]; exact le_rfl
 rw [CF.Window.usesPrior _ hf]; unfold F; rw [integral_mul_const,Real.exp_add]; exact mul_le_mul_of_nonneg_right (q i k ht) (Real.exp_pos _).le
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.gauge_whole
