import Anomaly.Ward.Voice
/-!
Passage on those $Z'_s$. For the finish in the spherical H reader,
need the pressure comparison *on its same actual answer*, not merely PriceBits.
Give a.e. certificate in a second mask convention (closed) suited to pressure.
This second convention not changing which Mark gets used in Y and JOINT proofs.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
noncomputable section
namespace YM.CF.Swell.Sonar
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Cube Lat Tenant Tulip Spire Scroll Scree Jet Skye Pastry Dial Fock Branch Drapes Rill Sour
open Nacre Next.Free Exterior Precision Wilson _root_.Zephyr.Chern SpectrumQ
open Ione.Clock Hove Spire Regis.Head Next.Rank.Spindle LampP
section
open scoped Matrix.Norms.Frobenius
lemma island_price (G:Gauge) :∃ r:ℝ,0<r∧∀ u:G.El,G.chord u ≤ r → ContinuousAt (G.plog ∘ G.mat) u:=by
 have ht:= G.plog_diff.eventually (by simp)
 obtain ⟨r,f,h⟩:= Next.Rank.surrounds G _ ((show Tendsto G.mat (𝓝 1) (𝓝 1) from by simpa using! G.continuous_mat.tendsto 1).eventually ht)
 exact ⟨r,f,fun u v=>(show ContDiffAt ℝ ω G.plog (G.mat u) from h (show u∈G.shell r from v)).continuousAt.comp G.continuous_mat.continuousAt⟩
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace StageQ
local notation "Γ"=> More n
local notation "χ" => fieldDir SU.group (More n) 1
local notation "Πp"=> tangD n
open PotQ
variable {b k m:ℕ}{d c α C M w a z:ℝ}{P:BudgetPoint}{K:Loom n}{X:SOp n}{T E:tableQ SU.group (More n) ℂ} {x:Site n} (R:Knit X (node x) b d α M C w m T) (L:mintQ α C d m) (H:Roof n c d k K)(hb:b+k+10 ≤ P.B)(hp:P.threshold ≤ c)

abbrev courtV(b:ℕ)(o:Site n) := halo b {node o}
abbrev mapW (b:ℕ)(o: Site n)(V:Pane n):tangD n:= paneExtendLin (node o) (wired 1 (node o) b V)
abbrev rim (P:BudgetPoint)(o:Site n) : Set (Pane n) := {V| Healthy P.threshold (courtV P.B o) V}
def themis (P:BudgetPoint)(o:Site n)(X:SOp n)(b:ℕ)(V:Pane n):ℂ:= (rim P o).indicator (fun U=> rawQ X (increment 1 (mapW b o U))) V
variable (s:Rules SU.group) (g:2*(b+1)<(More n).val)(t:b≤P.B)(q:4*(b:ℝ)*P.threshold ≤ s.c)(r:8*b*P.threshold<α)
include s g t q
lemma vetted(x:Site n)(V:rim P x):‖mapW b x V.val‖≤8*b*P.threshold ∧ Agrees (courtV b x) (spine V.val (node x)) (increment 1 (mapW b x V.val)):=by
 have ht:Healthy P.threshold (courtV b x) V.val:= disjoint_of_subset_left (Corona.halo_mono t le_rfl) V.property
 obtain ⟨v,u,H⟩:= closer s g _ ht 1 zero_lt_one P.threshold_pos q
 refine ⟨((paneExtendLin _).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (feeE _) (norm_nonneg _)).trans ?_),?_⟩
 · rw [one_mul]; exact v.trans_eq (by ring)
 intro i hv hw; let j:Dim (node x) b:=⟨i,mem_filter.mpr ⟨mem_univ _,hv,hw⟩⟩; change _=SU.group.lieExp (paneExtendLin (node x) _ j.val)*1; rw [evaluateE,mul_one]; simpa only [one_smul] using (u j).symm
variable (p:∀ u:SU.group.El,SU.group.chord u≤ z → ContinuousAt (SU.group.plog ∘ SU.group.mat) u) (hu:4*(b:ℝ)*P.threshold≤z)
include p hu
lemma bill_cont(x:Site n)(V:rim P x) : ContinuousAt (mapW b x) V.val:=by
 apply (paneExtendLin _).continuous.continuousAt.comp (f:=fun U:Pane n=>wired 1 (node x) b U)
 refine continuousAt_pi.mpr fun i=>?_ ; simp only [wired,inv_one,one_smul]
 have ht:Healthy P.threshold (courtV b x) V.val:= disjoint_of_subset_left (Corona.halo_mono t le_rfl) V.property
 let u:=spine V.val (node x) i.val; have hp:SU.group.chord u≤ z:=by unfold u; rw [spun _ _ g]; exact (played_cost (word SU.group g i) _ P.threshold_pos.le (chords _ _ _ ht g)).1.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast lengths_word SU.group g i) P.threshold_pos.le).trans hu)
 let G(z:Pane n):=spine z (node x) i.val; have hG:Continuous G:=by unfold G spine fingers Next.Rank.Spindle.leaves Lattice.gauge expandAt; fun_prop
 exact (p u hp).comp (f:=G) hG.continuousAt
include R L r
lemma certifiedCont : Measurable (themis P x X b) := by
 have hX: IsClosed (rim P x):=healthy_closed _ _ -- tune
 let S:= rim P x; let f(V: Pane n):= rawQ X (increment 1 (mapW b x V)); have hf:ContinuousOn f S:=by
    intro y v; let j:S:=⟨y,v⟩; have he: ContinuousAt (fun x:Πp=> rawQ X (increment 1 x)) (mapW b x y):=by
       let Q:=rawQ X 1; refine (((R.circle _ ((vetted s g t q x j).1.trans_lt r)).smooth.continuousAt.add continuousAt_const (g:=Function.const _ Q)).congr_of_eventuallyEq (Eventually.of_forall fun i=>?_)); exact (sub_add_cancel ..).symm -- tune
    exact (he.comp (bill_cont s g t q p hu x j)).continuousWithinAt
 exact hf.measurable_piecewise continuousOn_const hX.measurableSet -- indicator lemma
omit p hu
-- *any* chart / regional agreement within Guard enables themis mark use
include R
lemma priceFog (i:rim P x) (V:Pane n) (e:Agrees (courtV b x) i.val V)(f:Guard V d) : themis P x X b i.val=rawQ X V:=by
 let D:=fingers i.val (node x); obtain ⟨u,h⟩:= vetted s g t q x i
 unfold themis; rw [Set.indicator_of_mem i.property]
 calc rawQ X _ =rawQ X (gauge D V):= R.landsQ ⟨_,L.2.2.2.1 _ (u.trans_lt r)⟩ ⟨_,f.cov _⟩ (fun j w t=> (h j w t).symm.trans (congrArg (fun z:SU.group.El=> D j.1*z*(D (j.1+ step j.2))⁻¹) (e j w t)))
      _ =rawQ X V:= R.engage ⟨V,f⟩ D
lemma bill_gauge (V:Pane n)(C:Seat n→SU.group.El): themis P x X b (gauge C V)= themis P x X b V:=by
 have e:gauge C V∈rim P x ↔ V∈rim P x:=by simp only [rim,Set.mem_setOf,Healthy,gauge_flags]
 by_cases l:V∈rim P x
 · let i:rim P x:=⟨V,l⟩; obtain ⟨c,v⟩:=vetted s g t q x i; let Q:=increment (1:Pane n) (mapW b x V); have hc: Guard Q d:= L.2.2.2.1 _ (c.trans_lt r)
   let f:=(fingers V (node x)); let T:= gauge f⁻¹ Q; have hv: Agrees (courtV b x) V T:=by intro j w t; unfold T Lattice.gauge; change _=(f j.1)⁻¹ * Q j * ((f _)⁻¹)⁻¹; rw [← show spine V _ j=Q j from v j w t]; unfold spine Lattice.gauge; dsimp only [f]; group -- bad; tune
   rw [show themis P x X b _=rawQ X (gauge C T) from priceFog R L s g t q r ⟨_,e.mpr l⟩ _ (fun j w u=>congrArg (fun z:SU.group.El=> C j.1*z*(C (j.1+ step j.2))⁻¹) (hv j w u)) ((hc.cov _).cov _),show themis _ _ X b V=_ from priceFog R L s g t q r i _ hv (hc.cov _)]
   exact R.engage ⟨T,hc.cov _⟩ _
 unfold themis; rw [Set.indicator_of_notMem l, Set.indicator_of_notMem (mt e.mp l)]
-- use FleetS for equality in Reg consultations and ae claims *separately*.
include H hb hp
lemma nearMask (V:Pane n)(f:Rue.FleetS P.threshold V): traceMeter P K x X V=themis P x X b V:=by
 have e:V∈rim P x ↔ pingS P.threshold (courtV P.B x) V:=?_ -- tune
 by_cases w: V∈rim P x
 · obtain ⟨l,v⟩:=vetted s g t q x ⟨V,w⟩; unfold themis; rw [Set.indicator_of_mem w]; exact template_pass R H hb hp (e.mp w) _ v (L.2.2.2.1 _ (l.trans_lt r)) -- v spine direction
 unfold themis traceMeter pinMatrix; rw [Set.indicator_of_notMem w,Set.indicator_of_notMem (show V ∉ {U:Pane n| pingS P.threshold (Lattice.halo P.B {node x}) U} from (mt e.mpr w)),Matrix.trace_zero]
 exact (Rue.shoreK _ V f _)
end StageQ
end YM.CF.Swell.Sonar
