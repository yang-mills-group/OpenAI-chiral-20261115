import YM.CF.Vow.Fair
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
-- pay log G W at No support.K.B.H expense. Retain forced scale budget even with exp gamma posting small-er after.Scales
open Trees
variable (K W:Cusp n)(C:blazeK n)(G:Aura n→ℝ)
def fullD (i:Aura n): Finset (Support (More n)):= univ.filter fun D=>D.Nonempty∧D⊆i.val
variable (j: ArmsK P K C h)(G':∀ i:Aura n,∀ D:Support (More n),D ⊆ i.val → Medal P i.val D (W i D) h (G i))(hy:0 ≤ h)
abbrev hymn (C:blazeK n)(x:Aura n):=∑ D∈fullD x,C x D
abbrev currV (C:blazeK n)(i:Aura n)(D:Support (More n)):= if D∈ fullD i then C i D else 0
abbrev loftP (C:blazeK n)(G:Aura n→ℝ)(κ:ℝ)(u:Palot.Duo (More n)):=Sum.elim (fun i=>κ*hymn C i) G u
variable (S:Aura n)(T:Finset (Palot.Duo (More n)))(κ:ℝ)(v:1 ≤ κ)
include j hy
lemma batteryY (i:Aura n)(D:Support (More n))(p:D∈fullD i):0 ≤ C i D:= (j.price i D (mem_filter.mp p).2.1 (mem_filter.mp p).2.2).wage hy
lemma batty (i:Aura n)(D:Support (More n)):0 ≤ currV C i D:=by unfold currV; split; exact batteryY K C j hy _ _ ‹_›; exact le_rfl
include G' v
lemma guessV : ∀ i, 0 ≤ loftP C G κ i:=by
 intro i; cases i; next x=> exact mul_nonneg (zero_le_one.trans v) (sum_nonneg fun i p=>batteryY K C j hy _ _ p)
 next x=> exact (G' x ∅ (empty_subset _)).wage hy
lemma heaps : κ*(∑ D∈fullD S,pill S C G D T) ≤ ∏ i∈T, loftP C G κ i:=by
 let L:= T.toLeft; let M:=T.toRight; let H:= (fullD S).filter fun D=> lumpD T D S
 by_cases p:H=∅
 · rw [sum_eq_zero, mul_zero]; exact prod_nonneg fun i _=>guessV K W C G j G' hy κ v i
   exact fun D u=> if_neg fun h=> notMem_empty _ (p ▸ (show D∈H from mem_filter.mpr ⟨u,h⟩))
 obtain ⟨D,w⟩:=nonempty_iff_ne_empty.mpr p; let B:=(mem_filter.mp (mem_filter.mp w).1).2; let y:=(mem_filter.mp w).2
 have hx:1 ≤ L.card:=by obtain ⟨z,b⟩:=B.1; obtain ⟨u,h,_⟩:= deck_r _ _ B.2 y z b; exact card_pos.mpr ⟨_,h⟩
 let V:=∏ i∈M,G i; have hv:0 ≤ V:=prod_nonneg fun i _=> (G' i ∅ (empty_subset _)).wage hy
 let J:= fun i:Aura n=> hymn C i; have hQ: (∏ i∈T,loftP C G κ i)=(κ^L.card*(∏ i∈L,J i))*V:=by rw [← Palot.joinP T,prod_disjSum]; change (∏ i∈L,κ*J i)*V=_; rw [prod_mul_distrib,prod_const]
 rw [hQ]; let U(D):=∏ i∈L,C i (D∩i.val);
 rw [show (∑ D∈fullD S,pill S C G D T)=(∑ D∈H,U D)*V from ?_,←mul_assoc]; swap; · rw [sum_mul,sum_filter]
 apply mul_le_mul_of_nonneg_right _ hv
 refine mul_le_mul (le_self_pow₀ v (by omega)) ?_ (sum_nonneg (fun i p=> prod_nonneg (fun l q=> (j.price _ _ (stun_v S T (mem_filter.mp p).2 l q).1 inter_subset_right).wage hy))) (pow_nonneg (zero_le_one.trans v) _)
 let N:= (↥L→Support (More n)); let F(D:Support (More n))(i:↥L):= D∩ i.val.val
 have hr{A B: Support (More n)}(b:A∈H)(u:F A=F B): A⊆ B:=by
    obtain ⟨l,t⟩:=mem_filter.mp b; let g:=(mem_filter.mp l).2.2; intro i v; obtain ⟨z,hp,hZ⟩:=deck_r S T g t i v; exact (mem_inter.mp (show i∈B∩z.val from (show i∈F B (⟨z,hp⟩:↥L) from congrFun u (⟨z,hp⟩:↥L) ▸ (show i∈F A ⟨z,hp⟩ from hZ)))).1 -- tune
 let Y(X:N):=∏ i:↥L,currV C i.val (X i)
 calc
   _ = ∑ i∈H.image F,Y i:=by
      rw [sum_image fun a h b t e=> Finset.Subset.antisymm (hr h e) (hr t e.symm)]; refine sum_congr rfl fun i p=>?_ ; unfold U Y; rw [prod_subtype _ (p:=(·∈L)) (fun i=> Iff.rfl)]; apply prod_congr rfl; exact fun j _=> (if_pos (show F i j∈ fullD j.val from mem_filter.mpr ⟨mem_univ _,(stun_v S T (mem_filter.mp p).2 j.val j.property).1,inter_subset_right ⟩)).symm
   _ ≤ ∑ i:N,Y i := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> prod_nonneg fun i _=>batty K C j hy _ _
   _ = _:= by rw [Finset.prod_subtype L (p:=(·∈L)) (fun i=> Iff.rfl)]; unfold Y; rw [show ∑ i:N,_= _ from (Fintype.prod_sum (fun i:↥L=>fun t=>currV C i.val t)).symm]; apply prod_congr rfl; intro i _; unfold J hymn; simp only [currV,fullD, mem_filter,mem_univ,true_and,sum_filter]; -- tune
local notation "B'"=> Finset (Palot.Duo (More n))
local notation "gT"=> loftP C G κ
local notation "X'"=> Palot.stern ∘ Palot.dock
variable {N:ℕ}
lemma tintS(o:Seat n)(w:0≤a) : κ*(∑ i:Aura n with o∈i.val, (∑ D∈ fullD i,pill i C G D T)* currency N a i.val)≤ touches X' N gT a o T:=by
 by_cases h: ∃ i:Aura n, beatB T = beamH i.val∧ o∈ i.val
 · obtain ⟨i,p,h⟩:=h; obtain ⟨u,f⟩:= Palot.break_h X' (fun i=>(dock i).property) i T p;
   rw [sum_eq_single i,←mul_assoc]; swap; · intro z t v; rw [sum_eq_zero,zero_mul]; intro D k; unfold pill; apply if_neg; intro g; exact v (Subtype.ext ((bay_beam _).symm.trans ((congrArg Stilo.bay (g.1.symm.trans p)).trans (bay_beam _))))
   rotate_left; · exact fun v=> False.elim (v (mem_filter.mpr ⟨mem_univ _,h⟩))
   apply le_trans (mul_le_mul_of_nonneg_right (heaps K W C G j G' hy i T κ v) (Real.exp_pos _).le); rw [touches,if_pos ⟨u,f.symm ▸ h⟩, Finset.prod_mul_distrib]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> guessV K W C G j G' hy κ v i); unfold Trees.currency; rw [←f, ← Real.exp_sum]; apply Real.exp_monotone; rw [←Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ w; exact_mod_cast Ac.cover X' N u
 rw [sum_eq_zero,mul_zero]; exact turn_q _ _ (guessV K W C G j G' hy κ v) _ _ _ _
 intro i p; rw [sum_eq_zero,zero_mul]; intro D _; exact if_neg fun g=> h ⟨i,g.1,(mem_filter.mp p).2⟩
variable {γ δ q:ℝ}
lemma chisel (o:Seat n)(w:0 ≤ a)(p:Ready X' N gT a γ δ q): κ*(∑ i:Aura n with o ∈ i.val, hymn (windF C G) i*currency N a i.val)≤ γ*q^0*(1-q)⁻¹:=by
 unfold hymn windF; rw [show (∑ i:Aura n with o∈i.val, _)= (∑ T:B', ∑ i:Aura n with o∈i.val,(∑ D∈ fullD i,pill i C G D T)*currency N a i.val) from ?_,Finset.mul_sum]; apply (sum_le_sum fun i _=> tintS K W C G j G' hy i κ v o w).trans; apply le_trans _ (budget_sum (touch_tail X' N p o 0) univ); apply sum_le_sum; intro i h; simp
 rw [sum_comm]; apply sum_congr rfl; intro i t; rw [sum_comm, sum_mul]
end YM.CF.Vow
