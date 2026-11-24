import YM.CF.Pith.Pole
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Larch
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
variable {X D Y Z:Support (More n)}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue Trees Bake Vow
variable {F G: Pax n}{K:Cusp n}{f g: Copy n}
variable (U: Orbit n)
variable {ι:Type*}[DecidableEq ι](W:Finset ι)(X Y Z:ι→Aura n)(F:ι→ Copy n)(G:ι→ InkD n)(A:ι→ℝ)
-- sum charges with localized movement.M. countable finite here.lag. Anchor orientation.Lo.Bold. incidence contamination $.Zκ.Translent.
abbrev Anuk (K:Cusp n)(A:Aura n →ℝ)(P:BudgetPoint)(h:ℝ):Prop:= 0≤A∧∀ i:Aura n,∀ D:Support (More n),D.Nonempty→D⊆i.val→Medal P i.val D (K i D) h (A i)
abbrev soot_T:= ∑ i∈W, Vow.stroke (X i) (Y i) (Z i) (F i) (F i)
abbrev span_W(x:Aura n):= ∑ i∈W, if Z i=x then (2:ℝ)*A i else 0
lemma march_add(P:BudgetPoint)(X:Aura n)(x y:Copy n): Vow.march P X (x+y) U=march P X x U+march P X y U:=by unfold Vow.march; split; rfl; exact (add_zero _).symm
lemma len_T(P:BudgetPoint)(X:Aura n): march P X (∑ i∈W,F i) U=∑ i∈W,march P X (F i) U:=by
 unfold Vow.march; by_cases h: pingS P.threshold X.val U.1; simp_rw [if_pos h]; rw [Finset.sum_apply]; simp_rw [if_neg h,sum_const_zero]
variable(t:∀ i∈W,(X i).val⊆(Z i).val)(u:∀ i∈W,(Y i).val⊆(Z i).val)(p:∀ i∈W, Medal P (X i).val ∅ (F i) h (A i))(v:∀ i∈W,Medal P (Y i).val ∅ (F i) h (A i))
include t u
local notation "ew"=> (soot_T W X Y Z F)
local notation "wp"=> span_W W Z A
lemma propC (x:FleetS P.threshold U.1): (∑ i∈W, march P (Y i) (F i) U)+fuelV P ew U= ∑ i∈W,march P (X i) (F i) U:=by rw [soot_T,Vow.tunes,← Finset.sum_add_distrib]; exact sum_congr rfl fun i a=>amends U _ _ _ (t i a) (u i a) (fun _ _=> rfl) x
include p v
variable (hx:0 ≤ h)
include hx
lemma amulet : Anuk ew wp P h:=by
 refine ⟨fun i=> sum_nonneg fun j l=>by split; exact mul_nonneg (by norm_num) ((p j l).wage hx); exact le_rfl, fun i D y k=>?_
 ⟩
 unfold soot_T Vow.stroke; apply Vow.migrate Z _ _ _ y _ i k -- tune
 intro j v' D l Bv; rw [sub_eq_add_neg, two_mul]
 exact (flick_M (X j) _ (t j v') hx (p j v') D).plus ((flick_M (Y j) _ (u j v') hx (v j v') D).negT) -- types
omit v t u
variable (o:ι→Seat n)(r:ℕ)(θ γ':ℝ)(ρθ:0 ≤ θ)(hK:∀ i∈W, (Z i).val⊆ halo (k*P.B) {o i})(tK:∀ i:Seat n,(∑ j∈ W with o j=i,A j)≤γ') -- bind γ' before
abbrev shine_C(k':ℕ)(θ:ℝ):= (2:ℝ)*Real.exp (θ*((k'+k'+1)^4:ℕ))
abbrev tet_B (k B:ℕ):ℝ:= ((k*B+k*B+1)^4:ℕ)
-- local.P Weight ALL K vs plus γ l.Tr.stamp.
include hK tK ρθ
local notation "Γ"=>γ'
lemma pump(x:Seat n)(htB:0<P.B): tallB (span_W W Z A) P.B θ x≤ shine_C k θ*(tet_B k P.B *γ'):=by
 unfold tallB span_W; let P':=halo (k*P.B) {x}; have he(i)(v:i∈W)(h:x∈(Z i).val):o i∈P':=by obtain ⟨k,h,v⟩:=halo_spec.mp (hK i v h); refine halo_spec.mpr ⟨_,mem_singleton_self _,?_⟩; rw [separation_comm,←mem_singleton.mp h]; exact v
 have hz(i)(v:i∈W): 2*A i *currency P.B θ (Z i).val ≤ shine_C k θ*A i:=by
    calc
       _ ≤ 2*A i *Real.exp (θ*((k+k+1)^4:ℕ)):=by apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) ((p _ v).wage hx)); exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((Corona.cover_mono (hK i v) _).trans (Corona.tile _ _ _ htB))) ρθ)
       _ = _:=by unfold shine_C; ring
 let K(i:ι):= A i; have ht: (∑ i∈P',(∑ j∈ W with o j=i,A j))≤ P'.card*γ':= by simpa using sum_le_sum fun i (_:i∈P')=>tK i
 have hδ:0 ≤ γ':=(sum_nonneg (s:=W.filter (fun j=>o j=x)) (fun i v=>(p _ (mem_filter.mp v).1).wage hx)).trans (tK x); have hU: P'.card ≤ (k*P.B+k*P.B+1)^4:= (Corona.halo_size {x} _).trans (by simp)
 have hP:0 ≤ shine_C k θ:=by unfold shine_C; positivity
 simp_rw [sum_mul]; rw [sum_comm]; apply le_trans _ (mul_le_mul_of_nonneg_left (ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hU) hδ)) hP)
 simp_rw [sum_filter (s:=W)]; rw [sum_comm (s:=P'),mul_sum]; apply sum_le_sum; intro i v
 let D':= Z i
 by_cases b': x∈ D'.val; swap
 · rw [sum_eq_zero]; swap; · intro j t; rw [if_neg (fun (s:Z i=j)=>b' ((_root_.Eq.symm (show D'=j from s)) ▸ (mem_filter.mp t).2)),zero_mul]
   apply mul_nonneg hP; refine sum_nonneg fun j t=>?_ ; split; exact (p i v).wage hx; exact le_rfl
 rw [sum_eq_single_of_mem (Z i) (mem_filter.mpr ⟨mem_univ _,b'⟩), if_pos rfl, sum_eq_single_of_mem (o i) (he _ v b'), if_pos rfl]; exact hz i v
 · exact fun y _ h=> if_neg (Ne.symm h) -- tune
 intro j _ h; rw [if_neg (Ne.symm h),zero_mul]
end YM.CF.Larch
