import YM.CF.Yaw.Quartz
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Eire Jet Scroll Rill.TasteZ
local notation "G_"=> SU.group
variable {n m:Side}{U: Pane n}{D:Support (More n)}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{a b t K:ℝ}
open Rill
local notation "V'"=> More n
lemma travellers (k:ℕ)(h:a ≤ K)(v:1≤a)(s:Wind t (·*·) k a)(g:Wind t (fun i _=>i⁻¹) k a)(V:E→ Pane n)(X:ℕ)(υ:Lattice.Walk)(i:Site V')(u:υ.length ≤ X)(he:Cash (X+2) b a ≤ t)(η:0≤b)(hp:∀ j:Bond V',pinPos j⊆ (visits i υ).toFinset→ Tender (fun y=>V y j) z b k): Tender (fun y=> travel (V y) i υ) z (Cash (X+2) b a) k:=by
 induction X generalizing i υ with
 | zero=> rw [show υ=[] from List.eq_nil_of_length_eq_zero (by omega)]; exact (Shake.holds _).bag (show 0 ≤ Cash _ _ _ from (by unfold Cash; positivity))
 | succ X ih =>
    cases υ with
    | nil=> exact (Shake.holds (SU.group.mat 1)).bag (show 0 ≤ Cash _ _ _ from (by unfold Cash; positivity))
    | cons x υ=>
       let Y:= (visits i (x::υ)).toFinset; let Z:= (visits (i+x.vec) υ).toFinset; have hc:Z⊆Y:= by rw [show Y= insert i Z from by unfold Y Z; rw [visits,List.toFinset_cons]]; exact subset_insert _ _
       have hx:i+x.vec ∈Y:=hc (List.mem_toFinset.mpr (show i+x.vec∈ visits (i+x.vec) υ from by cases υ<;> simp [visits])); have hi:i∈ Y:= List.mem_toFinset.mpr (List.mem_cons_self ..)
       have hg:pinPos (x.used i)⊆Y:=by
          unfold pinPos; rcases x with ⟨t,b⟩; cases b; · exact insert_subset hi (singleton_subset_iff.mpr hx)
          have h:i+ Lattice.Step.vec ⟨t,true⟩= i-step t:=Eq.symm (sub_eq_add_neg ..); exact insert_subset (show i-step t ∈ _ from h ▸ hx) (singleton_subset_iff.mpr (show i-step t+step t∈ _ from (sub_add_cancel i (step t)).symm ▸ hi))
       have hl:=hp (x.used i) hg; have hL: Cash (X+2) b a≤ t:=(take_k v η (by omega)).trans he; rw [Nat.add_right_comm,← put_c]; -- nat_succ notation
       apply s.duty hL ?_ (ih _ _ (Nat.succ_le_succ_iff.mp u) hL (fun j v=> hp j (v.trans hc)))
       have hu: b=Cash 0 b a:=by simp [Cash]
       change Tender (fun y=> x.read (V y) i) z (Cash (X+2) b a) k; unfold Step.read; split; · exact (g.duty (hu.le.trans ((take_k v η (by omega)).trans hL)) hl hl).bag (le_trans (show a*b ≤ Cash 1 b a from (by simp [Cash,mul_comm])) (take_k v η (by omega)))
       exact hl.bag (hu.le.trans (take_k v η (by omega)))
lemma touched_h(i:Cell V') (t:i ∈ inspectD D): touched i ⊆ inspected D:= by intro k v; apply mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,?_⟩); rw [if_neg ((mem_filter.mp t).2)]; exact v
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)}
local notation "c₁"=> Domain N B
local notation "c₂"=> Domain P B
variable (L:E→L[ℝ] Directions SU.group (Domain N B))
variable (M:Monk SU.group S){q:Chi}{l n:ℕ}{x d β:ℝ}{H:Stilo.Harper (Site (Domain N B))}{T:Tube SU.group S}
local notation "bay"=> Stilo.bay
local notation "Nc"=> ({M with key:=cusp M.key x M.V}:Monk SU.group S)
lemma gorge_l (R:Rust (mid P B))(p:(pore S ((l+90)*radiusB x) R).val⊆bay H)(f:Stilo.bay H∩ flags (temp x) M.V=M.key.flags)(ht:Ready T x)(hb:1000≤radiusB x)(hL:‖L‖ ≤ K)(hy:1 ≤ K)(t:∀ i:Bond (Domain N B),Tender (fun v=>Vmove x M.V v i) 0 a n)(u:∀ i:Bond (Domain P B),Tender (fun v=>((Nc).atop v x).sent x T q d l β i) 0 a n): ∀ i:Bond c₂, pinPos i⊆ inspected (rustL (mid P B) R).val.2 → Tender (fun v:E=>(M.atop (L v) x).sent x T q d l β i) 0 (a*K^n) n:=by
 let Y: HomeL c₁ c₂:= (M.V,M.U,β,M.z); have he: Beat (monkD M Y) Nc (Stilo.bay H):= (cusp_d M.key (M:=M) rfl f M.V).toBeat; have hp : halo ((l+70)*radiusB x) (Eire.port S R) ⊆Stilo.bay H:=(chilling (Nat.mul_le_mul_right _ (by omega :(l+70)≤l+90)) (Subset.refl _)).trans p
 have hf:= Rill.TasteZ.pact L he hp ht hb hL hy (K:=a) t u; intro j v; exact hf.1 j (mem_image_of_mem _ (v (mem_insert_self ..))) -- Orientation pinPos
lemma tendB {n:ℕ}{d:ℝ}(U:E→SU.E)(h:Tender U z b n)(p:b≤d): Tender U z d n:= h.bag p
end YM.CF.Yaw
