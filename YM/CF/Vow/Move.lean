import YM.CF.Vow.Peso
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
def chi_f(k:ℕ):= (k+1:ℝ)*composeCost k 1 1
abbrev oV (F:InkD n): Copy n:=fun u=>F u.1
variable {F: Copy n}{G G':InkD n}{U':Scree.Hub n}{D':Force n}
lemma spicy_f(k:ℕ):0≤chi_f k:=by unfold chi_f composeCost; positivity
lemma rate_x (c: Ink n)(p:0 ≤ c)(hb:0≤h)(k:ℕ)(o:Seat n)(C:ℝ)(u:(∑ i:Finset (Dwell n), Scree.tariff P o h i*c i) ≤ C):joinV (stake h) (fun i:Finset (Dwell n)=> (k+1:ℝ)* composeCost k (c i) 1) ≤ chi_f k*C:=by
 refine le_trans ?_ (mul_le_mul_of_nonneg_left u (spicy_f k)); unfold joinV; rw [mul_sum]; apply sum_le_sum; intro i _
 have ht:(k+1:ℝ)*composeCost k (c i) 1=chi_f k * c i:=by unfold chi_f composeCost; ring
 dsimp only; rw [ht,mul_left_comm]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (p i)) (spicy_f _); apply le_mul_of_one_le_left (pow_nonneg hb _); exact one_le_pow₀ (le_add_of_nonneg_right (by positivity))
lemma rimP (p: ForceB P D' F h c)(v:0≤h) : Firm P D'.val.1.val.2 D'.val.2 F ∧ Medal P D'.val.1.val.2 D'.val.2 F h (chi_f P.order*c):=by
 obtain ⟨x,f,a,q,y,u,C,t,g,w⟩:=p; let S(i):=composeCost P.order (C i) 1
 have ht(i):0≤S i:=by unfold S composeCost; exact mul_nonneg (mul_nonneg (by positivity) (t i)) (pow_nonneg (by norm_num) _)
 refine ⟨⟨a,y⟩,⟨⟨fun (V W:Orbit n)=>x V.1 W.1 V.2 W.2, f,q,fun (V:Orbit n)=>u V.1 V.2⟩,fun i=>(P.order+1:ℝ)*S i,fun i=>mul_nonneg (by positivity) (ht i), ?_, rate_x _ t v _ _ _ w⟩ ⟩
 intro V j R t; refine Rue.paidP _ _ fun i=>?_ ; exact pins t (U:=V.1) (K:=fun j=>crumb (F (j,V.2)).val i) (g V j i)
lemma rimR (p: PressB P U' G h c)(v:0 ≤ h): Medal P U'.val.2 ∅ (oV G) h (chi_f P.order*c):=by
 obtain ⟨x,f,q,u,C,t,g,w⟩:=p; let S(i):=composeCost P.order (C i) 1
 have ht(i):0≤S i:=by unfold S composeCost; exact mul_nonneg (mul_nonneg (by positivity) (t i)) (pow_nonneg (by norm_num) _)
 refine ⟨⟨fun U V p _=>x _ _ p,fun U=>f U.1,q.comp measurable_fst,fun (V:Orbit n)=>u V.1⟩,fun i=>(P.order+1:ℝ)*S i,fun i=>mul_nonneg (by positivity) (ht i),?_,rate_x _ t v _ _ _ w⟩
 intro V j R t; refine Rue.paidP _ _ fun i=>?_ ; rw [sdiff_empty] at j; exact debt_m (U:=V.1) (K:=fun j=>crumb (G j).val i) (g V.1 j i)
-- restore charges
open Nor
variable (A: Ink n)
lemma Medal.tokenT (w:Medal P X D F h c)(s:∀ V:Orbit n,pingS P.threshold (X\D) V.1 → WorthB P V D F A)(o:Seat n)(t:o∈X)(i:Finset (Dwell n))(V:Orbit n)(x:pingS P.threshold (X\D) V.1): Signs P o (fun j=> crumb (F (increment V.1 (openG P D j),V.2)).val i) (Nor.linkY P X A k i):=by
 let f(U:Pane n):= crumb (F (U,V.2)).val i
 unfold linkY; split
 · apply tomB t _ (K:=f) (fun U T u=> by unfold f; rw [w.same (U,V.2) (T,V.2) u (fun _ _=>rfl)]); exact (s V x).haveP i
 rename_i g; exact Prism.mint (Prism.hail (v:=(0:ℝ)) (show ‖(0:ℂ)‖≤0 by rw [norm_zero])) (Eventually.of_forall fun j=> ((w.lit _).door g).symm) -- tune
abbrev fareX(k:ℕ)(P:BudgetPoint)(X:Support (More n)):=Nor.surgeL P X k*Nor.liftR P X k 1
lemma health_f(k:ℕ)(P:BudgetPoint)(X:Support (More n)):0 ≤ fareX k P X:=by unfold fareX Nor.surgeL Nor.liftR Jet.composeCost Nor.surgeL; positivity
lemma quietT (t:0≤A):0 ≤ Nor.linkY P X A k:=by
 intro i; unfold linkY; split
 · unfold liftR composeCost; refine mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) (t i))) (pow_nonneg ?_ _); unfold surgeL; positivity
 exact le_rfl
lemma Medal.preserves (w:Medal P D'.val.1.val.2 D'.val.2 F h c)(p:Firm P D'.val.1.val.2 D'.val.2 F)(v:0 ≤ h)(k:ℕ): ForceB P D' F h (fareX k P D'.val.1.val.2*c) :=by
 obtain ⟨A',t,u,g⟩:= w.pays; let N:=D'.val.1.val.2
 exact ⟨fun U V i j=>w.same (U,i) (V,j), w.lit,p.readV,w.keeps,p.litK,fun V t=>w.gaugeX (V,t), linkY P N A' k,quietT _ t,fun i h j=> w.tokenT A' (fun V v=>u V v (Subset.refl _)) _ D'.val.1.property j i h, (Nor.rate_i P N _ D'.val.1.property A' k h t v).trans (mul_le_mul_of_nonneg_left g (health_f ..))⟩ -- notation t shadow
lemma Medal.preservesE (τ:Ids n)(w:Medal P U'.val.2 ∅ (oV G) h c)(t:0≤h)(k:ℕ): PressB P U' G h (fareX k P U'.val.2*c):=by
 obtain ⟨A',v,x,g⟩:= w.pays; let N:= U'.val.2
 refine ⟨fun V W p=>w.same (V,τ) (W,τ) p (fun _ _=>rfl),fun V=>w.lit (V,τ), w.keeps.comp (measurable_id.prodMk (measurable_const (a:=τ))),fun V=>w.gaugeX (V,τ), linkY P N A' k, quietT _ v,fun V u i=>?_, (Nor.rate_i P N _ U'.property A' k h v t).trans (mul_le_mul_of_nonneg_left g (health_f ..)) ⟩
 have hV:= w.tokenT (k:=k) A' (fun V v=>x V v (Subset.refl _)) _ U'.property i (V,τ) (by rw [sdiff_empty]; exact u); have he(i:tangD n):openG P (∅:Support (More n)) i=i:=by funext j; simp [openG,Lattice.halo]
 simp_rw [he] at hV; exact hV
end YM.CF.Vow
