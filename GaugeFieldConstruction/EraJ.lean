import GaugeFieldConstruction.SonetJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.OromoJ
import GaugeFieldConstruction.FrijaJ
import GaugeFieldConstruction.Gloss
import GaugeFieldConstruction.QuishJ
import GaugeFieldConstruction.NorasJ
import GaugeFieldConstruction.TributoJ
import GaugeFieldConstruction.AmusaJ
import GaugeFieldConstruction.SpursJ5
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Legends
import GaugeFieldConstruction.Frosts
import GaugeFieldConstruction.Swirls
import GaugeFieldConstruction.Infar
import GaugeFieldConstruction.Moll
import GaugeFieldConstruction.Panther
import GaugeFieldConstruction.Kenko
import GaugeFieldConstruction.HopeQ
import GaugeFieldConstruction.Overland
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 290000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Lich Iva
open Engine Engine.Basin Engine.Docket Dialect
open Vow Bake Salt Stax Sour Larch
namespace Focus
open Appel.Rate Stockpile
section
open Sour.MatchW Sour.MatchW.Technique Cycle929 Tap Lilt
open Next.Fluctuations.Sector
open Neon
open QuadClock Haro
open Mew Vow Rive Bake
open scoped YM.CF.Mew
open Riant
open YM.CF.Oath.BellPrice PinRack
open TableF TableF.Boom Lenten Layout Fren
section
open Mew Roots Connect Ing Ing.Iona CoeffArc Frugal
variable {I O A Y:Type}[Fintype I][LinearOrder I][Fintype O][LinearOrder O][DecidableEq A][Fintype A][DecidableEq Y][Fintype Y]
variable {L: Side}{K:Teller SU.group}{R:Patch}{N m n B:Side}{d v x:ℝ}
variable {c:ChartRatio SU.group}
open Directory
namespace Onwards
variable (σ:I→Site N)(C:I→I→ℂ)
section
variable {K:Type}[AddCommMonoid K][Module ℂ K](U:Finset I→K)(B A:Finset I)
-- Book transform. Exact charge NO coefficient-degree room consumption beyond row norm.
lemma vappy {A E:Type}[AddCommMonoid E][Module ℂ E](F: Finset I→ A→ E)(B:Finset I)(i:A): Verdante σ C F B i=Verdante σ C (fun b=> F b i) B:=by unfold Verdante; simp_rw [Finset.sum_apply]; apply sum_congr rfl; intro a _; refine sum_congr rfl fun j p=>?_ ; split_ifs <;> rfl
variable {E G Z:Type}[Fintype Z][NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
lemma vapp (F:Finset I→Z→ G→ E)(k:Z)(x:G)(i:I):Verdante σ C F {i} k x= ∑ j∈ Roots.pipe_ζ σ i, C j i • F {j} k x:=by simp only [vappy,aloneX]
variable (F:Finset I→Z→G→E)(K': Cornea Z G E N)
-- Generic frame substitution.Proofs use only. w.Signal optionally C-full; Σ.Cost
lemma Curta (w:Ledges K' σ F): Ledges K' σ (Verdante σ C F):=by
 intro i y p A h; change Verdante σ C F A i y≠0 at h; have hf: A∈ realm_C σ:=by by_contra t; rw [Vout σ C _ A t] at h; exact h rfl -- zero
 rw [vappy] at h; change Verdante σ C (fun k=> F k i) A y ≠0 at h; rw [vappy] at h; unfold Verdante at h; dsimp only at h; obtain ⟨a,p',t⟩:= exists_ne_zero_of_sum_ne_zero h; obtain ⟨b,k,v⟩:= exists_ne_zero_of_sum_ne_zero t
 split at v; swap; · exact False.elim (v rfl)
 rename_i q; refine ⟨hf,fun j s=>?_⟩
 have hy:σ j ∈ a.image σ:=D_σ _ _ _ _ (q.symm ▸ s);
 obtain ⟨i,b,r⟩:= mem_image.mp hy; rw [← r]; exact (w _ _ p a (fun e=>v (by dsimp only at e; rw [e,smul_zero]))).2 i b
lemma FareJ {r S T s:ℝ}{b:ℕ}(h:BookT K' F b (realm_C σ) s r T)(ps:0≤S)(p:∀ j:I,S *∑ i:pipe_ζ σ j, ‖C j i.val‖ ≤ r): BookT K' (Verdante σ C F) b (realm_C σ) s S T:=by
 obtain ⟨F0,f,P⟩:= h; let B(i:Finset I)(k:Z):=∑ a∈ realm_C σ, ∑ x:Duty σ a, if FerryZ σ a x=i then ‖Dl σ C a x‖* F0 a k else 0
 have hu{k:Z}{A:Type}(D:Finset A)(g:A→G→ E)(F:A→ℝ)(v:∀ i∈D,K'.Lux k (g i) (F i)): K'.Lux k (∑ i∈D,g i) (∑ i∈D,F i):=by
    induction D using Finset.induction_on with
    | empty=> rw [sum_empty,sum_empty]; exact K'.zero k 0 (fun _ _=>rfl)
    | insert i D h ih=>rw [sum_insert h,sum_insert h]; exact K'.add _ _ _ _ _ (v _ (mem_insert_self i _)) (ih fun j p=>v j (mem_insert_of_mem p))
 refine ⟨B,fun i t k=>?_,fun x=>?_⟩
 · rw [vappy]; unfold Verdante B; apply hu (realm_C σ); intro a h; apply hu (univ:Finset (Duty σ a)); intro D p; split_ifs
   · exact K'.coin _ _ _ (f _ h _) _
   exact K'.zero k _ (fun _ _=>rfl)
 refine le_trans ?_ (P x); unfold B; let R0:= (realm_C σ)
 let Z0:= univ.filter fun y=>x∈K'.Φ y
 let g(i:Finset I)(a:Finset I)(y:Z):ℝ:= S^i.card* dra_k b s (K'.Φ y)
 let B(a:Finset I):=∑ y∈Z0,dra_k b s (K'.Φ y)*F0 a y
 let H(i a:Finset I):ℝ:=∑ x:Duty σ a, if FerryZ σ a x=i then S^a.card*‖Dl σ C a x‖*B a else 0
 -- first convert separately each.
 apply le_trans (b:= ∑ i∈ R0,∑ a∈R0,H i a)
 · apply le_of_eq; apply sum_congr rfl; intro i p; simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro a ha; unfold H; rw [sum_comm]; apply sum_congr rfl; intro y _; split_ifs with q; swap
   · simp [q] -- if local eq
   rw [← q, Dsize σ a y ha] -- maybe proof irrel
   unfold B; rw[mul_sum]; apply sum_congr rfl; intro k _; ring
 rw [sum_comm]; apply sum_le_sum; intro a ha; have hx:0≤ B a:= sum_nonneg (fun y m=>mul_nonneg (Real.exp_pos _).le (K'.posG _ _ _ (f _ ha _)))
 unfold H; rw[sum_comm]; apply le_trans (b:=∑ x:Duty σ a,S^a.card* ‖Dl σ C a x‖* B a) ((sum_le_sum fun i _=> le_of_eq (by
    rw [sum_eq_single_of_mem (FerryZ σ a i) (Dr_C _ _ i ha),if_pos rfl]; exact fun j _ h=> if_neg h.symm)) )
 rw [←sum_mul,←mul_sum]; refine mul_le_mul_of_nonneg_right ?_ hx; unfold Dl; simp_rw [norm_prod]; rw [←Fintype.prod_sum (fun i:a=> fun j:pipe_ζ σ i.val=> ‖C i.val j.val‖),← show (∏ _i:a,S)=S^a.card from (by simp), ←prod_mul_distrib]; refine le_trans (Finset.prod_le_prod (g:=fun i=>r) ?_ ?_) (le_of_eq (by simp));
 · intro i _; exact mul_nonneg ps (sum_nonneg (fun j _=>norm_nonneg _))
 intro i _; exact p i
#print axioms FareJ
end
end Onwards
end
end
end Focus
end Pitching
end YM.CF.Py.Rate
end
