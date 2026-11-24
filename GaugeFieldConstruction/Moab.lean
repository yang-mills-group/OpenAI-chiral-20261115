import GaugeFieldConstruction.Paris
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
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
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open TableF Lenten Lenten.Layout Fren
open Frugal
open Py.Riant
-- arbitrary finite labels grouped by Seat. further partition within group by programs.D.
variable {N:Side}{I S:Type}[LinearOrder I][Fintype I][Fintype S][DecidableEq S]
namespace Directory
variable (D: Directory I S)
variable {P B:Side} {X:GramM (mid N B)} {Y:GramM (mid P B)}
variable (L:Side)(o:S→Seat (mid P B))(y:S→Seat (mid N B))(T: S→Scree.Hub (mid N B))(hT:∀ i,(T i).val.1=y i)
variable (VΨ:I→ RegBudget (mid P B))(F:I→Vow.Pax (mid N B)) (W:I→ Zone (mid N B))
variable {h t s a μ τ b q d:ℝ} {A: S→Aura (mid N B)}
abbrev Ctree (T:S→Scree.Hub (mid N B))(X:GramM (mid N B))(F:I→Vow.Pax (mid N B))(D:Directory I S)(h:ℝ)(L:Side)(i:I): Oath.Zone (mid N B):= Brow (T (D.own i)) X.J.M h X.p (F i) L (D.depth (D.own i))
variable (hp:Chords t s a q μ h τ X.p Y.p L)(H:∀ i:I,FuelKey X Y (T (D.own i)) (o (D.own i)) h a b q μ (RamoK L*s) (A (D.own i)) (VΨ i) (F i) L)
variable (pk:∀ i:S,PocketL L μ τ (D.depth i))(hv: ∀ i:S,D.depth i≤2)(hq:∀ i:S,Cresc L.val Y.p (Zhub (o i)))
variable (F_in:D.TourF)(G_in:D.TourG)(hf:D.InShape F_in G_in τ)(hy:D.QSign Y.p Y.J.M o VΨ L h (RamoK L) s F_in)
variable (ht:W=Ctree T X F D h L)
include hT hp H pk hv hq hf hy ht
lemma D_earn : ∀ v:S, Freight (P:=X.p) (y v) X.J.M t μ τ h b (D.depth v) (fun i:D.Pname v=>W i.val) (G_in v) L ∧∀ j:D.Vname v,Basalt X.p (y v) L.val (L.val+1) (W j.val) (Gapμ L μ*(Rateκ L (D.depth v+1)*t)) 2 b h (D.depth v) X.J.M:=by
 intro v; let U(v):= o v; let F'(i:D.Pname v):= F i.val; let X'(i:D.Pname v):= VΨ i.val
 have hu (i:D.Pname v): FuelKey X Y (T v) (o v) h a b q μ (RamoK L*s) (A v) (X' i) (F' i) L:=by have he:=H i.val; rw [i.property.1] at he; exact he
 have hY(i:D.Vname v): FuelKey X Y (T v) (o v) h a b q μ (RamoK L*s) (A v) (VΨ i.val) (F i.val) L:=by have he:=H i.val; rw [i.property.1] at he; exact he
 have hx:= barter_R hp (hf v) hu (hv v) (hy v).1 (hq v) (pk v).lobe -- tune
 have hw(i)(x:D.own i=v):W i=Brow (T v) X.J.M h X.p (F i) L (D.depth v):=by rw [ht]; unfold Ctree; rw [x]
 rw [←hT]; refine ⟨?_,fun j=>?_⟩
 · rw [show (fun i:D.Pname v=>W i.val)=TipsK (T v) X L h F' (D.depth v) from funext (fun i=>hw i.val i.property.1)]; exact hx
 rw [hw j.val j.property.1]; exact GroundK hp (hY j) (hv v) ((hy v).2 j)
variable (J:D.ToMG)(K: D.ToPC)(F_out:D.TourF)(G_out:D.TourG)(hG:D.InShape F_out G_out τ)
abbrev Substance (o:S→Seat N)(X:GramM N)(t h:ℝ)(W:I→Oath.Zone N)(F: D.TourF)(V:D.TourG)(J:D.ToMG)(K:D.ToPC)(L:Side) :Prop:=∀ x:S,InkFr (fun i:D.Pname x=>W i.val) (fun i:D.Vname x=>W i.val) X.p (o x) X.J.M (D.depth x) (F x) t h (J x) (K x) L (V x)
include hG
lemma D_occurs :∃ J K,D.Substance y X t h W F_out G_in J K L:=by
 have hz:= D_earn D L o y T hT VΨ F W hp H pk hv hq F_in G_in hf hy ht; have htau:= show 0 ≤ τ from le_trans (by norm_num:0≤(8:ℝ)) hp.calm
 choose J K t using fun x:S=> Prize_T (hz x).1 (hf x).ray hp.edge hp.reachF hp.full htau (pk x) (G_out x) (hG x) (hz x).2 -- tune
 exact ⟨J,K,t⟩
variable (hQ:D.Substance y X t h W F_out G_in J K L)
include hQ
structure Paid (D:Directory I S)(P:GramM (mid N B))(W:I→Zone (mid N B))(y:S→Seat (mid N B))(F_out:D.TourF)(G_in:D.TourG)(J:D.ToMG)(K:D.ToPC)(L:Side)(t b h:ℝ):Prop where
 lenses(x:S): let Y:=CoatP (K x) L (G_in x); let M:= (fun i:D.Pname x =>W i.val); Bijective Y ∧ (∀ i: FrameK (D.Pname x),μRoad (Y i) P.p M (y x) P.J.M h t (D.depth x)= Woof i (F_out x)∧ LoomK i ≤ (Rateκ L 0*κMini L) * LoomK (Y i) ∧ LoomK ((K x) i)≤ κMini L*LoomK i ∧ LoomK i≤ κMini L* LoomK ((K x) i))
 optic (x:S):let C:= D.MatchRow y W (D.Ctags J K L G_in); (∀ i:D.Pname x, let l:= PickS (K x) i L (G_in x); let q:= C i.val; LoomK l ≤ (Rateκ L (D.depth x))⁻¹*κMini L ∧ Basalt P.p (y x) L.val (L.val+1) q (RamoK L/16*t) 2 (LoomK l*b) h (D.depth x) P.J.M ∧ CardT q (KeyUp P.p) P.J.M h (y x) (D.depth x)=(t:ℂ) • F_out x i) ∧ (∀ j:D.Vname x, let A:=PrizeP (J x) (K x) j L (G_in x); let F':= C j.val; LoomK ((J x) j)≤ LαK L (DimsP (D.depth x+1)+2*Alto)∧ LoomK A ≤ LαK L (-1+3*Alto) ∧ Basalt P.p (y x) L.val (L.val+1) F' (RamoK L/16*t) 2 (GapGain L (D.depth x)*(b+LoomK A*b)) h (D.depth x) P.J.M ∧ CardT F' (KeyUp P.p) P.J.M h (y x) (D.depth x)=0)
lemma faucets : Paid (N:=N) (B:=B) D X W y F_out G_in J K L t b h:=by
 let A:= D_earn D L o y T hT VΨ F W hp H pk hv hq F_in G_in hf hy ht
 have hZ:0 ≤ τ:=by have h:=hp.calm; linarith
 constructor
 · intro x Y M; exact M_purse (A x).1 hp.edge hp.reachF hp.full hZ (pk x) (G_out x) (hG x) (K x) (hQ x).beacon -- args order
 intro x H1; refine ⟨fun i=>?_,fun j=>?_⟩
 · dsimp only; unfold H1; rw [Tip_C]; exact Payout (A x).1 (hf x).ray hp.edge hp.reachF hp.full hZ (pk x) (G_out x) (hG x) (K x) (hQ x).beacon i
 dsimp only; unfold H1; rw [Tip_gap]; exact Prize_α (A x).1 (hf x).ray hp.edge hp.reachF hp.full hZ (pk x) (G_out x) (hG x) (A x).2 (J x) (K x) (hQ x) j -- defeq Prize
omit H hp hT pk hq hf hy ht hQ hG
variable (u:Paid D X W y F_out G_in J K L t b h)
include u
lemma profiles : ColLim (D.F_v y) (D.Ctags J K L G_in) (Maxi L):=by
 intro i; by_cases p:D.kind i=true
 · let T:D.Pname (D.own i):=⟨i,rfl,p⟩; exact Column_C D y J K L G_in (D.own i) hv T (((u.optic _).1 T).1)
 let T:D.Vname (D.own i):= ⟨i,rfl,Bool.eq_false_iff.mpr p⟩; exact Column_G D y J K L G_in (D.own i) hv T (((u.optic _).2 T).2.1)
omit u hv
lemma Max_v:1 ≤ Maxi L:= by unfold Maxi; exact le_add_of_nonneg_right (sum_nonneg fun i _=>add_nonneg (abs_nonneg _) (abs_nonneg _))
end Directory
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
