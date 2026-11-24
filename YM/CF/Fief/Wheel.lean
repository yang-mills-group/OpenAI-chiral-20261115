import YM.CF.Fief.Chore
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inherited
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{k n j d:ℕ}
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable{G S x e T}
variable(A:Muster G S x e T)
open Vol YM.Push.AbsoluteSums
open ConnectedActivityE6.Raw
variable (U: Monk SU.group S)
variable{s:ℝ}{l v:ℕ}
local notation "Q"=> Domain N B
local notation "Qp"=> Domain P B
local notation "λw"=> atOne (Domain N B)
section cost
variable (s:Signed)(k :ℕ)
def pageF {n:ℕ}(H:PathData SU.group)(A:Muster G S x e T) (Z:ℕ→ RG.Atom SU.group n)(X:Bit (Site (Domain N B)))(i:Site (Domain P B))(v C:ℝ):= crownQ S.ratio s k Z i v (C*A.phaseUp.threshold^n) X
def pageC {n:ℕ}(A:Muster G S x e T) (Z:ℕ→ RG.Atom SU.group n)(X:Bit (Site (Domain N B)))(i:Site (Domain N B))(v C:ℝ):= crownQ λw s k Z i v (C*A.phaseLow.threshold^n) X
local notation "M"=> Stores.till x
local notation "m"=> Stores.till x/S.patch.L.val
variable {a b C c u w σ σ' h h' Q':ℝ}
def ringC(D₁ D₂ C v:ℝ)(L:Bit (Site (Domain N B)))(i:Site (Domain N B)):= D₁*(crownQ λw s k (rod T.down m) i v C L + (pageC s k A (haste m T.down.cubic) L i v C+ pageC s k A (haste m T.down.quartic) L i v C))+pageC s k A (haste m T.down.loop) L i v C+D₂*(pageC s k A (batch T.down.cubic m) L i v C+pageC s k A (batch T.down.quartic m) L i v C)
def ringF(D₁ C v:ℝ)(L:Bit (Site (Domain N B)))(i:Site (Domain P B)):= D₁*(crownQ S.ratio s k (rod T.up M) i v C L+(pageF s k T.up A (haste M T.up.cubic) L i v C+pageF s k T.up A (haste M T.up.quartic) L i v C))+pageF s k T.up A (haste M T.up.loop) L i v C
lemma oil (s:ℝ)(hs:0 < s) : s/2=s/4+s/4:=by ring
lemma salary_b {Z:ℕ→ Atom SU.group n}(p: SumBudget (fun i=>(Z i).budget (a/2)) u)(h:0<a):Summable fun i=>(Z i).budget (a/4):=by rw [oil a h] at p; apply loan p; positivity
lemma salary_a {Z:ℕ→ Atom SU.group n}(p: SumBudget (fun i=>(Z i).budget a) u)(h:0<a): Summable fun i=>(Z i).budget (a/4):=loan (K:=u) (a:=a-a/4) (b:=a/4) (by rw [sub_add_cancel]; exact p) (by linarith)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](x':E){W:E→ Monk SU.group S}
local notation "Lp"=> fun x':E=> pull s 0 ( (W x').sent x T A.trot A.room A.post A.beta)
local notation "Lq"=>fun x':E=> pull s 0 ( (W x').V )
local notation "U₀"=> (turnStore s U.key).costs
local notation "V₀"=> traceZ (turnStore s U.key).flags
local notation "t"=> A.phaseUp.threshold
local notation "t'"=> A.phaseLow.threshold
variable (hp:∀ x',(W x').key=U.key)
include hp
lemma frost(p: CardX t (σ/4) Lp x' U₀ n A.trot C u)(i:Site (Domain P B))(h:T.up.Bounds T.high σ c b)(v:|A.beta| ≤ Q') : Pale (fun y x=>river A (W x) s k y i) (fun y=>ringF A s k Q' C (σ/4) y i) n x':=by
 have H:0 < σ/4:=by have ht:=h.width; positivity
 have hx:=A.phaseUp.threshold_pos; have hg:= A.phaseUp.threshold_le
 unfold Lich.Muster.river sapU extU; simp_rw [hp]; exact (((hut S.ratio s k (rod T.up M) Lp i C p T.high H hx hg (by omega) (salary_b (hurry h _) h.width)).merge ((sparkX S.ratio s k (haste M T.up.cubic) Lp i C p H hx hg (by omega) (salary_b (pastA _ h.width h.three _) h.width)).merge (sparkX S.ratio s k (haste M T.up.quartic) Lp i C p H hx hg (by omega) (salary_b (pastA _ h.width h.four _) h.width)))).sca _ v).merge (sparkX S.ratio s k (haste M T.up.loop) Lp i C p H hx hg (by omega) (salary_b (pastA _ h.width h.two _) h.width)) -- tune
omit hp
private lemma moats {n:ℕ}(Z:ℕ→ Atom SU.group n)(w:Site Q)(j:ℕ):spark λw s k Z (w,j)= shoreS (N:=N) (B:=B) s k w (Z j):=by
 unfold spark shoreS; dsimp only; rw [show (fun j:Site Q=> s.act ((λw).parent j))= (fun j:Site Q=>s.act j) from funext fun i=>congrArg s.act (parent_one _)] -- tune
include hp
lemma frost_c (p:CardX t' (σ/4) Lq x' V₀ n A.trot C u)(i:Site (Domain N B))(h:T.down.Bounds T.low σ c b)(v:|A.beta+(A.ang+A.fee)|≤ Q')(tX:|A.ang+A.fee|≤w)(tS:∀ l∉ V₀,Pressure.toll (Lq x') l ≤ t'): Pale (fun y x=> flows A (W x) s k y i) (fun y=> ringC A s k Q' w C (σ/4) y i) n x':=by
 have H:0<σ/4:=by have ht:=h.width; positivity
 have hx:= A.phaseLow.threshold_pos; have hg:= A.phaseLow.threshold_le
 let Lc (x:E):Config SU.group Q:= Lq x
 have ht(d:ℕ)(Z:ℕ→ Atom SU.group d)(g:d ≤ 4)(p':Summable (fun i=>(Z i).budget (σ/4))):Pale (fun y x=>extV A (W x) s k y i Z) (fun y=>pageC s k A Z y i (σ/4) C) n x':=by
    have hz:=spearX λw s k Z Lc i C p H hx hg g p' tS; unfold extV pageC crownQ; unfold crownQ at hz; simp_rw [hp,moats]; simp_rw [moats] at hz; exact hz
 have he:Pale (fun y x=>sapC A (W x) s k y i) (fun y=>crownQ λw s k (rod T.down m) i (σ/4) C y) n x':=by
    have hz:= hut λw s k (rod T.down m) Lc i C p T.low H hx hg (by omega) (salary_b (hurry h _) h.width); unfold sapC crownQ; unfold crownQ at hz; simp_rw [hp,moats]; simp_rw [moats] at hz; exact hz
 exact ((((he.merge ((ht 3 _ (by omega) (salary_b (pastA _ h.width h.three m) h.width)).merge (ht 4 _ (by omega) (salary_b (pastA _ h.width h.four m) h.width)))).sca _ v).merge (ht 2 _ (by omega) (salary_b (pastA _ h.width h.two m) h.width))).merge (((ht 3 _ (by omega) (salary_a (barn h.three m) h.width)).merge (ht 4 _ (by omega) (salary_a (barn h.four m) h.width))).sca _ tX)) -- tune ambiguity
end cost
end YM.CF.Fief
