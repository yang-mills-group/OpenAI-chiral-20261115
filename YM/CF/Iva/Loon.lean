import YM.CF.Lor.Togs
import YM.CF.Iva.Spin
import YM.CF.Lor.Kern
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
variable {N P B:Side}{G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{x β R e a b:ℝ} {n m l k:ℕ}
local notation "G₅"=> SU.group
variable{T:Tube G₅ S}(Z:Muster G S x e T)(M:Monk G₅ S){w t u C D:ℝ}
local notation "l_"=> Z.post
local notation "q_"=> Z.trot
local notation "Ba"=> radiusB x
local notation "Wa"=> (fun y=>M.atop y x)
open Lor
attribute [local instance] opCStarAlgebra
local notation "M'"=> (violet M)
abbrev zenX(i:Site (Domain N B)):= zenA T x q_ Z.room (Z.ang+Z.fee) l_ M Z.beta Z.vita Z.rota i
abbrev fotoP(i:Site (Domain N B)):= issued x Z.loft Z.etap (ηδ Z) Z.etaD M.key (M.park,M.k) i M.V
abbrev motoP(i:Site (Domain N B)):= issued x Z.loft Z.xip (ξδ Z) Z.xiD M.key (M.park,M.k) i M.V
-- Scalar part split factoring artU before parity. Q bracket, render long.Intent
variable (K: Monk G₅ S→Rent0 G e)
variable{i:Site (Domain N B)}{a b B₁ C D U V Y c τ:ℝ}
abbrev xurn(i:Site (Domain N B)):ℝ:= Corne.artU T x q_ Z.room l_ M i
abbrev FPT (Z:Muster G S x e T)(P: Rent0 G e)(i:Site (Domain N B)):= fJ G Z.LawQ x P i
abbrev poll(i:Site (Domain N B))(V W:Rent0 G e):= burnS Z M V W i-(xurn Z M i:ℂ)
abbrev orbitM (F:Monk SU.group S→ℂ):=F (M.atop 0 x)
abbrev PoleH (a b c d f g:ℝ): ℝ:= (a+b+c+d)+(f+g) -- TODO
lemma perk {i:Site (Domain N B)}(h:i∉ M.key.dome (Z.loft*Ba))(V W:Rent0 G e) : poll Z M i V W= (↑(footS Z M i+wish Z M i+ cluck Z M i+zenX Z M i):ℂ)+((FPT Z W i-FPT Z V i)-fotoP Z M i-motoP Z M i):=by
 unfold poll burnS Muster.per; rw [show blunt Z M i=_ from if_neg h]; push_cast; unfold Muster.lore; unfold prum; rw [if_neg h]; unfold xurn; unfold zenX FPT cluck motoP fotoP; push_cast; ring -- tune
section motions
local notation "N'"=> Monk G₅ S
local notation "H"=> Directions SU.group (Domain N B)
abbrev ZUM (p q a b c d e:ℝ):ℝ:= p+q+a+b+(c+d+e)
lemma upK (z:i∉M.key.dome (Z.loft*Ba)) (u:Allows k (fun y=> footS Z (Wa y) i) 0 a)(v:Allows k (fun y=> wish Z (Wa y) i) 0 b)(p:Allows k (fun y=> cluck Z (Wa y) i) 0 B₁)(h:Allows k (fun y=> zenX Z (Wa y) i) 0 C)(ht:Allows k (fun y=> fotoP Z (Wa y) i) 0 D)(hg:Allows k (fun y=>motoP Z (Wa y) i) 0 c)(hu:Allows k (starsW (x:=x) M (fun y=> FPT Z (K y) i)) 0 τ): Allows k (fun y=> let W:=Wa y; poll Z W i (K W) (K (Cay.rough W 0))) 0 (ZUM a b B₁ C τ D c):=by -- signs
 have he:= (((u.add v).add p).add h).linear Complex.ofRealCLM (show ‖Complex.ofRealCLM‖≤1 by simp); rw [one_mul] at he; have hp:=hu.smul (-1:ℝ); rw [abs_neg,abs_one,one_mul] at hp; refine (he.add (Newt.subtract_p (Newt.subtract_p hp ht) hg)).germ ?_; filter_upwards with i'; dsimp only; rw [perk Z (M.atop i' x) z]
 simp [starsW]
local notation "X'"=> (fun y=>(M').atop y x)
lemma cap_r {o:Site (Domain N B)}(h:o∉M.key.dome (Z.loft*Ba))(R N V U t B C:ℝ)(p:Allows k (fun y=>footS Z (Wa y) o) 0 R)(ht:Allows k (fun y=> wish Z (Wa y) o + wish Z (X' y) o) 0 N)(hx:Allows k (fun y=> cluck Z (Wa y) o) 0 V)(hv:Allows k (fun y=>cluck Z (X' y) o) 0 V) (b:Allows k (fun y=> zenX Z (Wa y) o+zenX Z (X' y) o) 0 U)(v:Allows k (fun y=>fotoP Z (Wa y) o) 0 B)(w:Allows k (fun y=>motoP Z (Wa y) o) 0 t)(u:Allows k ((starsW (x:=x) M (fun y=>FPT Z (K y) o))+(starsW (x:=x) M' (fun y=>FPT Z (K y) o))) 0 C): Allows k (fun y=> let W:=Wa y; let U:= X' y; poll Z W o (K W) (K (Cay.rough W 0))+poll Z U o (K U) (K (Cay.rough U 0))) 0 (ZUM (R+R) N (V+V) U C (B+B) (t+t)):=by -- tune
 have he:=((((p.add p).add ht).add (hx.add hv)).add b).linear Complex.ofRealCLM (show ‖Complex.ofRealCLM‖≤1 by simp); rw [one_mul] at he; have h_:=(u.smul (-1:ℝ)); rw [abs_neg,abs_one,one_mul] at h_; refine (he.add (Newt.subtract_p (Newt.subtract_p h_ (v.add v)) (w.add w))).germ ?_; filter_upwards with i; dsimp only; rw [perk Z (M.atop i x) h, perk Z ((M').atop i x) h]; -- tune opn
 simp only [neg_smul,one_smul,Pi.add_apply,Complex.ofRealCLM_apply,starsW,Complex.ofReal_add]; rw [show footS Z (X' i) o=footS Z (Wa i) o from rfl, show fotoP Z (X' i) o=fotoP Z (Wa i) o from rfl, show motoP Z (X' i) o=motoP Z (Wa i) o from rfl]; abel -- tune
end motions
end YM.CF.Iva
