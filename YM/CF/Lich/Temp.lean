import YM.CF.Lich.Bern
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
variable (r r' k:ℕ)(t w L:ℝ)
local notation "Z'"=> (Site (Domain N B))
local notation "nB"=> Cipher (mid N B)
local notation "S₁"=> blip S U.key r
variable{k}
abbrev Vow(S:StepData (Domain N B) (Domain P B)):= Z' ⊕ Palot.leaf Z'
abbrev Words(S:StepData (Domain N B) (Domain P B)):= Sat S ⊕ Vow S
def mapV(b:ℕ): Words S→ Palot.leaf Z':= Sum.elim (domeQ (S:=S) ((j+l+200)*radiusB x)) (Sum.elim (fun i=> ⟨halo b {i},⟨i,(halo_subset _ _) (mem_singleton_self i)⟩⟩) id)
abbrev senseC := treat T x U q θ l β A.vita t w L r j
abbrev steerC:= portF A U t w
variable (k:ℕ)
abbrev Xb : Vow S→ℂ := Sum.elim (docS A U V W r') (legS A U V k)
abbrev Fa : Vow S→ Op (Single (mid N B)):= Sum.elim (docA A U V r') (legA A V k)
section panel
-- usable for gauge-Swept additive later
variable {I I' M S:Type}[DecidableEq I][DecidableEq M][DecidableEq I'][Fintype I][Fintype S][LinearOrder S][Fintype I'][Fintype M]
variable(U:I→ℝ)(V:M→ℝ)(X:I→ℂ)(B:I'→ℂ)(Yw:I→Op S)(Z:I'→Op S)
local notation "h"=> hollow (n:=LeanV S)
abbrev rootK: I→ ribbon S:= fun i=> h (↑(U i)*Complex.exp (X i))* exp (boat (Yw i))
def sweetK: M⊕I'→ ribbon S:= Sum.elim (fun i=> h (V i)-1) (fun j'=> h (Complex.exp (B j'))*exp (boat (Z j'))-1)
lemma seedH(L:Finset I)(Xw:I→ ℂ): (∏ i∈L,h (Xw i))=h (∏ i∈L,Xw i):=by
 induction L using Finset.induction_on with
 | empty=> rw [prod_empty,prod_empty]; exact Subtype.ext (one_smul ..).symm
 | insert i Q hv ih=> rw [prod_insert hv,prod_insert hv,ih]; apply Subtype.ext; change (Xw i • (1:FC (LeanV S)))*((∏ i∈Q,Xw i) • 1)=(Xw i*(∏ i∈ Q,Xw i)) • 1; rw [Algebra.smul_mul_assoc,one_mul,← smul_smul]
lemma coast (a b: ℂ)(t u:ribbon S):h a*t*(h b*u)=h (a*b)*(t*u):=by
 rw [show h a*t*(h b*u)= (h a*h b)*(t*u) from by ring]; congr 1; apply Subtype.ext; change (a • (1:FC (LeanV S)))*(b • 1)= (a*b) • 1; rw [Algebra.smul_mul_assoc, one_mul,smul_smul]
lemma sect(l':Finset I)(P:Op S)(v s t:ℂ)(hf:(∑ i∈l',boat (Yw i))+(∑ i,boat (Z i))=boat P)(hv:s=(∑ i∈l', X i)+(∑ i,B i))(hx:t=(((∏ i,V i)*(∏ i∈l',U i):ℝ):ℂ)*Complex.exp (v+s)):let T':=(∏ i∈l',rootK U X Yw i)*∏ i:M⊕I',(1+sweetK V B Z i); t • (exp (boat P)).val=Complex.exp v • T'.val:=by
 intro T'; let e':=exp (boat P); let α0:= ∏ i:M,(V i:ℂ); let b':=(∑ i∈l',X i); let a':=∏ i∈l',(U i:ℂ); let B1:=∑ i,B i; let g':= a'*α0*Complex.exp s
 have hV:T'=h g'*e':=by
    letI : NormedAlgebra ℚ (ribbon S):= NormedAlgebra.restrictScalars ℚ ℝ (ribbon S);
    unfold T' rootK; rw [prod_mul_distrib,seedH,Fintype.prod_sum_type,prod_mul_distrib]
    have hp(x y:ribbon S): x+(y-x)=y:= by abel
    simp only [sweetK, Sum.elim_inl,Sum.elim_inr,hp]; rw [prod_mul_distrib, seedH,seedH,←Complex.exp_sum,←Complex.exp_sum, ←exp_sum,←exp_sum]; let H:= ∑ i∈l',boat (Yw i); let W:=∑ i,boat (Z i)
    change h (a'* Complex.exp b')*exp H*(h α0*(h (Complex.exp B1)*exp W))=_; rw [show h α0*(h (Complex.exp B1)*exp W)= h (α0*Complex.exp B1)*exp W from by simpa using (coast α0 (Complex.exp B1) 1 (exp W)),coast,←exp_add,show H+W=boat P from hf]; unfold g'; rw [hv,Complex.exp_add]; unfold b' B1; ring_nf; rfl
 rw [hx]; change _= Complex.exp v • _; rw [hV]; change _= Complex.exp v • ((g' • (1:FC (LeanV S)))* e'.val); rw [Algebra.smul_mul_assoc,one_mul,smul_smul]; congr 1; unfold g' α0 a'; rw [Complex.exp_add]; push_cast; ring
end panel
end Muster
end YM.CF.Lich
