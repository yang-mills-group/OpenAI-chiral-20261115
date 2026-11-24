import YM.CF.Scion.Owl
import YM.CF.Cloak.Coil
import YM.CF.Reine.Proof
set_option quotPrecheck false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]

set_option maxHeartbeats 500000
open Pec Proa Hest Hive Spire Skye Levier Cascade Kennel
open Girt Forge Appel Reine Cloak Cour Rill RG Wilson Lattice Laurent Precision Tree Next.SectorChange Pressure AnalyticBridge.Annulus1AD Ac
open Push.SectorMeasure.Oriented
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedSpace ℂ E][IsScalarTower ℝ ℂ E]
lemma join_r (X:E)(a b p t h d:ℝ)(v K g:ℂ)(s:a*b*Real.exp (-(d-h))=p*t): a • b • Complex.exp (v-(d:ℂ)-K-g) • X=p • Complex.exp (v-(h:ℂ)-g) • t • Complex.exp (-K) • X:=by
 simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; simp_rw [smul_smul]; congr 1
 rw [show v-(d:ℂ)-K-g=-K+(v-(h:ℂ)-g)+ ((↑(-(d-h))):ℂ) by simp only [Complex.ofReal_neg,Complex.ofReal_sub]; abel,Complex.exp_add, ←Complex.ofReal_exp,Complex.exp_add]; calc
    _= (((a*b*Real.exp (-(d-h)):ℝ):ℂ))*(Complex.exp (-K)*Complex.exp (v-↑h-g)) := by simp only [Complex.ofReal_mul]; ring_nf <;> simp [mul_left_comm, mul_comm, mul_assoc]
    _=_:=by rw [s]; simp only [Complex.ofReal_mul]; ring_nf <;> ac_rfl
end
open Acorn Atala Reef Char
variable {L N Q B:Side} {j:ℕ}{o:Odd L.val}{e v b d:ℝ}{Y:Pricing j L o (Thread j)}(P:Grasp Y B e)
variable (G:Ratio (mid N B) (mid Q B))(ℍ:GramM (mid Q B))(X:GramM (mid N B))(A₀:Scree.Loom (mid N B))(A:Scree.Loom (mid Q B))(q k:Chi)(w:ℝ)
variable (T:StepData (Domain N B) (Domain Q B))(F: Tube SU.group T)(ht:T.ratio=ratio G)(M:Monk SU.group T)(x s a b η:ℝ)(r l k':ℕ)(U:Ids (mid Q B))(V:Ids (mid N B))(J:ChartRatio SU.group)
-- exact sector normalization at ALL flags
-- I' on Q.V fixed. use out Loom. budget order d due.
local notation "K"=> ℍ.J.P
local notation "m"=> ℍ.J.M
local notation "Z"=> (M.sent x F k η l ℍ.beta,U)
local notation "WQ"=> (M.V,V)
abbrev caveF :=YF G A₀ A q w (ht ▸ M.park) (M.V,V) (M.sent x F k η l ℍ.beta,U)
local notation "Ω"=> caveF G ℍ A₀ A q k w T F ht M x η l U V -- tune order
-- avoid `variable hd: Chill...macro.`
-- wages integration enter; hAlive always, α fact
open Arena
attribute [local instance] opCStarAlgebra
lemma post_FO (γ:ℝ)(i:Rent0 G e)(hi:i.val= Ω) (C T₁ t:ℝ)(α₀: FC (Single (mid Q B)))(Y':Weave (Single (mid Q B)) (Single (mid N B)))
 (wr:IsStarProjection (spar j (upMale L o m) i.val.2)) -- tune
 (u: riteL (j:=j) m G i (denZ ℍ P A Z)=Complex.exp (ℍ.H0 (Z).1-Cour.shipA G P m (K).den ℍ.J.I X.J.I i.val-pigment X.J.I i.val.2) • acts ((nursery _ wr).eval (issue Y' (ℍ.board Z).val α₀*(exp (Hest.boat (Budget L o (K).den X.J.P.den G m j i.val))).val)) (nest P X.J.P (upMale L o m) i.val.2)) -- macro needs .val
 (hp: C * plight F x ℍ.beta k J η l γ M * Real.exp (-(tenderU F x M k η l ℍ.beta ℍ.p X.p b))=T₁ * t)
 (hM:ℍ.path=F.up)(hm:ℍ.funds=F.high)(hv:X.path=F.down)(hk:X.funds=F.low)(hβ:X.beta= ℍ.beta+b): let K':= -Cour.shipA G P m ℍ.J.P.den ℍ.J.I X.J.I i.val
 let T':= issue Y' (ℍ.board Z).val α₀*(exp (Hest.boat (Budget L o ℍ.J.P.den X.J.P.den G m j i.val))).val
 C • (plight F x ℍ.beta k J η l γ M • (waveV P G ℍ A₀ A q w (ht ▸ M.park) (M.V,V) Z))= T₁ • Complex.exp (X.betaL A₀ WQ-X.v+ℍ.v) • t • Complex.exp K' • acts ((nursery _ wr).eval T') (nest P X.J.P (upMale L o m) i.val.2):=by
 intro K' Z'; rw [show waveV P G ℍ A₀ A q w (ht ▸ M.park) (M.V,V) Z= riteL (j:=j) m G i (denZ ℍ P A Z) by unfold waveV; unfold riteL; dsimp only [LinearMap.coe_mk, AddHom.coe_mk]; rw [hi] ,u]; unfold GramM.betaL GramM.H0; rw [hM,hm,hv,hk,hβ,← show i.val.2=A₀ WQ from congrArg Prod.snd hi];
 let z:= F.down.inChannels F.low X.p (ℍ.beta+b) M.V; rw [show X.v- (↑z:ℂ)-pigment X.J.I i.val.2-X.v+ℍ.v= ℍ.v- ↑z-pigment X.J.I i.val.2 by abel]; exact join_r _ C (plight F x ℍ.beta k J η l γ M) T₁ _ z _ _ _ _ hp
end YM.CF.Scion
