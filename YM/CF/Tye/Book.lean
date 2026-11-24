import YM.CF.Tye.Wheel
import YM.CF.Iva.Loon
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
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
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
local notation "Z"=> mid N B
local notation "j'"=> A.loft
local notation "q"=> A.trot
local notation "Q"=> A.LawQ
local notation "L'"=> A.post
local notation "J"=> A.vita
local notation "R"=> A.rota
local notation "v'"=> A.room
local notation "H"=> A.hot
local notation "β"=> A.beta
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "X"=> kist M
variable (f:Sweep (mid N B))(W U': Rent0 G e)(i:Site (Domain N B))
variable (ph:S.ratio=ratio G)(t:tyke G A.LawQ)(xw:A.Beds.val=(1,1))
local notation "W'"=> male e G f W
local notation "N'"=> rot f M
local notation "A'"=> clue S f.s (Facet.pasta f) M
local notation "Λ"=> chart f
local notation "Ω"=> M.key.dome (j'*radiusB x)
include t ph
lemma pint_l : fJ G Q x W' i= payZ f (fJ G Q x W (Λ i)):=by
 unfold fJ; rw [← din_t,map_sum]; refine sum_equiv (weaveS G f) (fun i=>?_ ) ?_
 · simp only [mem_filter,mem_univ,true_and,rumR]
 intro p _; have hp : A.LawQ p W'=payZ f (Q (weaveS G f p) W):=by
    let hp:= t f (weaveS G f p) W; rw [show toRoar G f⁻¹ (weaveS G f p)=p from (weaveS G f).symm_apply_apply p] at hp; exact hp
 rw [hp,map_smul,din_t]; exact congrArg (· • (payZ f _)) (turtle_t f ph p i)
omit t ph
include xw
lemma mink_B: male e G f A.Beds=A.Beds:=by
 let C:= A.Beds; apply Subtype.ext; change stanza G _ _ A.Beds.val= _; rw [xw]; have hp{N:Side}(a:Shape)(b:Bool): stir (N:=N) (xtra b) a (1:Config SU.group _)=1:=by funext i; unfold stir; simp only [Function.comp_apply,Lattice.pull,Step.read,Pi.one_apply]; simp
 unfold Scroll.stanza; simp only [hp] -- tune namespace
variable{U₁ U₂ U₃ U₄ U₅ U₆:ℝ}{n:ℕ}{D₁:nomA N P B→ℂ}
omit xw
include h hp ht hm hi hz hv
lemma aheadQ (ρ:Bright T x A.hash q v' (α+γ) L' M β J R j')(θ:Bright T x A.hash q v' (α+γ) L' Y β J R j')(u:i ∉ (Y).key.dome (j'*radiusB x)) (g: FreeResolvent.Gap (baseX T x (kist M).key M.park M.k 1) m): Coin T x A.hash q J R v' (α+γ) L' ((Y).park,(Y).k) i (Y).V= Coin T x A.hash q J R v' (α+γ) L' (M.park,M.k) (affine s b i) M.V:=by
 let z:=affine s b i; have htP:= funds_branch h; rw [θ.sung _ u,ρ.sung _ (mt (dome_map ..).2 u), kist_s,rough_s,ink_s T (rough M 0) x q v' _ β h hp hv hz, ink_s T (kist M) x q v' _ β h g hv hz,kite_s T (rough M 0) x q v' _ β h hp hv hz _ R ht hi hm,kite_s T (kist M) x q v' _ β h g hv hz _ R ht hi hm,qerr_s T M x q v' _ h hp hv hz s b g] -- tune qerr args
include hA hB
lemma behindB (ρ:Bright T x A.hash q v' (α+γ) L' M β J R j')(θ:Bright T x A.hash q v' (α+γ) L' (cedar M) β J R j')(u:i ∉Ω):Coin T x A.hash q J R v' (α+γ) L' (M.park,M.k) i (cedar M).V= Coin T x A.hash q J R v' (α+γ) L' (M.park,M.k) i M.V:=by
 change Coin T x A.hash q _ _ _ _ _ ((F).park,(F).k) i (F).V=_; rw [θ.sung _ u,ρ.sung _ u,rough_f,ink_f T (rough M 0) x q v' L' β h hA hB hp hv hz,kite_f T (rough M 0) x q v' L' β h hA hp hv hz J R ht hi hm,qerr_f T M x q v' L' h hA hp hv hz i]; rfl
variable {m':ℝ}
-- $
local notation "K₀"=>Tarn.Coin T x A.hash q J R v' (α+γ) L'
structure WaveK(M:Monk SU.group S) :Prop where
   gap : FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m
   glow: FreeResolvent.Gap (baseX T x (kist M).key M.park M.k 1) m
   fine : Bright T x A.hash A.trot A.room (A.ang+A.fee) A.post M β A.vita A.rota A.loft
omit hp
variable (ρ:∀ M:Monk SU.group S, Chir M x→WaveK (m:=m) A M)
variable (pu:Chir M x)(w':FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)
include pu ρ
lemma debit(u:i ∉ (N').key.dome (A.loft*radiusB x)) : K₀ ((N').park,(N').k) i (N').V= payZ f (K₀ (M.park,M.k) (Λ i) M.V):=by
 have hh : i∉ (A').key.dome (j'*radiusB x):=by unfold rot dice at u; split at u <;> exact u
 have hp:= sing_b M f.s (Facet.pasta f) pu; have he:= (ρ M pu); have hV:=ρ _ hp; have hl := aheadQ A M f.s (Facet.pasta f) h he.gap hv hz ht hi hm i he.fine hV.fine hh he.glow; let Y':=K₀ ((A').park,(A').k) i (A').V
 have hz₀(f':ℝ):payZ f (f':ℂ)=f':=by unfold payZ cSignX; split; simp; rfl
 change _=payZ f (K₀ _ (affine f.s (Facet.pasta f) i) M.V); rw [←hl]; change _=payZ f Y'; have hT:payZ f Y'=Y':=by unfold Y'; rw [hV.fine.sung _ hh,hz₀]
 rw [hT]; have hg:=ρ _ (rotT M f pu); unfold rot dice at hg ⊢; split
 next p=> rw [if_pos p] at hg; exact behindB A _ h hV.gap hv hz hA hB ht hi hm i hV.fine hg.fine hh
 rfl
omit pu ρ
end YM.CF.Tye
