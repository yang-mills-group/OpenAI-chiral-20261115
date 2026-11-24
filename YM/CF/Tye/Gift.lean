import YM.CF.Tye.Harp
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
open Nacre Matrix Further.CurvedGaussianJets.Tracks PhysicalNext.OrderedAffine2B.SymFare
variable{z v C D:ℝ}{n k:ℕ}{Φ:nomA N P B→ℂ}{θ:nomA N P B→Op (Single (mid N B))}
variable(ρ:∀ M:Monk SU.group S, Chir M x→WaveK (m:=m) A M)(pu:Chir M x) (u:Baton A)
-- simultaneous stage matrix could use arbitrary gFine only coarse transform required. E/K masks.
variable (v1:Palot.leaf (Site (Domain N B)))
include h hp hv hz
lemma path_g {j:ℕ}(w:LinkS S j): Tarn.pave T x q v' L' w V=Tarn.pave T x q v' L' w M:=by
 unfold Tarn.pave; by_cases p:∃ u:Run ((shiftZ g M).zoo x) (j+1), Tarn.stave u=w; swap
 · rw [dif_neg p,dif_neg (show ¬∃ u:Run (M.zoo x) (j+1),Tarn.stave u=w from p)]
 let he:∃ u:Run (M.zoo x) (j+1),Tarn.stave u=w:=p; rw [dif_pos p,dif_pos he]; exact Tarn.collectG g T x q v' L' M h p.choose hp hz hv
lemma mass_g: massX A V v1=massX A M v1:=by
 unfold massX; refine tsum_congr fun j=>sum_congr rfl fun i _=> sum_congr rfl fun a _=>?_ ; unfold leys; rw [path_g A M g h hp hv hz]; rfl
omit h hp hv hz
include h hv hz pu ρ
lemma wake_a: mace A V v1=mace A M v1:=by
 unfold mace patrol; apply congrArg; refine sum_congr rfl fun f _=>?_ ; obtain ⟨i,hx⟩:=gapG M g f; rw [hx]; have he:=mass_g A (Cay.rough (rot f M) 0) i h (ρ (rot f M) (rotT M f pu)).gap hv hz; simp only [he]
omit h hv hz pu ρ
include u
lemma beam_g: mare A V i= mare A M i:=by
 unfold mare patrol; apply congrArg; refine sum_congr rfl fun j _=>?_ ; obtain ⟨v,h⟩:=gapG M g j; rw [h,u]
omit u
include h hp hv hz hb ht hi hm
lemma mix_g : mix A V i=mix A M i:=by
 unfold mix; rw [Tye.wish_g A M g h hp hv hz i,flock_g A M g h hp hv hz hb i, show artU T x q v' L' V i=artU T x q v' L' M i from rfl]; unfold blunt; change _+ (if i∈ Ω then _ else _)+_= _; split; next v=> rw [kite_g T M _ _ _ _ _ h hp hv hz J R ht hi hm, qerr_g T M _ _ _ _ h hp hv hz g i]
 rw [zen_g T M x q v' L' β h hp hv hz _ _ ht hi hm g]
variable (p:Tally A.LawQ Φ z v C D n) (w: Site (Domain P B)→ SU.E)
local notation "F'"=> (dressL G e).dress w
local notation "Mt"=> ActZ (scaleG G w)
omit h ht hi hm hb hz hp hv
include p
lemma pint_g : fJ G Q x (F' W) i=fJ G Q x W i:=by
 unfold fJ; apply sum_congr rfl; intro j _; obtain ⟨v,H',h⟩:=p.members; rw [(H' j).gauge]
include u h ht hi hm hb hz hp hv
lemma mark_g : mig A V (F' W) (F' U') i=mig A M W U' i:=by unfold mig; rw [mix_g A M g h hp hv hz ht hi hm hb,beam_g A M g i u]; unfold prum; rw [pint_g A W i p w,pint_g A U' i p w]
variable (O:Hos S k)(r:ℕ)
lemma stove_g:hont A V (F' W) (F' U') r k O=hont A M W U' r k O:=by unfold hont; simp_rw [mark_g A M g h hp hv hz ht hi hm hb W U' _ u p w]; rw [sore_g A M g h hp hv hz ht hi hm]
omit ht hi hm hb u
include pu ρ
lemma ped_g : pedal A V (F' U') k v1=pedal A M U' k v1:=by
 unfold pedal; rw [wake_a A M g h hv hz ρ pu,shard_g A M g h hp hv hz]; obtain ⟨v,H',_⟩:=p.members; simp_rw [(H' _).gauge]
omit h hp hv hz pu ρ p
variable(hK:Ind G A.Fame z v C n θ)
include hK
lemma fount_g:fount A V (F' U') k i=Mt (fount A M U' k i):=by
 unfold fount; change (if i∈M.key.dome k then _ else _)= _; split; unfold ActZ; rw [map_zero]; rw [med_g A U' hK w]; exact (piece_g ..).symm
lemma leg_g: legA A (F' U') k v1=Mt (legA A U' k v1):=by unfold legA ActZ; rw [map_sum]; refine sum_congr rfl fun i _=>?_ ; obtain ⟨v,h,_⟩:= hK.port; exact (h i).gauge _ U'
lemma haunt_g : haunt A (F' U') r k O= Mt (haunt A U' r k O):=by unfold haunt ActZ; rw [map_sum, med_g A U' hK w]; refine sum_congr rfl fun i _=>?_ ; exact (piece_g ..).symm -- order
end YM.CF.Tye
