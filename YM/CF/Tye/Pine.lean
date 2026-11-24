import YM.CF.Tye.Way
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
local notation "Uᴳ"=> male e G f U'
local notation "F'"=> payZ f
variable (ρ:∀ M:Monk SU.group S, Chir M x→WaveK (m:=m) A M) (pu:Chir M x)
variable (O: Palot.leaf (Site (Domain N B)))(k:ℕ)
include ph
lemma queen_s(i:Support (Domain P B)): i∈Lich.Muster.queen (S:=S) (x:=x) k O↔ weaveS G f i ∈Lich.Muster.queen (S:=S) (x:=x) k (chute f O):=by
 have he: hatY S (weaveS G f i)=(hatY S i).image (chart f):=by
    change (i.image _).image _=_; unfold hatY; rw [image_image,image_image]; exact image_congr fun j _=>Facet.gearP S G ph f j
 simp only [Lich.Muster.queen,Tee,Hest.portA,mem_filter,mem_compl, mem_univ,true_and, rumR,he]; refine and_congr Iff.rfl ?_; rw [show Lattice.halo k ((hatY S i).image (chart f))= _ from dignify (hatY S i) f.s (Facet.pasta f) k]; exact (image_injective (chart f).injective).eq_iff.symm
include pu ρ h hA hB hv hz t xw
lemma pedal_s: pedal A (rot f M) Uᴳ k O=F' (pedal A M U' k (chute f O)):=by
 have he:shardy A (rot f M) k O= shardy A M k (chute f O):=by
    have hu:= shard_s A M f.s (Facet.pasta f) h (ρ M pu).gap hv hz O k; unfold rot dice; split; next p=> exact (shard_f A A' h (ρ _ (sing_b M f.s (Facet.pasta f) pu)).gap hv hz hA hB O k).trans hu
    exact hu
 unfold pedal; rw [he, vaultT A M f]; rw [←din_t f ((_:ℂ)+ _),map_add,map_add,din_t,din_t,pin_z,map_sum]; congr 1
 refine sum_equiv (weaveS G f) (queen_s f ph O k) fun i _=>?_ ; have hp(C: Rent0 G e) : Q i (male e G f C)=payZ f (Q (weaveS G f i) C):=by let hp:=t f (weaveS G f i) C; rw [show toRoar G f⁻¹ (weaveS G f i)=i from (weaveS G f).symm_apply_apply i] at hp; exact hp
 rw [map_sub,hp U']; have ht:=hp A.Beds; rw [mink_B A f xw] at ht; rw [din_t,din_t,ht]
omit pu ρ h hA hB hv hz t xw
variable {U₁ U₂ U₃:ℝ}{n:ℕ}{Φ:nomA N P B→ Op (Single (mid N B))}
variable(w:Ind G A.Fame U₁ U₂ U₃ n Φ)(Q':UNI SpinIdx)(gw:JetS f.s f.charge (detX f.s) Q')
local notation "A₁"=> yank f.charge (castX f) Q'
include gw w
lemma lega_s : legA A Uᴳ k O=A₁ (legA A U' k (chute f O)):=by
 unfold legA; rw [yank_p A f w Q' gw]; refine sum_equiv (weaveS G f) (queen_s f ph O k) fun i _=>?_ ; let hp:=fame_s A f Q' U' gw w (weaveS G f i); rwa [show toRoar G f⁻¹ (weaveS G f i)=i from (weaveS G f).symm_apply_apply i] at hp
omit gw w ph
end YM.CF.Tye
