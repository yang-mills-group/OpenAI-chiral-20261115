import YM.CF.Iva.Lore
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
variable {s_ s1 c c' e0 v v' z L:ℝ}{r r' b0 κ:ℕ} -- tune
local notation "Ω"=> Domain N B
local notation "Χ"=> Domain P B
local notation "G'"=> SU.group
local notation "φ_"=> nomA N P B
local notation "d"=> Single (mid N B)
variable {R_ b_ j r0:ℕ}{J:nomA N P B→ Op (Single (mid N B))}{Φ:nomA N P B→ℂ}
local notation "κ₀"=> ((Z.post+90)*radiusB x)
variable (g:Gard (a:=s_) (a':=s1) (C:=C) (c:=c) (v:=v) (D:=D) (Z:=z) (Φ:=Φ) (J:=J) (n:=n) (R₁:= R_) Z r r' b0 κ)
local notation "H"=> Rent0 G e
local notation "Q"=> ((Z.loft)*Ba)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
abbrev frostC(i:Site Ω):= (Muster.per Z M i-(fotoP Z M i)- motoP Z M i)
abbrev coin_ (Z:Muster G S x e T)(W:Monk G₅ S)(C: Monk SU.group S→ Rent0 G e)(o:Site Ω):= poll Z W o (C W) (C (Cay.rough W 0))
local notation "dθ"=> Directions SU.group (Domain N B)
lemma frost_s(i:Site Ω)(a b c d' e f g' h:ℝ) (q:i∈ M.key.dome Q)
 (u:Allows k (fun y=>footS Z (Wa y) i) 0 a)(v:Allows k (fun y=>wish Z (Wa y) i) 0 b)(s:Allows k (fun y=>cluck Z (Wa y) i) 0 c)(p:Allows k (fun y=>kite T x q_ Z.room l_ (Wa y) Z.beta Z.vita Z.rota i) 0 d')(p':Allows k (fun y=>qerr T x q_ Z.room l_ (Wa y) i) 0 e)(C: |xurn Z M i|≤ f) (V:Allows k (fun y=>fotoP Z (Wa y) i) 0 g')(U:Allows k (fun y=>motoP Z (Wa y) i) 0 h): Allows k (fun y=> frostC Z (Wa y) i) 0 (((a+b+c)+(d'+e))+f+g'+h):=by
 let χ(y:dθ):= blunt Z (Wa y) i; have he:Allows k χ 0 (d'+e):= (p.add p').germ (Eventually.of_forall (fun y=>(if_pos q).symm)); have hk: Allows k (fun y=> Muster.per Z (Wa y) i) 0 (((a+b+c)+(d'+e))+f):=by
    let hp:= (((((u.add v).add s).add he).add (Jet.allows_const (v:=xurn Z M i) 0 (show ‖xurn Z M i‖≤_ from C))).linear Complex.ofRealCLM (show ‖Complex.ofRealCLM‖ ≤1 by simp)) -- Definally xurn constant
    exact hp.mono (by rw [one_mul])
 exact Newt.subtract_p (Newt.subtract_p hk V) U
variable (F: Monk SU.group S→ Rent0 G e)(W P':E→ Rent0 G e)(O:Support (Domain N B)){M': Monk SU.group S}
variable (I I': E→L[ℝ] Directions SU.group (Domain N B))
local notation "N'"=> (fun i:E=>M'.atop (I' i) x)
local notation "N_"=> (fun i:E=>M.atop (I i) x)
local notation "t₀"=> (M.park,M.k)
local notation "t₁"=>(M'.park,M'.k)
variable (ht:∀ᶠ i in 𝓝 (0:E), Muster.Post Z (M.atop (I i) x) (M'.atop (I' i) x) (W i) (P' i) (F (M'.atop (I' i) x)) (F (Cay.rough (M'.atop (I' i) x) 0)) κ O)
lemma hg_k (p:‖I'‖ ≤ 1) (G0 : Directions SU.group (Domain N B)→ ℂ) (c0':ℝ)(y:Allows k G0 (0: Directions SU.group (Domain N B)) c0'): Allows k (G0 ∘ I') (0:E) (Jet.composeCost k c0' 1) := Allows.comp (f:=I') ((map_zero I').symm ▸ y) (allows_linear p (by rw [map_zero,norm_zero]; exact zero_le_one))
include g ht
variable {c0 c1 B2 a3 L0:ℝ}
lemma rim_s (p:‖I'‖ ≤ 1)(i:Site (Domain N B))(z:Beat.shadows (o:=i) O b0)(U:0≤L0)(Y:M'.V=M.V)(hq:M.park=M'.park)(hx:M.k=M'.k)(v:∀ h₀:i∈ M'.key.dome Q, Allows k (fun y=> frostC Z (M'.atop y x) i) 0 a ∧ (‖FPT Z Z.Beds i‖≤c0))
 (v1:∀ u:i∉ M'.key.dome Q, Allows k (fun y=>coin_ Z (M'.atop y x) F i) 0 b ∧ |xurn Z M' i| ≤ c1) (hu: i∈ M.key.dome Q → Allows k (fun x=> FPT Z (W x) i) 0 c') (hθ: Jet.composeCost k a 1+(c0+c') ≤ L0)(hp:Jet.composeCost k (b+c1) 1 ≤ L0):Allows k (fun x'=> burnS Z (M.atop (I x') x) (W x') (P' x') i) 0 L0:=by -- note build direct real near, far fiscal

 have hK:i∈ M.key.dome Q ↔ i∈ M'.key.dome Q:= gateL (M.atop (I (0:E)) x) ht.self_of_nhds.duo i b0 z (by rw [separation_self]; exact (zero_add _).le.trans g.hunter.toe)
 by_cases x':i∈ M.key.dome Q
 · obtain ⟨v,h⟩:= v (hK.mp x'); refine (((hg_k I' p _ a v).add (Newt.subtract_p (Jet.allows_const _ h) (hu x'))).mono hθ).germ ?_; filter_upwards [ht] with i' z'; unfold burnS Muster.lore; unfold prum; rw [if_pos (show i∈ (M.atop (I i') x).key.dome Q from x')]; have hg:= peri_p Z (M.atop (I i') x) R_ κ b0 z'.duo g.ash g.ages i z'.kindB g.hunter z g.beta; change Muster.per Z (M'.atop (I' i') x) i - _-_+_= _; rw [←hg]; rw [show fotoP Z (M'.atop (I' i') x) i=fotoP Z (M.atop (I i') x) i from ?_, show motoP Z (M'.atop (I' i') x) i=motoP Z (M.atop (I i') x) i from ?_]; -- via definitions park K but views differ!
   · change _-fotoP Z _ _-motoP Z _ _+ (FPT Z Z.Beds i- FPT Z _ i)= _+ (_-fotoP Z _ _-motoP Z _ _); unfold FPT; abel
   · exact (oaths (M.atop (I i') x) z'.duo z'.kindB i b0 z g.hunter.scene g.hunter.wise g.hunter.pureT g.hunter.oath g.hunter.toe (g.hunter.hero Z.xip (by simp))).symm
   exact (oaths (M.atop (I i') x) z'.duo z'.kindB i b0 z g.hunter.quote g.hunter.note g.hunter.pureT g.hunter.oath g.hunter.toe (g.hunter.hero Z.etap (by simp))).symm
 obtain ⟨hb,hv⟩:= v1 (mt hK.mpr x')
 let X'(y: Directions SU.group (Domain N B)):=burnS Z (M'.atop y x) (F (M'.atop y x)) (F (Cay.rough (M'.atop y x) 0)) i; have hy : Allows k X' 0 (b+c1):=by
    refine (hb.add (Jet.allows_const _ (v:=(↑(xurn Z M' i):ℂ)) (by rw [Complex.norm_real]; exact hv))).germ ?_; filter_upwards with y; exact sub_add_cancel (X' y) _
 apply ((hg_k I' p _ _ hy).mono hp).germ; filter_upwards [ht] with i' z'; exact (fisc Z _ _ _ R_ κ b0 _ z'.duo g.ash g.ages i z'.kindB g.hunter z _ g.trih g.beta g.pole z'.port z'.noth).symm
end YM.CF.Iva
#print axioms YM.CF.Iva.rim_s
