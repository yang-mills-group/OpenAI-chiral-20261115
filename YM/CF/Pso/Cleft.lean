import YM.CF.Pso.Etna
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
variable {v u:ℝ}(hp1:0<u)(ht':0<v)
local notation "Mt"=> poleY M v u
local notation "Vt"=> tint_z A v
local notation "Ut"=> tint_z A u
local notation "fu"=> M.fuel x T q v' L' u
local notation "fo"=> M.sent x T q v' L' u
variable {ρ:Type}[TopologicalSpace ρ](P_:ρ→ℝ)(c:Continuous P_)(hhP:∀ i,0<P_ i)
local notation "ζt" i:max=> tint_z A (P_ i)
local notation "ℙt" i:max=> poleY M (P_ i) u
lemma pay_h (N:Type*) [LinearOrder N][Fintype N]: Continuous (Pastry.hollow (n:=N)):=Continuous.subtype_mk (continuous_id.smul continuous_const : Continuous (fun i:ℂ=> i • (1:Fock.FC N))) _
include M A T ht' hp1
lemma boon_w (C:Bond (Domain P B)): boon (Vt) C (Mt)= boon (Ut) C M:=by
 unfold boon; split
 · rename_i he; change ∃ _ , _ at he
   let p':∃ i∈(locals M.key M.key x M.park ((j'+104)*radiusB x))ᶜ,i.val.val=C:=he
   rw [dif_pos p']; exact congrArg (fun f:Prices SU.group (Active M.key x M.park)=>broad q v' (tape f p'.choose)) (spirit_X A M hp1 ht').1
 rename_i hp; split
 next h'=> exact False.elim (hp h')
 rfl

omit ht'
include c hhP
lemma cuff_w (C:Sat S)(v w:ℝ):Continuous (fun z=> portF (ζt z) (ℙt z) v w C):=by
 have hx (z:ρ): portF (ζt z) (ℙt z) v w C= portF (Ut) M v w C:=by
    obtain ⟨a,p⟩:=spirit_X A M hp1 (hhP z)
    let U₁:= ℙt z; obtain C|C|C:= C
    · change (if C∈(nearFace S (M.key.dome ((j'+110)*radiusB x)))ᶜ then tokenF M.key q x (U₁.sent x T q v' L' (P_ z)) C else 1)=_; rw [p]; rfl
    · change (if C∈(nearNoise (M.key.dome ((j'+100)*radiusB x)))ᶜ then tidal M.key x v w q (U₁.sent x T q v' L' (P_ z)) M.V M.k C else 1)=_; rw [p]; rfl
    unfold portF; dsimp only [Sum.elim_inr]; apply boon_w A M hp1 (hhP z) C

 rw [funext hx]; exact continuous_const
lemma coin_c (C:Words S)(r k:ℕ)(v w:ℝ): Continuous (fun z=> wistL (ζt z) (ℙt z) W U' r k v w C):=by
 obtain C|C|C:=C
 · change Continuous (fun z=>hollow (n:=LeanV (Single (mid N B))) (portF (ζt z) (ℙt z) v w C:ℂ)-1); exact ((pay_h _).comp (Complex.continuous_ofReal.comp (cuff_w A M hp1 P_ c hhP C v w))).sub continuous_const -- fee theorem v w signature! uses u positive but want arbitrary
 · unfold wistL sweetK DocF DocY fount pendant; dsimp only [Sum.elim_inr,Sum.elim_inl]; by_cases h:C ∈ M.key.dome r
   · dsimp only [poleY,Cay.rough,tint_z]; simp only [h, if_true]; exact continuous_const
   dsimp only [poleY,Cay.rough,tint_z]; simp only [h,if_false,not_false_eq_true]
   exact ((((pay_h _).comp (Complex.continuous_exp.comp (mig_c A M W U' C hp1 P_ c hhP))).mul (continuous_const (y:=exp (boat (doubleK (Corne.led G x A.Fame U') C))))).sub continuous_const)
 unfold wistL sweetK DocF DocY pedal; dsimp only [Sum.elim_inr]; simp_rw [fun z=> long_z (v:=P_ z) (u:=u) A M C]
 exact ((((pay_h _).comp (Complex.continuous_exp.comp ((continuous_const.add (Complex.continuous_ofReal.comp (tide_c A M hp1 P_ c hhP k C))).add (continuous_const (y:= ∑ j∈ Lich.Muster.queen (x:=x) (S:=S) k C,(A.LawQ j A.Beds-A.LawQ j U')))))).mul (continuous_const (y:= exp (boat (legA A U' k C))))).sub continuous_const) -- braces
lemma heed_c (r k:ℕ)(O:Hos S k)(v w:ℝ)(Id:ρ→ℝ)(t:Continuous Id)(h:∀ i,Id i≠0): Continuous (fun z=> heedP (ζt z) (ℙt z) W U' r k v w (Id z) O):=by
 let φ(z):= senseC (ζt z) (ℙt z) (r:=k) v w (Id z) (O:Hos S k); have hf:Continuous φ:=by
    unfold φ senseC treat Monk.pep; dsimp only [tint_z] -- implicit projections
    simp_rw [fun z=> (ball_m A M hp1 (hhP z) w v O.val).1,fun z=> (ball_m A M hp1 (hhP z) w v O.val).2.1,fun z=> (ball_m A M hp1 (hhP z) w v O.val).2.2]; -- tuner ν extends O card
    change Continuous (fun z => _*Real.exp (P_ z/u*_) * _ * (Id z)⁻¹^Fintype.card (Frozen O.val x M.park)); exact (((continuous_const.mul (Real.continuous_exp.comp ((c.div_const _).mul continuous_const))).mul continuous_const).mul ((t.inv₀ h).pow _))
 have ht:Continuous (fun z=>hont (ζt z) (ℙt z) W U' r k O):= (Complex.continuous_ofReal.comp (sore_c A M hp1 P_ c hhP O.val)).add (continuous_finsetSum (O.val.dome r) (fun j _=>mig_c A M W U' j hp1 P_ c hhP))
 exact ((pay_h _).comp ((Complex.continuous_ofReal.comp hf).mul (Complex.continuous_exp.comp ht))).mul (continuous_const (y:=exp (boat (haunt A U' r k O))))
end YM.CF.Tye
