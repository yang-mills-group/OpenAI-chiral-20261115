import YM.SU5.Exchange.Seed.Fit
import YM.SU5.Exchange.Seed.Zero
import YM.SU5.Exchange.Seed.Keys
import YM.SU5.Exchange.Seed.Marks
import YM.CF.Rive.New
import YM.CF.Song.Pads
import SatinThinTopic
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open scoped YM.CF.Mew
-- economics from root consultations only: near-b has cheap derivative figure.
-- using paid sterile part F1 with common root orientation. no rotating here
-- nor assuming scalar/electrics after root mixes.
structure Occlus (P:BudgetPoint) where
 κ:ℝ
 uΓ:ℝ
 w:ℝ
 γ:ℝ
 c:ℝ
 d:ℝ
 e:ℝ
 η:ℝ -- spare bandwidth for conversion (5*? from timer-tail)
 hγ:0 < γ
 hη:0 < η
 hw: P.supportExponent+4*η ≤ uΓ-w
 degree: degreePrice P.B (100*γ) η ≤ 1/2
 degree0: degreePrice P.B γ η < 1
 still: γ*(1-degreePrice P.B γ η)⁻¹≤ 1
 covers: γ+Real.exp 1*(γ*(1-degreePrice P.B γ η)⁻¹) ≤ 100*γ
variable (C:Occlus P)
local notation "uO"=> C.κ
local notation "ϵ"=> C.η
local notation "γN"=> C.γ
local notation "ΘΩ"=> P.supportExponent+C.η
local notation "σℓ"=> P.supportExponent+C.η+C.η
local notation "σH"=> P.supportExponent+C.η+C.η+C.η
local notation "θr"=> degreePrice P.B C.γ C.η
local notation "cQ"=> C.γ*(1-degreePrice P.B C.γ C.η)⁻¹
local notation "σH'"=> γN*200
abbrev yσE(P:BudgetPoint)(C:Occlus P):ℝ:= Nor.reserveT P.power P.order P.B C.η * (C.γ * (1-degreePrice P.B C.γ C.η)⁻¹)
abbrev yσF(P:BudgetPoint)(C:Occlus P):ℝ:= Nor.reserveT P.power P.order P.B C.η *(C.κ⁻¹ * (C.γ*200))
variable{I:Type}[LinearOrder I][Fintype I](F:ForceBudget n)(K : Key I→ Rinse (Seat n) (Copy n))(z b: Aura n→ℝ)(r:Aura n→Support (More n)→ℝ)
local notation "J"=> settleK F
-- step_Craft. request one linear Parameter; don’t need common Kcash ordering.
variable (σ:I→Seat n)(q:ℕ)(M:Key I→ Orbit n→ Aura n→ FC (Dwell n)) -- verify hη direction
local notation "Q_'"=> wingQ -- unused
structure OrbitRack (C:Occlus P) (σ:I→Seat n) (q:ℕ) (F:ForceBudget n)(h:ℝ) (K:Key I→Rinse (Seat n) (Copy n))(z b:Aura n→ℝ)(r:Aura n→ Support (More n)→ℝ) (M:Key I → Orbit n→ Aura n→ FC (Dwell n)) : Prop where
 pigment: ∀ X:Aura n,∀ D ⊆ X.val,Stax.Fray P h (cipherK q) X D (settleK F X D) (r X D)
 price: ∀ z'∈hill I, Stax.Pitch P h (cipherK q) (K z') z (M z')
 birth: ∀ z'∈hill I, ∀ X:Aura n, Stax.Fray P h (cipherK q) X ∅ (K z' X ∅ X 1) (b X)
 gamb: Gamble K -- gives homogeneous
 turns:∀ (u:ℕ)(X:Aura n),∀ D⊆X.val,Hush σ X.val (fun z=> layerN (settleK F) (K z) u X D) -- to be discharged via root condition.
 plain:∀ (z':Key I),∀ m,Bake.Turf (fun i:Aura n=> layerN (settleK F) (K z') m i ∅)
 empty:∀ u, Stax.layerN (settleK F) (K 0) u=settleK F
 timer:Timer (uChip z b r) z C.κ C.uΓ C.w (Sour.widthK n P.B) (Sour.spanV P.B) C.γ C.c C.d C.e 1 b
variable (L:OrbitRack C σ q F h K z b r M)(u:ℕ)(p:1≤h)
def lensCells (k:Key I):Cusp n:= layerN (settleK F) (K k) u
local notation "Θ"=>lensCells F K u
abbrev lensSimple (k:Key I) (X:Aura n):Copy n:= (layerN (settleK F) (K k) u X ∅) -- θ.
local notation "ΩΘ"=>lensSimple F K u
abbrev lensG (k:Key I):= FeeD P (lensSimple F K u k)
local notation "Ψg"=>lensG (P:=P) F K u
abbrev lensK(k:Key I):= roomV P (ΩΘ k) (Θ k) 0
local notation "Ψk"=>lensK (P:=P) F K u
variable (τ:Ids n)
local notation "s'"=> paidLayers r z b u
abbrev lensD (z':Key I): RegBudget n:= cast_E (Ψg z') τ
local notation "Dθ"=>lensD (P:=P) F K u τ
abbrev lensPort(z':Key I): ForceBudget n:= budgetR (Ψk z')
local notation "DΚ"=> lensPort (P:=P) F K u
include L p
lemma rackPay(z':Key I)(v:z'∈hill I)(X:Aura n)(D:Support (More n))(e:D⊆X.val) : Stax.Fray P h (cipherK q) X D (Θ z' X D) (s' X D):=paidN J r L.pigment _ z b (L.price z' v) (zero_le_one.trans p) (L.birth z' v) u X D e
omit L p -- compress params
variable {z b r} -- dimensions implicit? include rely
include L p
lemma rackMoney : Ready Palot.stern P.B (urnL s') (σH) C.γ C.η (degreePrice P.B C.γ C.η) ∧∀ i:Seat n,tallB (Vow.hymn s') P.B (σH) i ≤ uO⁻¹*γN:=by
 let A:=L.timer; have h':=zero_le_one.trans p
 have s_(X:Aura n)(D:Support (More n))(e:D⊆X.val) :0≤ s' X D:=(rackPay C F K z b r σ q M L u p _ roots X D e).merit.wage h'; have u_:=C.hw
 have hT: (σH+C.η)≤ C.uΓ-C.w*1:=by rw [mul_one]; linarith only [u_]
 have ht(i:Seat n):tallB (roofL s' uO) P.B (C.uΓ-C.w*1) i≤γN:=Stax.chargeLayers r z b u _ A i
 have hs(i):= lam_H s' i C.κ _ _ (zero_lt_one.trans_le A.slope) s_ (ht i)
 have he:0 ≤ Vow.hymn s':=fun i=>sum_nonneg fun j v=>s_ i j (mem_filter.mp v).2.2
 have hr:0 ≤ urnL s':=fun i=> s_ i _ (empty_subset _)
 refine ⟨ready_T C.hγ C.hη C.degree0 hr (fun i=>(tall_m _ hr hT i).trans (hs i).1),fun i=>(tall_m _ he ((le_add_of_nonneg_right C.hη.le).trans hT) i).trans (hs i).2⟩
open Palot Bake
lemma layerSuit(z':Key I)(v:z'∈hill I) : (∀ X:Aura n,Vow.Medal P X.val ∅ (ΩΘ z' X) h (urnL s' X))∧ ArmsK P (Θ z') (s') h:=by
 let ht:= rackPay C F K z b r σ q M L u p z' v; exact ⟨fun X=> (ht X ∅ (empty_subset _)).merit,frame_v ht ⟩
local notation "hb"=>heat_q -- unused
lemma lowLens (z':Key I)(v:z'∈hill I): ( (∀ i, PressB P i ((Dθ z') i) h (pence_Q P (fun X=> spanD X (urnL s') 0) i)) ∧ ∀ j:Seat n,(∑ i:Scree.Hub n, filmK P (σℓ) i j*pence_Q P (fun X=> spanD X (urnL s') 0) i)≤yσE P C ) ∧ ( (∀ i,ForceB P i ((DΚ z') i) h (rentH P (windF s' (bagU (urnL s') 0)) i)) ∧ ∀ j:Seat n,(∑ i:Force n, giftK P (ΘΩ) i j* rentH P (windF s' (bagU (urnL s') 0)) i) ≤ yσF P C ):=by
 let ℓ:=s'; obtain ⟨c0,c1⟩:= rackMoney C F K σ q M L u p; obtain ⟨r₀,fκ⟩:=layerSuit C F K σ q M L u p z' v
 have hη:=C.hη; have hX:=P.exponent_pos; have hy:0 ≤ σℓ:=by linarith
 obtain ⟨Q',gQ⟩:= Vow.rent_x fκ (w:=0) (Q:=0) (fun X D _ _=>Vow.Medal.zeroT) le_rfl c0 hy r₀ hη p L.timer.slope (fun i=> by change 0+_≤ (1:ℝ); rw [zero_add,pow_zero,mul_one]; exact C.still) (L₁:=0) (fun i=> by simp [tallB]) c1 C.degree (show (1/2:ℝ)<1 by norm_num) (mul_pos (by norm_num) C.hγ) (by rw [pow_zero,mul_one,add_zero,← mul_assoc,mul_inv_cancel₀ (by linarith [L.timer.slope]),one_mul]; exact C.covers) -- orientation
 have hv(i):tallB (spanD · (urnL s') 0) P.B (σH) i≤ cQ:=by have he:= thinX c0 (add_nonneg hy hη.le) i 0; rw [pow_zero,mul_one] at he; exact he
 refine ⟨reserveZ (P:=P) (fun X=> spanD X (urnL s') 0) _ (fun i=>glenP i p r₀ c0 (add_nonneg hy hη.le) 0) (turfK (ΩΘ z') (L.plain z' u)) τ hv (zero_le_one.trans p) C.hη, reserveF (P:=P) _ _ Q' (fun i=> ?_) (zero_le_one.trans p) C.hη⟩
 apply le_inv_mul_iff₀ (zero_lt_one.trans_le L.timer.slope) |>.2; exact (gQ i).trans_eq (by ring)
lemma layerRay (X:Aura n)(D:Support (More n))(e:D⊆X.val) (V:Orbit n):River (fun z=> (Θ z) X D V):=by
 let R:Copy n →ₗ[ℂ]Cipher n:=LinearMap.proj V; unfold lensCells layerN; simp_rw [Finset.sum_apply]; exact (tip_bank _ _ (fun i _=>(show Solvent i _ from Solvent.map R (chipsSol _ K L.gamb X D e i)).riv)).1
lemma lensSimpleR (X:Aura n)(V:Orbit n):River (fun z=> (Ψg z) X V):=by
 let A:=(rackMoney C F K σ q M L u p).1; have hp:=C.hη; have hx:=P.exponent_pos
 exact lore_Y (ΩΘ) P p (fun x y=>layerRay C F K σ q M L u p x _ (empty_subset _) y) (fun _=>urnL s') (by linarith : 0≤ σH) (fun _ _=> A) (fun z v=> (layerSuit C F K σ q M L u p z v).1) (ready_pos Palot.stern P.B A).le C.degree0 X V
lemma lensOrigin : Dθ 0=0 ∧ (DΚ 0)= budgetR (settleK F):=by
 have he: ΩΘ 0=0:=by change (fun i:Aura n=> layerN (settleK F) _ _ i ∅)=_; rw [L.empty]; exact funext (settle0 F)
 refine ⟨?_,?_⟩
 · funext i x; unfold lensD lensG Ione.cast_E; rw [he,TreasuryFog.costBright]; simp
 funext i; let d:=extraD i; unfold lensPort lensK lensCells budgetR; rw [L.empty,he,TreasuryFog.brightZero P _ i.property.1 i.property.2]
lemma totGas (A: ForceBudget n)(V:Orbit n) : hGas (flags P.threshold V.1) (hailV (flags P.threshold V.1) (settleK A) V) = beamP P (settleK A) V:=by
 let O:=flags P.threshold V.1; unfold beamP hGas Hac; symm; refine sum_subset (show highV O⊆_ from fun i p=> let h:= (mem_filter.mp p).2; mem_filter.mpr ⟨mem_univ _,h.1,h.2.1⟩) ?_
 intro j v q; by_contra y; apply q; obtain ⟨p,u⟩:= (mem_filter.mp v).2; refine mem_filter.mpr ⟨mem_univ _,p,u,fun i l w=>?_⟩
 have he:O∩i.val=∅:= disjoint_iff_inter_eq_empty.mp (Disjoint.symm w); refine y (prod_eq_zero l ?_); change settleK A i (O∩i.val) V=0; rw [he,settle0]; rfl

lemma lensCash (z':Key I)(V:Orbit n)(e:FleetS P.threshold V.1)(v:z'∈hill I): hGas (flags P.threshold V.1) (hailV (flags P.threshold V.1) (Θ z') V)= exp (exponentL P (Dθ z') V.1)*fueled P (F+(DΚ z'-DΚ 0)) V:=by
 let O:=flags P.threshold V.1; let G:= Θ z'
 have ht: hailV O G V= keyL P G (ΩΘ z') V:=by
    funext i; unfold keyL; split; next h=> unfold hailV; rw [disjoint_iff_inter_eq_empty.mp h]; rfl
    next h=>rfl
 have h':0 ≤ σℓ:=by have hz:=C.hη; have ht:=P.exponent_pos; linarith
 have hB:= (layerSuit C F K σ q M L u p z' v); have hr:= Vow.polyH G (0:Cusp n) V _ (rackMoney C F K σ q M L u p).1 p hB.1 (add_nonneg h' C.hη.le) e (exponentL P (Dθ z') V.1) (by rw [prizes0,add_zero]; exact Ione.ocean P (Ψg z') τ (Bake.turfK _ (L.plain z' u)) V)
 change Palot.hGas O (hailV O G V)= _; rw [ht,hr]; exact congrArg (fun v=>_* v) (TreasuryFog.budgetDisplace V (Ψk z') e F (DΚ 0) (fun i v=>by
    rw [(lensOrigin C F K σ q M L u p τ).2, TreasuryFog.eachFace _ _ i _ inter_subset_right] -- tune params
    exact Finset.not_disjoint_iff_nonempty_inter.mp (fun h=>v h.symm)))

end TreasuryFog
end YM.CF.Vow
