import YM.SU5.WakeFields.SwearIn
import YM.SU5.Exchange.Seed.Station

/-! # Parameterized rack. Every analytic receipt here is on the actual diagonal Key,
combined old and new. And remains on those root-arrangement Keys on joining. Allocation can
vary with them (width exponent & budgets don't vary); includes the common allocation case.
Adapt economic lemmas from `Seed/Station`. -/
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
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog

open QuadClock Waxy Push.AbsoluteSums Trees Rue Rive Vow Larch Stax Sour Cadre Mew Ione Gas Ursell
open scoped YM.CF.Mew
variable (C:Occlus P)
local notation "uO"=> C.κ
local notation "ϵ"=> C.η
local notation "γN"=> C.γ
local notation "ΘΩ"=> P.supportExponent+C.η
local notation "σℓ"=> P.supportExponent+C.η+C.η
local notation "σH"=> P.supportExponent+C.η+C.η+C.η
local notation "θr"=> degreePrice P.B C.γ C.η
local notation "cQ"=> C.γ*(1-degreePrice P.B C.γ C.η)⁻¹

variable {I : Type} [LinearOrder I] [Fintype I]
variable {C}
variable (F : Key I→ ForceBudget n) (K : Key I→ Rinse (Seat n) (Copy n))
variable (Y W : Key I → Aura n → ℝ) (J : Key I→ Aura n→ Support (More n)→ℝ)
variable (M : Key I → Bag n) (σ : I→Seat n)
--

/-- Origin needs Fleet settlement, exact K cost at the new layer & an
adjustment handle. These are used together with the analytic picture for `Flood`. -/
structure Furrow (σ : I→Seat n) (C : Occlus P) (q : ℕ) (F : Key I→ ForceBudget n)
    (h : ℝ) (K : Key I→ Rinse (Seat n) (Copy n))
    (Y W : Key I→ Aura n→ℝ) (J : Key I→ Aura n→ Support (More n)→ℝ) (M : Key I→ Bag n) : Prop where
 pigment : ∀ z∈hill I, ∀ X:Aura n,∀ D⊆X.val,Fray P h (cipherK q) X D (settleK (F z) X D) (J z X D)
 price : ∀ z∈hill I, Tint P h (cipherK q) (K z) (Y z) (M z)
 figure : ∀ z∈hill I, PictureT P (cipherK q) (K z) (M z)
 birth : ∀ z∈hill I, ∀ X:Aura n,Fray P h (cipherK q) X ∅ (K z X ∅ X 1) (W z X)
 settleQ : ∀ i:Force n, Hush σ i.val.1.val.2 (fun z=> F z i) ∧ ∀ V:Orbit n,River (fun z=> F z i V)
 visit : ∀ i:Aura n,Hush σ i.val (fun z=> M z i) ∧ ∀ V:Orbit n,Flood 1 (fun z=> M z i V)
 plain : ∀ z∈hill I,∀ k : ℕ,Bake.Turf (fun i:Aura n=> layerN (settleK (F z)) (K z) k i ∅)
 timer : ∀ z ∈ hill I,Timer (uChip (Y z) (W z) (J z)) (Y z) C.κ C.uΓ C.w (Sour.widthK n P.B) (Sour.spanV P.B) C.γ C.c C.d C.e 1 (W z)
variable {q : ℕ} {F K Y W J M σ} (L : Furrow (P:=P) σ C q F h K Y W J M) (u : ℕ) (p : 1 ≤ h)
local notation "QΨ" z:max => (settleK (F z))
local notation "sℓ" z:max k:max => paidLayers (J z) (Y z) (W z) k
namespace Furrow
section
variable (P F K)
def spaceCells (k:Key I):Cusp n:= layerN (settleK (F k)) (K k) u
local notation "Θ"=>spaceCells F K u
abbrev spaceSimple (k:Key I) (X:Aura n):Copy n:= (layerN (settleK (F k)) (K k) u X ∅) -- θ.
local notation "ΩΘ"=>spaceSimple F K u
abbrev spaceG (k:Key I):= FeeD P (spaceSimple F K u k)
local notation "Ψg"=>spaceG P F K u
abbrev spaceK(k:Key I):= roomV P (ΩΘ k) (Θ k) 0
local notation "Ψk"=>spaceK P F K u
variable (τ:Ids n)
abbrev spaceD (z':Key I): RegBudget n:= cast_E (Ψg z') τ
local notation "Dθ"=>spaceD P F K u τ
abbrev spacePort(z':Key I): ForceBudget n:= budgetR (Ψk z')
local notation "DΚ"=> spacePort P F K u
end
local notation "Θ"=>spaceCells F K u
local notation "ΩΘ"=>spaceSimple F K u
local notation "Ψg"=>spaceG P F K u
local notation "Ψk"=>spaceK P F K u
variable (τ:Ids n)
local notation "Dθ"=>spaceD P F K u τ
local notation "DΚ"=>spacePort P F K u
-- ALWAYS subtract every *seat's* displacement at previous Layer-0, of this Key.
-- Keeps the old Force on this parameter family, all addresses even with equal supports.
abbrev placePort (P:BudgetPoint) (F0 : Key I→ ForceBudget n) (G : Key I→ Rinse (Seat n) (Copy n)) (c : ℕ) (z:Key I) : ForceBudget n := spacePort P F0 G c z-spacePort P F0 G 0 z
local notation "ΔΚ"=> placePort P F K u
include L p
lemma rackPay(z':Key I)(v:z'∈hill I)(X:Aura n)(D:Support (More n))(e:D⊆X.val) : Stax.Fray P h (cipherK q) X D (Θ z' X D) ((sℓ z' u) X D):=paidN (QΨ z') _ (L.pigment z' v) _ (Y z') (W z') (L.price z' v) (zero_le_one.trans p) (L.birth z' v) u X D e
lemma rackMoney (z':Key I)(v:z'∈hill I) : Ready Palot.stern P.B (urnL (sℓ z' u)) (σH) C.γ C.η (degreePrice P.B C.γ C.η) ∧∀ i:Seat n,tallB (Vow.hymn (sℓ z' u)) P.B (σH) i ≤ uO⁻¹*γN:=by
 let A:= L.timer z' v; have h':=zero_le_one.trans p
 have s_(X:Aura n)(D:Support (More n))(e:D⊆X.val) :0≤ (sℓ z' u) X D:=(L.rackPay u p z' v X D e).merit.wage h'; have u_:=C.hw
 have hT: (σH+C.η)≤ C.uΓ-C.w*1:=by rw [mul_one]; linarith only [u_]
 have ht(i:Seat n):tallB (roofL (sℓ z' u) uO) P.B (C.uΓ-C.w*1) i≤γN:=Stax.chargeLayers _ _ _ u _ A i
 have hs(i):= lam_H (sℓ z' u) i C.κ _ _ (zero_lt_one.trans_le A.slope) s_ (ht i)
 have he:0 ≤ Vow.hymn (sℓ z' u):=fun i=>sum_nonneg fun j v=>s_ i j (mem_filter.mp v).2.2
 have hr:0 ≤ urnL (sℓ z' u):=fun i=> s_ i _ (empty_subset _)
 refine ⟨ready_T C.hγ C.hη C.degree0 hr (fun i=>(tall_m _ hr hT i).trans (hs i).1),fun i=>(tall_m _ he ((le_add_of_nonneg_right C.hη.le).trans hT) i).trans (hs i).2⟩
open Palot Bake
lemma layerSuit(z':Key I)(v:z'∈hill I) : (∀ X:Aura n,Vow.Medal P X.val ∅ (ΩΘ z' X) h (urnL (sℓ z' u) X))∧ ArmsK P (Θ z') ((sℓ z' u)) h:=by
 let ht:= L.rackPay u p z' v; exact ⟨fun X=> (ht X ∅ (empty_subset _)).merit,frame_v ht ⟩
local notation "hb"=>heat_q -- unused
lemma lowLens (z':Key I)(v:z'∈hill I): ( (∀ i, PressB P i ((Dθ z') i) h (pence_Q P (fun X=> spanD X (urnL (sℓ z' u)) 0) i)) ∧ ∀ j:Seat n,(∑ i:Scree.Hub n, filmK P (σℓ) i j*pence_Q P (fun X=> spanD X (urnL (sℓ z' u)) 0) i)≤yσE P C ) ∧ ( (∀ i,ForceB P i ((DΚ z') i) h (rentH P (windF (sℓ z' u) (bagU (urnL (sℓ z' u)) 0)) i)) ∧ ∀ j:Seat n,(∑ i:Force n, giftK P (ΘΩ) i j* rentH P (windF (sℓ z' u) (bagU (urnL (sℓ z' u)) 0)) i) ≤ yσF P C ):=by
 let ℓ:=(sℓ z' u); obtain ⟨c0,c1⟩:= L.rackMoney u p z' v; obtain ⟨r₀,fκ⟩:=L.layerSuit u p z' v
 have hη:=C.hη; have hX:=P.exponent_pos; have hy:0 ≤ σℓ:=by linarith
 obtain ⟨Q',gQ⟩:= Vow.rent_x fκ (w:=0) (Q:=0) (fun X D _ _=>Vow.Medal.zeroT) le_rfl c0 hy r₀ hη p (L.timer z' v).slope (fun i=> by change 0+_≤ (1:ℝ); rw [zero_add,pow_zero,mul_one]; exact C.still) (L₁:=0) (fun i=> by simp [tallB]) c1 C.degree (show (1/2:ℝ)<1 by norm_num) (mul_pos (by norm_num) C.hγ) (by rw [pow_zero,mul_one,add_zero,← mul_assoc,mul_inv_cancel₀ (by linarith [(L.timer z' v).slope]),one_mul]; exact C.covers) -- orientation
 have hv(i):tallB (spanD · (urnL (sℓ z' u)) 0) P.B (σH) i≤ cQ:=by have he:= thinX c0 (add_nonneg hy hη.le) i 0; rw [pow_zero,mul_one] at he; exact he
 refine ⟨reserveZ (P:=P) (fun X=> spanD X (urnL (sℓ z' u)) 0) _ (fun i=>glenP i p r₀ c0 (add_nonneg hy hη.le) 0) (turfK (ΩΘ z') (L.plain z' v u)) τ hv (zero_le_one.trans p) C.hη, reserveF (P:=P) _ _ Q' (fun i=> ?_) (zero_le_one.trans p) C.hη⟩
 apply le_inv_mul_iff₀ (zero_lt_one.trans_le (L.timer z' v).slope) |>.2; exact (gQ i).trans_eq (by ring)
omit L p
lemma settleEnd (F : ForceBudget n) (K : Rinse (Seat n) (Copy n)) : layerN (settleK F) K 0 = settleK F := by
 funext i D; simp only [layerN, Nat.zero_add, Finset.sum_range_one, Cadre.peg]

lemma baseLevel (P : BudgetPoint)(F : Key I → ForceBudget n)(K : Key I→ Rinse (Seat n) (Copy n))(z:Key I) : spaceSimple F K 0 z=0 ∧ spacePort P F K 0 z=budgetR (settleK (F z)) := by
 have he:spaceSimple F K 0 z=0:=by unfold spaceSimple; rw [settleEnd]; exact funext (settle0 _)
 refine ⟨he,?_⟩
 funext i; unfold spacePort spaceK spaceCells budgetR; rw [settleEnd, he, TreasuryFog.brightZero P _ i.property.1 i.property.2]
lemma totGas (A: ForceBudget n)(V:Orbit n) : hGas (flags P.threshold V.1) (hailV (flags P.threshold V.1) (settleK A) V) = beamP P (settleK A) V:=by
 let O:=flags P.threshold V.1; unfold beamP hGas Hac; symm; refine sum_subset (show highV O⊆_ from fun i p=> let h:= (mem_filter.mp p).2; mem_filter.mpr ⟨mem_univ _,h.1,h.2.1⟩) ?_
 intro j v q; by_contra y; apply q; obtain ⟨p,u⟩:= (mem_filter.mp v).2; refine mem_filter.mpr ⟨mem_univ _,p,u,fun i l w=>?_⟩
 have he:O∩i.val=∅:= disjoint_iff_inter_eq_empty.mp (Disjoint.symm w); refine y (prod_eq_zero l ?_); change settleK A i (O∩i.val) V=0; rw [he,settle0]; rfl

include L
lemma settleStay (X:Aura n)(D:Support (More n)) : Hush σ X.val (fun z=> settleK (F z) X D) := by
 intro z vz w vw p; refine sum_congr rfl fun i u=>?_ ; have ht: lordD i=X:= (mem_filter.mp u).2.1; apply (L.settleQ i).1 z vz w vw; intro i g; apply p i; rw [←ht]; exact g
lemma settleFlow (X:Aura n)(D:Support (More n))(V:Orbit n) : River (fun z=> settleK (F z) X D V) := by
 unfold settleK; simp_rw [Finset.sum_apply]; exact (tip_bank _ _ (fun i _=> (L.settleQ i).2 V)).1
lemma floods (X:Aura n) (D:Support (More n))(e:D⊆X.val)(V:Orbit n): Flood u (fun z=> (PowerSeries.coeff u (Cadre.chip (K z) (QΨ z) X D)) V):=
 Sour.Shelf.music L.figure X D e (fun i D _=>L.settleFlow i D) (fun i=>(L.visit i).2) u V
lemma layerStay (X:Aura n)(D:Support (More n))(e:D⊆X.val) : Hush σ X.val (fun z=> Θ z X D) := by
 intro z vz w vw p; unfold spaceCells layerN; exact sum_congr rfl (fun i _=> Sour.Shelf.hush L.figure X D e i (fun i D _=>L.settleStay i D) (fun i=> (L.visit i).1) z vz w vw p)
lemma layerFlow (X:Aura n)(D:Support (More n))(e:D⊆X.val) (V:Orbit n) : River (fun z=> (Θ z) X D V) := by
 unfold spaceCells layerN; simp_rw [Finset.sum_apply]; exact (tip_bank _ _ (fun i _=>(L.floods i X D e V).riv)).1
include p
lemma simpleFlow (X:Aura n)(V:Orbit n): River (fun z=>Ψg z X V) := by
 have hp:=C.hη; have hx:=P.exponent_pos; let B(z)(v:z∈hill I):=(L.rackMoney u p z v).1
 exact lore_Y (ΩΘ) P p (fun x y=> L.layerFlow u x _ (empty_subset _) y) (fun z=> urnL (sℓ z u)) (by linarith : 0≤ σH) B (fun z v=> (L.layerSuit u p z v).1) (ready_pos Palot.stern P.B (B _ roots)).le C.degree0 X V
omit p
-- at the single-Key origin, even the coefficient computation is *not* uniform-height on old Force. Compare only valid D.
lemma cutOrigin (X:Aura n)(D:Support (More n))(e:D⊆X.val): Θ 0 X D= (QΨ (0 : Key I)) X D:= by
 funext V; unfold spaceCells layerN; rw [Finset.sum_apply, sum_eq_single_of_mem 0 (mem_range.mpr (Nat.zero_lt_succ u)),Cadre.peg]
 exact fun b _ v=>(L.floods b X D e V).grow (Nat.pos_of_ne_zero v)

lemma plainOrigin : ΩΘ 0=0:= funext fun X=> (L.cutOrigin u X ∅ (empty_subset _)).trans (settle0 ..)
lemma setup : Dθ 0=0 ∧ ΔΚ 0=0:=by
 let hQ:= L.plainOrigin u
 refine ⟨?_,?_⟩
 · funext i x; unfold spaceD spaceG Ione.cast_E; rw [hQ,TreasuryFog.costBright]; simp
 funext i; let d:= extraD i
 unfold placePort; rw [(baseLevel P F K 0).2, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]; unfold spacePort spaceK budgetR
 rw [hQ,TreasuryFog.brightZero P _ i.property.1 i.property.2, L.cutOrigin u _ _ i.property.2]
include p
lemma spaceCash (z':Key I)(V:Orbit n)(e:FleetS P.threshold V.1)(v:z'∈hill I): hGas (flags P.threshold V.1) (hailV (flags P.threshold V.1) (Θ z') V)= exp (exponentL P (Dθ z') V.1)*fueled P (F z'+ΔΚ z') V:=by
 let O:=flags P.threshold V.1; let G:= Θ z'
 have ht: hailV O G V= keyL P G (ΩΘ z') V:=by
    funext i; unfold keyL; split; next h=> unfold hailV; rw [disjoint_iff_inter_eq_empty.mp h]; rfl
    next h=>rfl
 have h':0 ≤ σℓ:=by have hz:=C.hη; have ht:=P.exponent_pos; linarith
 have hB:= (L.layerSuit u p z' v); have hr:= Vow.polyH G (0:Cusp n) V _ (L.rackMoney u p z' v).1 p hB.1 (add_nonneg h' C.hη.le) e (exponentL P (Dθ z') V.1) (by rw [prizes0,add_zero]; exact Ione.ocean P (Ψg z') τ (Bake.turfK _ (L.plain z' v u)) V)
 change Palot.hGas O (hailV O G V)= _; rw [ht,hr]; exact congrArg (fun v=>_* v) (TreasuryFog.budgetDisplace V (Ψk z') e (F z') (spacePort P F K 0 z') (fun i v=>by
    rw [(baseLevel P F K z').2, TreasuryFog.eachFace _ _ i _ inter_subset_right] -- tune params
    exact Finset.not_disjoint_iff_nonempty_inter.mp (fun h=>v h.symm)))
end Furrow
end TreasuryFog
end YM.CF.Vow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.simpleFlow
#print axioms YM.CF.Vow.TreasuryFog.Furrow.setup
#print axioms YM.CF.Vow.TreasuryFog.Furrow.lowLens
#print axioms YM.CF.Vow.TreasuryFog.Furrow.spaceCash
