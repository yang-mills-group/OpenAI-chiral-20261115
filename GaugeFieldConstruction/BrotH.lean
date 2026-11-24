import GaugeFieldConstruction.Alundra
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry 
section
variable {n:Side}{α β I γ L:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β]
variable {S:α→Support (More n)}{z:β → Force n}(σ:I→Seat n)
-- Capsule carries Region(X) & declared halos via certified.Born Reg partners.Label monotonic.Authority. Input always any rooted z (includes label κ v pricing);
-- if consumes no packs still returns R symbol (may use p barrier by ozone.Dpole restrict option). If mode force=true, force-only mask independent V.Plate.
structure Grotto (I:Type) (S:α→Support (More n))(z:β→ Force n) where
    anchor : Hub n
    needs : ℕ
    range : needs ≤2
    flag :Bool
    fromR : Heart anchor S needs → List I
    termR : Heart anchor S needs → InkD n
    fromB : (y:Heart anchor S needs) → Finset β → List I
    termB : (y:Heart anchor S needs) → Finset β→ Copy n

variable (A:Grotto I S z)
local notation "L0"=> Heart A.anchor S A.needs
local notation "Tθ"=> Legist A.anchor S A.needs
local notation "K0" i:max=> Base z (Legist A.anchor S A.needs i) A.flag
local notation "T0" i:max=> roost z (Legist A.anchor S A.needs i) A.flag
namespace Grotto
def Rinc : dues I (Hub n) → InkD n:= ∑ i:L0, clipK σ (Tθ i) (A.fromR i) (if A.flag then 0 else A.termR i)
def Kinc : dues I (Force n) → Copy n :=∑ i:L0, ∑ P:K0 i, clipK σ ((T0 i) P) (A.fromB i P.val) (A.termB i P.val)
-- All fiscal
variable (r:ℝ)(V:α→ℝ)(B:β→ℝ)
def exp_R : dues I (Hub n)→ℝ:=∑ i:L0, clipK σ (Tθ i) (A.fromR i) (r * ∏ j:Fin A.needs,V (i.val j))
def exp_Y :dues I (Force n)→ℝ:=∑ i:L0,∑ P:K0 i, clipK σ ((T0 i) P) (A.fromB i P.val) ((r*∏ j:Fin A.needs,V (i.val j)) * ∏ j∈P.val,B j)
structure Ri (p:BudgetPoint)(q h:ℝ):Prop where
    rent(x:Heart A.anchor S A.needs)(t:ψS σ (A.fromR x)) (e:A.flag=false): PitR p h q ((A.fromR x).toFinset,Legist A.anchor S A.needs x) (A.termR x) (r*∏ j:Fin A.needs,V (x.val j))
    keep(x:Heart A.anchor S A.needs)(t:ψS σ (A.fromR x)) (e:A.flag=false)(u:A.termR x≠0): Pub σ (A.fromR x).toFinset (Legist A.anchor S A.needs x).val.2
structure Yi (p:BudgetPoint)(q h:ℝ)(k:ℕ):Prop where
    rent(x:Heart A.anchor S A.needs)(P:Base z (Legist A.anchor S A.needs x) A.flag)(t:ψS σ (A.fromB x P.val)): PitF p h q k ((A.fromB x P.val).toFinset,roost z (Legist A.anchor S A.needs x) A.flag P) (A.termB x P.val) ((r*∏ j:Fin A.needs,V (x.val j))*∏ j∈P.val,B j)
    keep(x:Heart A.anchor S A.needs)(P:Base z (Legist A.anchor S A.needs x) A.flag)(t:ψS σ (A.fromB x P.val))(h:A.termB x P.val≠0): Pub σ (A.fromB x P.val).toFinset (plateI (roost z (Legist A.anchor S A.needs x) A.flag) P)
-- Γ Memory.Pitting.Recurse
structure Pits (p:BudgetPoint)(q h:ℝ)(k:ℕ):Prop where
   lease : Ri σ A r V p q h
   packs : Yi σ A r V B p q h k
   clarity : 0≤ r
variable {p:BudgetPoint}{q h:ℝ}{k:ℕ}
lemma Ri.ready (k: Ri σ A r V p q h)(ht:0≤r)(u:0≤V)(s:0<q): BillX p σ h q (exp_R σ A r V) (Rinc σ A):=by
    apply ReefX.registry_sum (T:=PitR p h q) σ (fun i:Hub n=> i.val.2) ReefxR -- arg tune
    intros i hi; have ht':0≤ r* ∏ j:Fin A.needs,V (i.val j):=mul_nonneg ht (prod_nonneg fun _ _=> u _)
    apply allot_sum (T':= PitR (n:=n) p h q) _ _ _ _ _ ReefxR _ ht'
    · intro t; split; next b=> exact Medal.big (F:=oV (0:InkD n)) (show Medal p _ ∅ (oV (0:InkD n)) h 0 from Medal.zeroT) (div_nonneg ht' (pow_pos s _|>.le)) -- if cond true
      exact k.rent i t (by simpa using ‹¬A.flag=true›)
    intro t H; split at H; next e=> exact False.elim (H rfl)
    apply k.keep _ t _ H; simpa using ‹¬A.flag=true›
lemma Yi.ready (m:Yi σ A r V B p q h k)(u:0≤V)(v:0≤B)(ht:0≤r):BillF p σ h q k (exp_Y σ A r V B) (Kinc σ A):=by
    apply ReefX.registry_sum (T:=PitF (n:=n) p h q k) σ (fun i:Force n=> i.val.1.val.2) (ReefxF k)
    intro i x; apply ReefX.registry_sum (T:=PitF (n:=n) p h q k) σ _ (ReefxF k)
    intro y e; apply allot_sum (T':=PitF (n:=n) p h q k) _ _ _ _ _ (ReefxF _) _ (mul_nonneg (mul_nonneg ht (prod_nonneg fun _ _=>u _)) (prod_nonneg fun _ _=>v _)) (m.rent _ _) (m.keep _ _)
local notation "r∗"=>fun k:Hub n=> k.val.2
local notation "k∗"=> fun x:Force n=> x.val.1.val.2
variable (y:Seat n){Ω a η:ℝ}{b:ℕ}{L:List (Site (More n))}
variable (u:0≤V)(v:0≤B)(ht:0≤r)(l: Scales b a η L)
local notation "PZ"=>RedB b a η L
local notation "ΩΠ"=>ColdB b a η L
local notation "G0"=>PZ A.anchor.val.2 * ridg b A.anchor.val.2^3
local notation "Δπ"=>η⁻¹*respite b (a+2*ζd) η L (plateI z) B A.anchor.val.1 y
local notation "Γπ"=>η⁻¹*respite b (a+6*ζd) η L S V A.anchor.val.1 y
local notation "gπ"=> Cube_M b* Ω
local notation "Mπ"=> windPulse b A.anchor.val.1 y
variable (HP : ∀ y:Site (More n),postG S V (RedB b a η L) y≤ Ω)(HV:∀ y:Site (More n),postG (plateI z) B (ColdB b a η L) y≤ Ω)(t:Cube_M b*Ω≤1)(g:0≤Ω)
include u ht HP l t g
lemma exp_r : pointX (r∗) (A.exp_R σ r V) PZ y≤ r* (G0 * (Mπ*(if A.needs=0 then 1 else gπ)+2*Γπ)):=by
 unfold exp_R; rw [pointX_sum]
 apply le_trans _ (mul_le_mul_of_nonneg_left (stroll_site A.anchor y S V u l g HP t A.needs A.range) ht); rw[mul_sum]; apply sum_le_sum; intro i v
 refine (allot_le _ _ _ _ _ (mul_nonneg ht (prod_nonneg fun j _=> u _)) _ (fun i=>Temp_p ..|>.le) _).trans_eq ?_; unfold Legist lengthQ; split_ifs with h -- tune
 · exact mul_assoc ..
 exact (mul_zero _).symm
include HV v
lemma exp_f :pointX (k∗) (A.exp_Y σ r V B) ΩΠ y≤ r*(G0 *((Mπ*gπ+2*Γπ)+Δπ)) :=by
 unfold exp_Y; rw [pointX_sum]; simp_rw [pointX_sum]
 apply le_trans _ (mul_le_mul_of_nonneg_left (crewTouch A.anchor y A.flag S V u z B v l g HV HP t _ A.range) ht); simp_rw[mul_sum]; apply sum_le_sum; intro i t; apply sum_le_sum; intro j y
 apply (allot_le _ _ _ _ _ (mul_nonneg (mul_nonneg ht (prod_nonneg fun _ _=>u _)) (prod_nonneg fun _ _=>v _)) _ (fun _=>Temp_p ..|>.le) _).trans_eq
 split_ifs <;> first| (exact Eq.symm (mul_zero _)) | (ring)
end Grotto
end
end YM.CF.Scree.Ing
end
