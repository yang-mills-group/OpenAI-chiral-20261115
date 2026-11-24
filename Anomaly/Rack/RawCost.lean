import Anomaly.Rack.Huddle
/-!
Produce and price REAL Key perturbations of this Gram. No old Keys
required at this stage. `singleReceipt` first E landing at unchanged R,
support exponent slack retained for later operations. Cost of *combined*
E and F perturbations from all Mark input, including Hush, first and higher
powers. This is BEFORE renormalizing for recurrence with Axon
(so, e.g., no assertion that replacing this Reg in such a manipulation
can leave the Force fixed!).
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Lor Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate


namespace LocalLimit
namespace Preparation
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell QuadClock

open Buffered Vow Stax Sault Exa Afterglow Tapestry Girt
variable {P:Preparation} {ℓ:ℕ}(Y : Course P (VolumeCape.Dream.Nimbus ℓ))
variable {k0 i k s:ℕ}{G d μ K:ℝ→ℝ}
local notation "Θω"=> hat P.R.L P.x s
local notation "N"=> P.Ctor (Y.ir i) s
local notation "Kmy"=> (Y.voyage i).CapeT s
local notation "Rs"=>RootBook Y i k s
variable {J:Type}[LinearOrder J][Fintype J]
variable (σ:J→ Site (P.Ctor (Y.ir i) s))(t:ReadyBench Y (hat P.R.L P.x s) (G (hat P.R.L P.x s)) (d (hat P.R.L P.x s)) (μ (hat P.R.L P.x s)) (K (hat P.R.L P.x s)) (RootBook Y i k s) k0)
variable (p:Force_M ((RootBook Y i k s)).p.B (Cube.node ∘ σ) k0)
local notation "Ao"=> Orbit N
local notation "H"=> P.h
local notation "Npers"=> P.J.n

-- issue for a Mark portfolio at these same X(k,s); use disjoint pips
structure Quill (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(s i k:ℕ)(Xo:J→Site (P.Ctor (Y.ir i) s)) (Q:J→ Mark (P.Ctor (Y.ir i) s))(V : J→ phy (P.Ctor (Y.ir i) s))(A:J→Aura (P.Ctor (Y.ir i) s)) -- contours cores not need nonempty? use Support
    (Kc: Key J→RegBudget (P.Ctor (Y.ir i) s))(Wc:Key J → ForceBudget (P.Ctor (Y.ir i) s))(u d e f:ℝ) : Prop where
  -- Charter not output of Arc. paid without orientations.
  notice : Notice Xo Kc Wc
  spine : let R:=RootBook Y i k s; let Ka:= (Y.voyage i).CapeT s; ∀ j, Contact Ka (A j).val (Q j) (V j)
  tips : ∀ j, let R':=RootBook Y i k s; let P':=R'.p; let Δ:=P'.B; let i0:=Cube.node (Xo j); let E:=νTip Kc j; (∀ X:Scree.Hub _,X.val.1≠ i0 ∨ ¬ grooveB 24 P' i0⊆ X.val.2 → E X=0) ∧
    (∃ r:Scree.Hub _→ℝ,(∀ X,PressB P' X (E X) P.h (r X))∧(∑ X:Scree.Hub _, Ione.massPlus P' (7/(Δ:ℝ)) X.val.2 (r X))≤ e)∧
    (∃ r:Scree.Hub _→ℝ,(∀ X,PressB (pStar P') X (E X) P.h (r X))∧(∑ X:Scree.Hub _, Ione.massPlus (pStar P') (7/(Δ:ℝ)) X.val.2 (r X))≤f)
  wallet : let R:=RootBook Y i k s; ∀ z:Key J, (∀ i,‖z i‖ ≤2) → IncX primeU (Kc z) R.p P.h u ∧ Dark primeU (Wc z) R.p P.h d
  marked : let R:=RootBook Y i k s; let Ka:= (Y.voyage i).CapeT s; let D:=fun z=>denZ (color_b R R.beta (R.F+Kc z) R.slip (R.K+Wc z) R.v) P.U Ka; ∀ (L:List J), ψS (Cube.node∘Xo) L → L.Pairwise (fun i j=>Disjoint (A i).val (A j).val) → ∀ v : Orbit (P.Ctor (Y.ir i) s), Rue.FleetS R.p.threshold v.1 →
    tipI (fun z=> D z v) L=acts ((L.map fun i=>V i v).prod) (denZ R P.U Ka v)

-- strengthen endK conclusion simply call previous method.
variable {h g e f_ :ℝ}
local notation "slots"=> P.Ctor (Y.ir i) s
local notation "cap2"=> RootBook Y i k s
local notation "Υ"=> (Cube.node ∘ σ)
variable (A:J→ Mark (P.Ctor (Y.ir i) s))(B:J→phy (P.Ctor (Y.ir i) s))
variable (Zq : J→ Aura (P.Ctor (Y.ir i) s))
variable (v:∀ j, Contact ((Y.voyage i).CapeT s) (Zq j).val (A j) (B j))(hZ:∀ j:J, ∃ F:Sour.Bag (P.Ctor (Y.ir i) s),Swell.Nest P.U (RootBook Y i k s) ((Y.voyage i).CapeT s) P.J.n 24 ((Cube.node ∘ σ) j) P.h (rScale ((RootBook Y i k s)).p) (B j) F (G (hat P.R.L P.x s)) (d (hat P.R.L P.x s)))

abbrev winL (k0:ℕ)(D μ: ℝ→ℝ)(x:ℝ):= (k0:ℝ)*(2*putTip 2 D x)+ wakeL μ x
lemma win_P (Q : Patch)(k0:ℕ) (U V:ℝ→ℝ)(hU:Quench Q U)(hV:Quench Q V): Quench Q (winL k0 U V):=( ( (wakePrice k0 U Q hU).2.2.1 |>.manyF (2:ℝ)).manyF _).addL ((wakePrice k0 V Q hV).2.2.2.2)

include t p v hZ
lemma pricedQuill(s':s<Y.uv k): ∃ (K: Key J→ RegBudget (P.Ctor (Y.ir i) s))(W: Key J → ForceBudget (P.Ctor (Y.ir i) s)),
    Quill Y s i k σ A B Zq K W (winL k0 d μ Θω) (wakeK k0 μ Θω) (putTip 2 d Θω) (putTip 3 d Θω) := by
  obtain ⟨r,Z,t',uR⟩:=rent_old _ _ _ _ _ _ t.data.1 t.data.2 (zero_le_one.trans P.height)
  choose V l using hZ
  let y(x:J):=grooveB 24 (Rs).p ((Υ) x)
  let g := thresholdOcclus t.fence
  obtain ⟨hh,k1,o1,v1,j_,D0⟩:=t.heads
  have ht (j): Barrage (Rs).p Npers (y j) H (V j) ((Rs).p.supportExponent+8/((Rs).p.B:ℝ)) (G Θω) (d Θω):=by rw [j_]; exact (l j).pouch
  have hr (i:Seat N) : tallB (Cadre.roofL r 1) (Rs).p.B ((Rs).p.supportExponent+1/2) i ≤ chi_f 6 * K Θω := by
    have hv:=uR i; rw [o1] at hv; exact hv
  obtain ⟨a,b,E,D_,L,T⟩:= IssueRack t.fence ht (σ:=Υ) (fun i=> halo_subset _ _ (mem_singleton_self _)) p D0 (zero_le_one.trans P.height) r Z hr
  let U : Ids N:= Classical.arbitrary _
  let Fy (j:J):= singleReceipt V a b E U j ((Υ) j)
  let kappa:= zealPitch V a b E
  let a0:= Fintype.card J+1
  let Rz:= RootBook Y i k s
  let X:= hat P.R.L P.x s
  let Δ:= Rz.p
  let b':ℝ:= Δ.B
  let ε:ℝ:= BScale.runway Θω
  let X0:=putTip 2 d X; let X1:=putTip 3 d X
  have hb: ε=b'⁻¹:=by unfold ε b' BScale.runway; rw [← hh]
  have hD: 0<ε:= lt_of_lt_of_eq (inv_pos.mpr (Nat.cast_pos.mpr Δ.B_pos)) hb.symm
  let E' := lensD (P:=Rz.p) Rz.K kappa a0 U; let W':= lensPort (P:=Rz.p) Rz.K kappa a0
  let V' := awake Υ E' Fy; let Y' := bustle Υ W'
  have h0(j)(X:Scree.Hub (P.Ctor (Y.ir i) s)) : X.val.1≠(Υ) j → Fy j X=0:=by intro v; exact Vow.TreasuryFog.station _ _ _ E U _ j X v
  have hE : g.η=BScale.runway X:= hb.symm
  have hc:reserveT Δ.power Δ.order Δ.B ε*|d Θω|= X0:=by unfold X0 putTip; rw [show Δ.order=_ from o1,show Δ.power= _ from v1,show Δ.B= _ from hh]
  have he(j):voyageB (b j) Δ.B (Δ.supportExponent+7/b'+ε) ≤ |d Θω| := by rw [hb,show Δ.supportExponent+7/b'+b'⁻¹=Δ.supportExponent+8/b' from by ring]; exact (L j).2.trans (le_abs_self _)
  have huv(j)(x):0 ≤ b j x:=by obtain ⟨_,q,_⟩:=(E j x).forms; exact q.price
  let fT(j):= formalCost ((Υ) j) (b j) Δ
  have budget(j): (∑ i:Scree.Hub N, Ione.massPlus Δ (7/b') i.val.2 (fT j i)) ≤ X0:= hc ▸ (birth_tally ((Υ) j) (b j) Δ ε _ hD (huv j) (he j))
  have wage_p :0 ≤ putTip 2 d X := by unfold putTip; change 0≤ reserveT _ _ _ ε*_ ; unfold reserveT coin_n stilK; positivity
  have Hpos:0 ≤ P.h:= zero_le_one.trans P.height
  have hu(j)(x:Scree.Hub N): PressB Δ x (Fy j x) H (fT j x):= heated V a b E U _ j D0 Hpos _
  have hz(j):IncX primeU (Fy j) Rz.p H X0 := by
    refine ⟨⟨fT j, hu j, fun i=> le_trans (sum_le_sum (fun x _=>?_)) (budget j)⟩,fun _ t=>False.elim t⟩
    have hc : 0 ≤ fT j x:= (Taxi.eraF _ _ (hu j x) Hpos 1 (ping_f Δ x.val.2)).grade
    split_ifs
    · change Real.exp (_ * (coverNumber Δ.B x.val.2:ℝ)) * _ ≤ Real.exp ((Δ.supportExponent+7/b')*(coverNumber Δ.B x.val.2:ℝ))*_
      exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by unfold b'; positivity)) (by positivity))) hc
    exact mul_nonneg (Real.exp_pos _).le hc
  obtain ⟨Q,M⟩:=fleshNotes Rz σ Npers V g (Υ) kappa r T U a0 P.height rfl (E:=Fy) (fun j X v=> by have hp:X.val.1=(Υ) j:=Classical.not_not.mp (mt (h0 j X) v); rw [← hp]; exact X.property)
  refine ⟨V',Y',Q,v,?_,?_,?_⟩
  · intro j R' B' K i0 p'; rw [show p'=Fy j from (M j).1]; refine ⟨fun X t=>t.elim (h0 j X) (fun t=> offRoot V a b E U _ j _ (fun X v=> (D_ j X v).1) X t), ⟨fT j, hu j,budget j⟩,?_⟩ -- need braces second grouping.
    refine ⟨formalCost ((Υ) j) (b j) (pStar Δ),birth_Star V a b E U _ j D0 Hpos, le_trans (birth_tally ((Υ) j) (b j) (pStar Δ) ε _ hD (huv j) (he j)) ?_⟩
    apply le_of_eq; change reserveT 3 Δ.order Δ.B ε * _= _; unfold putTip; rw [show Δ.B= _ from hh,show Δ.order= _ from o1]
  · intro _ z w; have h0:= eraTender Rz Npers V g (Υ) kappa r T U a0 k0 P.height hz h0 p t.debt wage_p z w -- tune
    have he:yσE Δ g=wakeE μ X:=by unfold wakeE yσE dollarT; change reserveT Δ.power Δ.order Δ.B g.η * (μ X*(1-degreePrice _ _ g.η)⁻¹) = _; rw [hE, show Δ.B=_ from hh,show Δ.order=_ from o1,show Δ.power=_ from v1, pow_zero, mul_one]; try rfl
    have hp:Real.exp (3*(k0:ℝ))* yσF Δ g=wakeK k0 μ X:=by
      simp_rw [wakeK, yσF, hE,show Δ.B=_ from hh,show Δ.order= _ from o1,show Δ.power= _ from v1, show g.κ=1 from rfl, inv_one,one_mul]; rfl
    refine ⟨?_,hp ▸ h0.2⟩
    have hv:= h0.1
    rw [show yσE (Rz.p) g=_ from he,hE, show Rz.p.B = _ from hh] at hv
    exact hv
  intro _ _ _ L W D v' t'
  have hlen:L.length≤ a0:= (List.Nodup.length_le_card (uS_b _ W)).trans (Nat.le_add_right ..)
  refine endVector P.U Rz Kmy Npers B A (fun i=> (Zq i).val) V g (Υ) kappa r T U a0 L W hlen D v P.height l (by unfold a0; omega) v' t' ((projects_here Y i k s v').1)
    (fun j=> SpanTip_at V a b E U _ j (fun X v=> (D_ j X (fun w=> v (w (halo_subset _ _ (mem_singleton_self _))))).1)) -- rename D vs layouts; need root ?_.
end Preparation
end LocalLimit
end YM.CF.Py.Rate
