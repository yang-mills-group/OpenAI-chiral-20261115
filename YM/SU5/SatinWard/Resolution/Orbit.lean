import YM.SU5.SatinWard.Resolution.Quarterly
import SatinThinConvoy
import YM.SU5.SatinWard.Resolution.Inning
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A:ℝ)
open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop

open ResolutionFrame Vow.TreasuryFog Swell
open ResolutionFrame Rue Advance Tapestry
variable {I:Type}[Fintype I][LinearOrder I]{v z:ℕ}
attribute [-instance] instDecidableEqLex
local notation "WK"=> Booth I η
local notation "Θ"=> P.Ctor (Y.ir i) (s+1)
local notation "εμ"=> Primary ι η
local notation "Φ"=> F.colors (P.Ctor (Y.ir i) s)
local notation "Xp"=> RootBook Y i k s
local notation "Xf"=> RootBook Y i k (s+1)
local notation "G★"=> Vale.apt (Y.ir i) P.block P.R.L s
-- lean abbrev turnover step receipts. ensure proof printed. preserve all Step assumptions to reuse for grafts later.
variable [DecidableEq η](D:ArmorK)
set_option maxHeartbeats 240000
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Pressure.Worth Worth.Pays Graph
-- all annual payments. `Invoices` even in integrating on that partition, with q^{-1} radius when earned. Normed.Check.
-- Linear receipt. No assumption on germ laws here.
variable {g:ℕ}{n:Side} {a0:ℕ}{d':ℕ}
variable {G:Sept (Primary ι η) (P.Ctor (Y.ir i) g) (P.Ctor (Y.ir i) v)} {B:∀ e:ℕ,Sept (Primary ι η) (P.Ctor (Y.ir i) e) (P.Ctor (Y.ir i) v)}{R:ℕ→ Reflow ι η}
variable (h':Examiners Y C H A m F a0 g v i k G R B)
local notation "T"=> P.R.L
local notation "w" => sprintCost T
abbrev topBeam {A B:Side}(P: Sept (Primary ι η) A B)(x:Site A):= ShapeLab.columns (fun i:ι=>P (.inl i) x)
variable (M:Sept (Primary ι η) (P.Ctor (Y.ir i) (s+1)) n) (D':Reflow ι η)
lemma saleC {H:Type*}[AddCommGroup H][Module ℝ H](L:Side)(M:Primary ι η→H)(j:ι): (∑i:Primary ι η,D'.sales L i (.inl j) • M i)=ShapeLab.columns (fun i:ι=> M (.inl i)) (D'.U.symm (ShapeLab.leg j)):=by change (∑i:ι⊕η,_)=_; rw [Fintype.sum_sum_type, ShapeLab.cols_apply]; simp only [Reflow.sales,zero_smul,sum_const_zero,add_zero]
lemma saleH {H:Type*}[AddCommGroup H][Module ℝ H](L:Side)(M:Primary ι η → H)(j:η): (∑i:Primary ι η,D'.sales L i (.inr j) • M i)= sprintCost L • (M (.inr j)+ ShapeLab.columns (fun i:ι=> M (.inl i)) (D'.leaks j)):=by change (∑i:ι⊕η,_)=_; rw [Fintype.sum_sum_type, ShapeLab.cols_apply]; simp only [Reflow.sales,ite_smul,zero_smul,mul_smul,←smul_sum,sum_ite_eq',mem_univ,if_true,smul_add]; abel
lemma craneBeam (M:Sept (Primary ι η) (P.Ctor (Y.ir i) (s+1)) (P.Ctor (Y.ir i) v))(j:Coords ι)(x:Site (P.Ctor (Y.ir i) s)): topBeam (cranePrice Y M D') x j=topBeam M (heel G★ x) (D'.U.symm j):=by
 unfold topBeam; let L':=(topBeam M (heel G★ x)).comp D'.U.symm.toLinearMap; have ht(i':ι):cranePrice Y M D' (.inl i') x=L' (ShapeLab.leg i'):=saleC D' P.R.L (fun i'=>M i' (heel G★ x)) i'; simp_rw [ht]; rw [ShapeLab.columns_map]; rfl

variable (u₀:a0≤ s)(x:Site (P.Ctor (Y.ir i) s))
include h' u₀ in
lemma carryBook (d:ℕ)(u:s+d≤g)(y:Coords ι)(z:η) : let h0:= upRoot Y i (Nat.le_add_right s d) x
  topBeam (B s) x y=topBeam (B (s+d)) h0 (slip R s d y) ∧
  B s (.inr z) x=w^d • (B (s+d) (.inr z) h0 + topBeam (B (s+d)) h0 (jetlag T R s d z)) := by
 intro y'
 induction d with
 | zero=>
    change _= topBeam (B s) y' y∧ B s _ _=_ • (B s _ _+ topBeam (B s) y' (0: Coords ι)); rw [show y'= x from climbing_refl ..]; simp
 | succ d ih=>
   let G':=Vale.apt (Y.ir i) P.block P.R.L (s+d); let h0:= upRoot Y i (Nat.le_add_right s d) x
   have hp(u: s+d ≤ g):=ih u; obtain ⟨h,q⟩:= hp (by omega)
   have hb: B (s+d)= _:= (h'.grow (s+d) (by omega) (by omega)).1
   have hx:y'=heel G' h0:=climbing_succ _ _ _
   let Z:= B (s+d+1); let U:= topBeam Z (heel G' h0)
   constructor
   · calc _ = topBeam (B (s+d)) h0 (slip R s d y):=h
          _ = U ((R (s+d)).U.symm (slip R s d y)):=by rw [hb]; exact craneBeam Y _ _ _ _
          _ =_:=by rw [hx]; rfl
   calc _=w^d • (B (s+d) (.inr z) h0 + topBeam (B (s+d)) h0 (jetlag T R s d z)):= q
        _=w^d • ( w • (Z (.inr z) (heel G' h0)+U ((R (s+d)).leaks z)) + U ((R (s+d)).U.symm (jetlag T R s d z))):=by
             rw [hb,craneBeam]; apply congrArg (fun z':Mark (P.Ctor (Y.ir i) v)=> w^d • z'); apply congrArg (· + _); exact saleH (R (s+d)) _ (fun z=>Z z (heel G' h0)) z
        _=_:=by rw [hx,jetlag_v,pow_succ,mul_smul]; change _=w^d • ( w • ( Z (.inr z) _ + U _)); rw [map_add,map_smul]; simp only [smul_add, smul_inv_smul₀ (sprint_pos T).ne']; rw [add_assoc]

-- lower relative to fixed-base
variable (u:s≤g)
include h' u₀ u
local notation "y★"=> upRoot Y i u x
lemma mainBeam [Nonempty η] (z:Coords ι): topBeam (B s) x z= topBeam G y★ (slip R s (g-s) z):=by
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le u
 rw [Nat.add_sub_cancel_left,←h'.first]
 -- carryBook requires η input; possible η=PEmpty. can't. fix split estimates or assume η Nonempty
 exact (carryBook Y m F C H A h' u₀ x d le_rfl z (Classical.arbitrary η)).1
lemma carryLag (z:η) : let g0:=B s (.inr z) x; let l:=g-s; let V0:=topBeam G y★
                g0 + topBeam (B s) x (jetlag T R a0 (s-a0) z)= w^l • (G (.inr z) y★ + V0 (jetlag T R a0 (g-a0) z)) := by
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le u; obtain ⟨f,rfl⟩:=Nat.exists_eq_add_of_le u₀; dsimp only; rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left, show a0+f+d-a0=f+d from by omega]; let p:=carryBook Y m F C H A h' u₀ x d le_rfl (jetlag T R a0 f z) z; rw [← h'.first, p.1, p.2, jetlag_stop, map_add,map_smul]; simp only [←add_assoc,smul_add, inv_pow,smul_inv_smul₀ (pow_pos (sprint_pos T) d).ne'] -- inspect

-- graft formulas
omit h' u₀ u
local notation "Graft"=> Announcement ι η
lemma ledgerAt (M:Sept (Announcement ι η) (P.Ctor (Y.ir i) s) (P.Ctor (Y.ir i) s))(V:Sept (Announcement ι η) (P.Ctor (Y.ir i) (s+1)) (P.Ctor (Y.ir i) (s+1)))(U':Reflow ι (ι⊕η))(y:Site (P.Ctor (Y.ir i) s)) : let H' := composeGraft (k:=k) Y M V U'
   (∀ z:Coords ι, topBeam H' y z= topBeam V (heel G★ y) (U'.U.symm z)) ∧
   ∀ j:ι,H' (escrow j) y=(1/2:ℝ) • (topBeam H' y (ShapeLab.leg j) - ascender Y s i k (M (.inl j) y)):=by
 let H1(a:Graft):= V a (heel G★ y); let H2(a:ι):=ascender Y s i k (M (.inl a) y); let H3:=batchBy H1 H2; intro V'; let Z:=(topBeam V (heel G★ y)).comp U'.U.symm.toLinearMap
 have p(j:Graft): V' j y =∑ k:Graft, incrementShip U' T k j • H3 k:=by
    change (∑ u:Graft, _ • (graftPortrait _ M V u y))= _; refine sum_congr rfl fun i _=>?_ ; rcases i with i|(i|i)<;> rfl
 have h(j:ι): V' (.inl j) y= Z (ShapeLab.leg j):=by rw [p]; change (∑ i:Graft, U'.sales T i _ • _) = _; exact (unaffected U' T H1 H2 _ (show familySpot (.inl j:Graft)=false from rfl)).trans (saleC _ _ H1 j)
 refine ⟨fun z=> ?_,fun j=>?_⟩
 · unfold topBeam; simp_rw [h]; rw [ShapeLab.columns_map]; rfl
 rw [p, topBeam, ShapeLab.columns_one,h]; rw [show Z _ = _ from (saleC U' T H1 j).symm, smul_sub]; exact sailCoupon ..
#print axioms carryLag
#print axioms ledgerAt
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
