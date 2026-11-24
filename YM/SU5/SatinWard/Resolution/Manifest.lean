import YM.SU5.SatinWard.Resolution.Orbit
import YM.SU5.SatinWard.Resolution.Compass
import YM.SU5.SatinWard.Resolution.Crimp
import YM.SU5.Reconstruction.Oblique.TiltAxis
import YM.SU5.Reconstruction.Oblique.Consulting
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
open Again Tapestry Tower.SlabMark Tower.Tilted VelourBoard
open StressFlux AnalyticBridge.VerifiedReset Ione.Clock
-- general `Banner` reads: (i independent charge= p revenue) ANY skate. support&regularity qualified when constructed later. these are exact Marks even off boot widths.
namespace Shrine
-- θ in place; single step scalar comparator; local "ult" formula may mix Booleans.Sharp marks. Two budgets one attendee at time.
local notation "ι₀" => Wage4
local notation "L★"=> P.R.L
local notation "Ω★" i:max=> side Y i
local notation "v★" i:max => P.Ctor (Y.ir i)
local notation "H★"=> (ι₀ ⊕ η)
local notation "W★"=> Announcement ι₀ η
local notation "w"=> sprintCost P.R.L
variable {a₀ g:ℕ}
def glowMark (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i:ℕ)(s:ℕ)(D:Skate)(x:Site (P.Ctor (Y.ir i) s)):Mark (P.Ctor (Y.ir i) s):= temple (Y.meter.a s) (node x) ((lapQ Y s) • D)
lemma glows (x:Site (side Y i s))(v:s≤Y.uv k)(z:Bool): glowMark Y i s (glazeKey z) x=paintClass Y s i k (.inl z) x:=by
 unfold glowMark; rw [← (Papal.prices_plot Y s i k v).1, point_book]; rfl
abbrev portB (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i s g:ℕ)(p:s≤g)(D X:Skate)(k:ℕ)(x:Site (side Y i s)): Mark (P.Ctor (Y.ir i) (g+1)):= let O:=upRoot Y i p x; let G:= (1/2:ℝ) • (glowMark Y i (g+1) D (upRoot Y i (show s≤g+1 from Nat.le.step p) x)-ascender Y g i k (glowMark Y i g X O)); (sprintCost P.R.L)^(g-s) • G
variable (Q Q':Coords ι₀≃ₗ[ℝ]Coords ι₀)
local notation "Τ" =>cloverFrame
variable (p:10 ≤ P.R.L.val)(h0:a₀≤g)(g0:Satin.PairIdx Y (g+1) i k) (W':Showroom Y Γ A a b d ε c C H cloverFrame Z V K W m D η a₀ g i k (fun s=>paintClass Y s i k))
variable (M:(Wage4⊕η)→Site (side Y i (g+1))→Mark (side Y i (g+1)))
local notation "v₀"=>g+1
abbrev draftK (u i k:ℕ)(Y:Course P (VolumeCape.Dream.Nimbus ℓ))(Q: Coords ι₀≃ₗ[ℝ]Coords ι₀) (M:η→ Site (side Y i u)→Mark (side Y i u)):Sept (Primary Wage4 η) (P.Ctor (Y.ir i) u) (P.Ctor (Y.ir i) u):= Gdraft Y (paintClass Y u i k) M Q
variable {K1:Reflow Wage4 (Wage4⊕η)}{R:ℕ→ Reflow Wage4 (Wage4⊕η)} {B:∀ y:ℕ,Sept (Announcement Wage4 η) (P.Ctor (Y.ir i) y) (P.Ctor (Y.ir i) (g+1))}
local notation "D★" => draftK
abbrev F1Q (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i':ℕ)(k g:ℕ) (U' U: Coords Wage4≃ₗ[ℝ]Coords Wage4)(M:(Wage4⊕η)→ Site (side Y i' (g+1)) → Mark (side Y i' (g+1)))(R:Reflow Wage4 (Wage4⊕η)):= composeGraft (s:=g) (i:=i') (k:=k) Y (D★ g i' k Y U' 0) (D★ (g+1) i' k Y U M) R
variable (F':Examiners Y C H A m cloverFrame a₀ g (g+1) i k (F1Q Y i k g Q Q' M K1) R B)
variable (q₁:Pupil Y a b d Γ ε cloverFrame g i k (paintClass Y g i k) Q)(q:Pupil Y a b d Γ ε cloverFrame (g+1) i k (paintClass Y (g+1) i k) Q')
lemma firm_point {M:η→ Site (side Y i s)→ Mark (side Y i s)} (q:Pupil Y a b d Γ ε cloverFrame s i k (paintClass Y s i k) Q) (h:s≤Y.uv k) (z:Bool) : D★ s i k Y Q M (.inl (.inl z))= glowMark Y i s (glazeKey z):=by
 let v:=plusE z; have hx:Q v=v:=q.firms (.inl z) rfl; have he:Q.symm v=v:=by apply Q.injective; rw [Q.apply_symm_apply,hx]
 change ShapeLab.columns _ (Q.symm v)=_; rw [he]; exact (ShapeLab.columns_one (paintClass Y s i k) (.inl z)).trans ((funext fun i=>glows Y i h z).symm) -- x arg order
noncomputable def multiplier : Coords ι₀→ₗ[ℝ] Skate:= { toFun:=fun z=> cloverKey (z (.inl true)) (z (.inl false)), map_add':=fun x y=>by { unfold cloverKey; simp only [Pi.add_apply,add_smul]; abel }, map_smul':=fun x y=>by simp only [cloverKey,RingHom.id_apply,smul_add,smul_smul,Pi.smul_apply,smul_eq_mul] }
lemma multiplier_p (v:Bool): multiplier (plusE v)=glazeKey v:=by cases v <;> unfold multiplier glazeKey; all_goals simp [plusE, ShapeLab.leg]
lemma multiplier_o (v:WageP): multiplier (ShapeLab.leg (.inr v))=0:=by simp [multiplier, ShapeLab.leg, ShapeLab.clover_zero]
noncomputable def glowFrame {N:Side}(p:BudgetPoint)(q:ℝ)(x:Site (More N)):Coords ι₀→ₗ[ℝ] Mark N:= (temple p x).comp (q • multiplier)
lemma glowDome (x:Site (P.Ctor (Y.ir i) s)) (q:s≤Y.uv k): ShapeLab.columns (fun j=> paintClass Y s i k j x)= glowFrame (Y.meter.a s) (lapQ Y s) (node x):=by
 rw [←ShapeLab.columns_map (glowFrame ..)]; apply congrArg ShapeLab.columns; funext j; cases j with
 | inl j=> rw [←glows Y x q]; exact congrArg (fun z=>glowMark Y i s z x) (multiplier_p j).symm
 | inr j=> change 0= temple _ _ ((lapQ Y s) • multiplier (ShapeLab.leg (.inr j))); rw [multiplier_o,smul_zero,map_zero]
lemma dispatch (x:Site (side Y i s)) (q:s ≤ Y.uv k) (U:η→ Site (side Y i s)→Mark (side Y i s)) (b:Coords ι₀): topBeam (D★ s i k Y Q U) x b= glowMark Y i s (multiplier (Q.symm b)) x:=by
 let F:= paintClass Y s i k; let G:=(glowFrame (Y.meter.a s) (lapQ Y s) (node x)).comp Q.symm.toLinearMap; unfold topBeam; have hz(i:ι₀): ShapeLab.columns F (Q.symm (ShapeLab.leg i)) x= G (ShapeLab.leg i):=by
    unfold G; rw [←glowDome Y x q]; simp only [LinearMap.comp_apply]; rw [ShapeLab.cols_apply,Finset.sum_apply,ShapeLab.cols_apply]; rfl
 change (ShapeLab.columns fun i:Wage4=> ShapeLab.columns F (Q.symm (ShapeLab.leg i)) x) b=_; simp_rw [hz]; rw [ShapeLab.columns_map]; rfl
local notation "ζv" i:max z:max => jetlag P.R.L R a₀ (i-a₀) z
local notation "G'"=>F1Q Y i k g Q Q' M K1
-- receipt. simplifies occult "half" after lower reflow.
noncomputable def rimGain (K1:Reflow Wage4 (Wage4⊕η))(Q:Coords Wage4≃ₗ[ℝ]Coords Wage4)(v:Bool)(x:Coords Wage4):Coords Wage4:= Q.symm (K1.U.symm (plusE v + (2:ℝ) • x))
include g0 q₁ F' -- used below
lemma sharpWitness (t:a₀ ≤ s)(u:s≤g)(z:Bool) (y:Site (P.Ctor (Y.ir i) s)) : let X:= (Sum.inl z:Wage4); let h:= (Sum.inl X:Wage4⊕η)
  portB Y i s g u (multiplier (rimGain K1 Q' z (ζv g h))) (glazeKey z) k y= B s (escrow X) y + topBeam (B s) y (ζv s h):=by
 intro a u'; rw [carryLag Y m _ C H A F' t y u]
 let x:=upRoot Y i u y; let X':= heel (Vale.apt (Y.ir i) P.block P.R.L g) x
 let V' := D★ (g+1) i k Y Q' M; let M' := D★ g i k Y Q (0:(Wage4⊕η)→Site (side Y i g)→ Mark (side Y i g)); let e:=ledgerAt (k:=k) Y M' V' K1 x
 change w^_ • ((1/2:ℝ) • (glowMark Y i (g+1) _ (upRoot Y i (by omega : s≤g+1) y) - _))= w^_ • ( (G') (escrow a) x + (topBeam G' x) _); apply congrArg (fun v:Mark (side Y i (g+1))=> w^(g-s) • v)
 rw [show (G') (escrow a) x=(1/2:ℝ) • (topBeam G' x (ShapeLab.leg a)-ascender Y g i k (M' (.inl a) x)) from e.2 a, show (upRoot Y i (by omega : s≤g+1) y)=X' from climbing_succ _ _ u]; let A':= ζv g u'
 rw [show M' (.inl a) x = glowMark Y i g (glazeKey z) x from congrFun (firm_point Y Γ Q q₁ ((Nat.le_succ g).trans g0.2.le) z) x] -- proof tune
 have ht(b:Coords ι₀):topBeam (G') x b=glowMark Y i (g+1) (multiplier (Q'.symm (K1.U.symm b))) X':=(e.1 b).trans (dispatch Y Q' X' g0.2.le _ _)
 rw [show glowMark Y i (g+1) (multiplier (rimGain K1 Q' z A')) X'= glowMark Y i (g+1) (multiplier (Q'.symm (K1.U.symm (plusE z+(2:ℝ)•A')))) X' from rfl,show glowMark Y i (g+1) _ X'=topBeam G' x (plusE z+(2:ℝ)•A') from (ht (plusE z+(2:ℝ)•A')).symm,map_add,map_smul, smul_sub,smul_add,smul_smul,smul_sub]
 change (1/2:ℝ) • _ + ((1/2:ℝ)*2) • _ - (1/2:ℝ) • ascender Y g i k (glowMark Y i g (glazeKey z) x) = (1/2:ℝ) • topBeam G' x (plusE z) - (1/2:ℝ) • _ + topBeam G' x A'; norm_num; abel
#print axioms sharpWitness
variable (v0:PantryFin Wage4 cloverFrame P.R.L A C H)
local notation "Z★"=> cloverFrame.pulseHidden P.R.L C H A
omit q₁ g0 F'
variable {ιm:Type}[Fintype ιm]
noncomputable abbrev rentalW (L:Side)(A C H:ℝ) :ℝ:= 1+2*cloverFrame.pulseHidden L C H A*(Fintype.card Wage4:ℝ)
noncomputable abbrev vboost (L:Side)(C H A:ℝ) :=2*(cloverFrame.pulseBase L*(1+2*(2*cloverFrame.pulseHidden L C H A)))
noncomputable def portGain (q:Bool→ Coords Wage4):ℝ:= gatherG (q true)+gatherG (q false)
lemma hutBound (ξ:ℕ) (l':a₀ ≤ ξ)(u':ξ ≤ g) (pC:1≤C)(pH:1≤H)(pA:1≤A)(z:Wage4⊕η) (v0:PantryFin Wage4 cloverFrame P.R.L A C H) (F':Examiners Y C H A m cloverFrame a₀ g (g+1) i k (F1Q Y i k g Q Q' M K1) R B): ‖ζv ξ z‖≤2*Z★:=by
 obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le l'
 let κ(n:ℕ):ℝ:= if h:n<d then ((F'.grow (a₀+n) (by omega) (by omega)).2.pilot).choose else 0
 let P'(i':ℕ):= (RootBook Y i k (a₀+i')).p
 let A'(i):=lapQ Y (a₀+i)
 have ht(j:ℕ)(h:j<d): Economics Τ C H A L★ (P' j) (P' (j+1)) (κ j) (A' (j+1)) (A' j) (R (a₀+j)):=by unfold κ; rw [dif_pos h]; exact ((F'.grow _ (by omega) (by omega)).2.pilot).choose_spec.1
 erw [Nat.add_sub_cancel_left]; exact jet_e ht pC pH pA v0 z -- /names
structure StageM (f0 g:ℕ)(V:Bool→ Coords Wage4):Prop where
 limit : mBooster P.R.L (portGain V)
 rimBound :∀ j, ‖V j‖ ≤ vboost P.R.L C H A
 spin :∀ s' (h:f0 ≤ s')(u:s'<g)(d:Bool), SeatsPriced (totalBudget A (Announcement Wage4 η)) Y s' i k (g+1) (portB Y i s' g u.le (multiplier (V d)) (glazeKey d) k) (rentalW P.R.L A C H*lapQ Y s')
-- should use even at f0=g(growth separate)
include h0 W' g0 q₁ q F' v0
lemma season_marked (T':Tracks A C H Y Τ g i k K1) (x:∀ z∈Finset.Icc a₀ g, Invoices (if z<g then A else 0) P Y z i k (g+1) (B z) (if z<g then lapQ Y z else 1)): let V'(d:Bool):=rimGain K1 Q' d (ζv g (.inl (.inl d))); StageM (η:=η) (i:=i) (k:=k) Y C H A a₀ g V':=by
 intro V'; let tH:=(W'.purser.awake g h0 le_rfl) |> fun p=> Whitened.charter p.1; obtain ⟨κ,qE,yq,tκ,hκ⟩:= T'.pilot
 let gγ:= cloverFrame.typical P.R.L (RootBook Y i k g).p (RootBook Y i k (g+1)).p κ (.inl true) * (lapQ Y (g+1)/lapQ Y g)
 let z'(z:Bool):= ζv g (Sum.inl (Sum.inl z)); have hK(s)(p:a₀ ≤ s)(u:s≤g)(d): ‖ζv s d‖ ≤ 2*Z★:= hutBound Y m C H A Q Q' M _ p u tH.lease.large tH.eUp tH.accr d v0 F' -- `{p}` give types
 have hh:= cloverFrame.typical_bounds _ (RootBook Y i k g).p (RootBook Y i k (g+1)).p _ tκ hκ tH.corset₁ tH.corset₂ _ _ tH.buoy tH.climb tH.climb' (.inl true) -- Pupil hr
 refine ⟨mBooster.of_rim _ _ _ _ _ Q' _ _ _ _ _ qE z' (fun i=> hK _ h0 le_rfl _) _ rfl v0 hh.1 hh.2 q.maturity (fun i=> q.firms _ rfl),fun i=>?_,?_⟩
 · apply (q.maturity _).trans; unfold vboost; apply mul_le_mul_of_nonneg_left _ zero_le_two; apply (qE.sail _).trans; apply mul_le_mul_of_nonneg_left _ (div_pos receipt_pos (cloverFrame.chi_pos _)).le; apply (norm_add_le ..).trans; rw [plusE, ShapeLab.leg_norm,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]; gcongr; exact hK _ h0 le_rfl _
 intro s p0 uf j
 obtain ⟨T,t⟩:= F'.fleet _ p0 uf.le; have f1:= x s (mem_Icc.mpr ⟨p0,uf.le⟩); simp only [if_pos uf] at f1; let X:= ζv s (Sum.inl (Sum.inl j)); let Y':=escrow (η:=η) (.inl j:Wage4)
 let Dκ(i:W★)(_:W★):ℝ:= Sum.elim X (fun i':Wage4⊕η=> if i'=Sum.inl (Sum.inl j) then 1 else 0) i
 have he: portB Y i s g uf.le (multiplier (V' j)) (glazeKey j) k= earnBy (B s) Dκ Y':=by
    funext v; rw [show portB _ _ _ _ _ _ _ _ _ = B s Y' v+topBeam (B s) v X from sharpWitness Y Γ m C H A Q Q' g0 M F' q₁ p0 uf.le j v]; unfold earnBy; rw [Fintype.sum_sum_type]; unfold topBeam; rw [ShapeLab.cols_apply]; simp only [Dκ, ite_smul, zero_smul,one_smul,Sum.elim_inl,Sum.elim_inr,sum_ite_eq',mem_univ,if_true,sum_ite_eq]; exact add_comm ..
 rw [he]
 let U:=Z★; have hu:=hK s p0 uf.le (Sum.inl (Sum.inl j)); change ‖X‖ ≤ 2*U at hu; have hv:0≤U:=by linarith only [hu,norm_nonneg X]
 refine priceSeats Y A (W:= B s) (fun i t₁=> fieldPermit_of_episode Y m _ _ t i t₁) f1 (morning_safe Y i k g0.1 g0.2.le) Dκ Y' _ (show 0≤ 1+2*U*(Fintype.card Wage4:ℝ) from by positivity) ?_
 intro i; unfold Dκ; rw [Fintype.sum_sum_type]; simp only [Sum.elim_inl, Sum.elim_inr, apply_ite abs, abs_one, abs_zero, sum_ite_eq',sum_ite_eq,mem_univ,if_true]; let h:= sum_le_sum (s:=univ) (f:=fun i:Wage4=> |X i|) fun i _=> (norm_le_pi_norm _ i).trans hu; rw [sum_const,card_univ,nsmul_eq_mul] at h; unfold rentalW; change _ ≤ 1+2*U*(Fintype.card _); linarith only [h]

end Shrine
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
