import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Stitched

/-!
# Genuine auxiliary histories

Selected for the bridge. They are *not* `Canter` witnesses (which would retain a
possibly tighter wave band under Heron); prices here are retained at the
actual co-elected rates. Use the genuine `Lives_B` with the pre-pivot Scroll.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x
open Brace

/-- The heat law with the lower-step election compatible with the rate theorem's
canonical shots. Use `Chaff.lit_R` to access its `shireF` integrals. `B0` may thus be
shared with the corresponding sharp history, not between periods. Only the donor takes
heat at the top (real time parameter `radiusB (hat R.L x (trunkY n b))`). -/
structure Donor (V : Grace K R L) {U : Grasp V.U B d} {W : GivenX V U}
    {x : ℝ} (b n N0 : ℕ) (J : Robes N V W) (q : Chi) (h : ℝ) (D C Q : ℝ → ℝ)
    (T : Month x 1 6 2 N0 V W) (m : Side) (ht : T.q ≤ m.val)
    (S : Cape m B R.L) (B0 f : ℕ → ℝ) (P : Prescription R B) (F0 : Scrolls B) where
  gram : Vestal m B R.L
  wave : ℕ→SpaceM
  tilt : ℕ→ℝ
  allowance : ℕ → ℝ
  radius : ℕ → ℝ
  cash : ℝ
  offset : ℝ
  top : RegBudget (cell m B R.L (trunkY n b))
  vane (i:ℕ) : i ≤ buoy n → allowance i=dleaf R.L (hat R.L x i)
  rare(i:ℕ): Rue.IsleB SU.group (T.a i).threshold
  pole(i:ℕ): (T.a i).threshold ≤ J.k
  cape : CanCape J q m S
  due : Due V 1 2 6 N0 T m ht (trunkY n b) B0
  lives : Lives_B (H:=h) V (F0 (mesh m R.L (trunkY n b))) top (radiusB (hat R.L x (trunkY n b))) cash (T.a (trunkY n b)) (S (trunkY n b)) U offset
  pull : Pull_K V 1 2 6 N0 T m ht n b B0 J q h D allowance (coldQ R.L Q radius x n) S top offset gram wave tilt
  cool : Refrigerated J q n b h P C T ht S f gram wave tilt
  balance (i:ℕ) : i ≤ trunkY n b → partitionZ (gram i) U (S i) = partitionZ (gram (trunkY n b)) U (S (trunkY n b))

namespace Donor
variable (H : Service V U W J q h D C Q P N0 delay) (pY : ResponsiveService J q N0 h delay P)
    (YQ : Sculp V 1 2 6 N0 m 0 J q h δ R0 E Cf y D' hy Fp n b Jx V0)
    {Ue : RegBudget (cell m B R.L (trunkY n b))} {sE:ℝ} {F0:Scrolls B}
    (hb : Due V 1 2 6 N0 T m ht (trunkY n b) B0) (hh : 1≤h) (hk : B=R.L^b)
    (w : Bon J q h D delay (Actual T ht W0 f (trunkY n b)))
    (pS:Lives_B (H:=h) V (F0 (mesh m R.L (trunkY n b))) Ue (radiusB (hat R.L x (trunkY n b))) (Fp (hat R.L x (trunkY n b))) (T.a (trunkY n b)) (W0 (trunkY n b)) U sE)
local notation "Qh" => hueR V 1 2 6 N0 T m ht (trunkY n b) B0
include ht pS YQ hk hh
-- Adapted from the top provision in Tar's `ride_V`.
private lemma provides (x' : ℝ) :
    Provides R.L K.j (color_b (Qh kT) x' Ue 0 0 (sE:ℂ)) h (V0 kT) (zone_F kT (post_H n)) := by
    have he:zone_F kT (post_H n)=some b:=by unfold zone_F trunkY; rw [if_pos (by omega),Nat.add_sub_cancel_left]
    have hA := pS.weight
    rw [he]; have hc := Provides.liftE h (Qh kT) _ _ hA YQ.cost
    refine ⟨⟨hc.weight,fun s v=>hc.face s (by subst B; exact ply_J _ _ s v)⟩,rfl,?_⟩
    have ht':0≤ Fp (hat R.L x kT):=by
       obtain ⟨A,u,w⟩:= hA.weight; refine (sum_nonneg fun j _=>?_).trans (w 0); split; exact mul_nonneg (Real.exp_pos _).le ((Taxi.eraF _ _ (u j) (zero_le_one.trans hh) 1 (ping_f (T.a kT) _)).grade); exact le_rfl
    exact Provides.liftQ h (Qh kT) _ _ (Vale.lye (ply_U R.L b) _ _).2 (ht'.trans YQ.cost)

include H pY hb w
lemma exists_fixed : Nonempty (Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0) := by
  obtain ⟨G,t,z,p,r⟩ := stitched_exists ht H pY YQ hb hh w (provides ht YQ hh hk pS)
  have hc : CanCape J q m W0 := w.can.cape
  have hv(i j:ℕ)(hi:i≤j)(hj:j≤ kT):partitionZ (G i) U (W0 i)=partitionZ (G j) U (W0 j):= by
    induction j with | zero => rw [show i=0 by omega] | succ j ih=> rcases hi.eq_or_lt with u|u; rw [u]; exact (ih (by omega) (by omega)).trans (purse V 1 2 6 N0 T m ht n b B0 hb J q h D V0 (coldQ R.L Q Jx x n) W0 hc _ _ p w.can.isle j hj)
  exact ⟨⟨G,t,z,V0,Jx,_,sE,Ue,YQ.vane,w.can.isle,w.can.pole,hc,hb,pS,p,r,fun i p=> hv i kT p le_rfl⟩⟩

omit YQ pS hb w
variable {v z:ℝ}
include ht H pY hk hh
lemma available (S:Sculpture V q b h F0 Q D v N0 J z) (hz:z ≤ x) :
    ∀ᶠ n in atTop, ∀ B0, Bon J q h D delay (Actual T ht W0 f (trunkY n b)) →
      Due V 1 2 6 N0 T m ht (trunkY n b) B0 → Nonempty (Donor V b n N0 J q h D C Q T m ht W0 B0 f P F0) := by
  obtain ⟨Fp,R0,E,C0,D₀,z',H',_,_,_,_,_,_,_,_,h₀,Q₁,Q₂⟩ := S.pay_calendar
  filter_upwards [Q₂ x hz (h₀.trans hz) m] with n τ
  obtain ⟨Jx,V0,p⟩ := τ
  intro B0 w v'
  let i:=trunkY n b; let P':= T.a i; let V':= Vale.mesh m R.L i
  have ht' := (w.can.cape i)
  have hp':hintF P' 2 6 (hat R.L x i) 1 := let H:= T.boot i; ⟨H.2.2.2.1,H.2.2.2.2,H.1,H.2.1,H.2.2.1⟩
  have hu:=hz.trans (Vale.crown R.L x i)
  have hsize:100*(1+ P'.B) ≤ (Domain V' B).val:=by unfold P'; rw [(T.boot i).2.1]; exact (T.clear ht 0 i).1.size
  obtain ⟨s,F,b⟩ := Q₁ (hat R.L x i) hu (Vale.mesh m R.L i) P' (W0 i) ht'.paid hp' (J.gran.trans ht'.size) ((T.boot i).2.1 ▸ S.ready _ hu) (w.can.pole i) (by change _ < (Domain V' B).val; omega)
  exact exists_fixed ht H pY p v' hh hk w b
end Donor
end LocalLimit
end YM.CF.Py.Rate
