import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Solve

/-! Join at the end of burn. Compare the READINGS of these auxiliary data in the
heat law later; not asserting every Canter uses canonical lower steps. -/

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

variable (Y : Service V U W J q h D C Q P N0 delay) (pY : ResponsiveService J q N0 h delay P)
    (YQ : Sculp V 1 2 6 N0 m 0 J q h δ R0 E Cf y D' hy Fp n b Jx V0)
    {Ue : RegBudget (cell m B R.L (trunkY n b))} {sE:ℂ}
    (hb : Due V 1 2 6 N0 T m ht (trunkY n b) B0) (hh : 1≤h) (hn : δ ≤ D)
    (w : Bon J q h D delay (Actual T ht W0 f (trunkY n b)))
    (pS:∀ b':ℝ,Provides R.L K.j (color_b (hueR V 1 2 6 N0 T m ht (trunkY n b) B0 (trunkY n b)) b' Ue 0 0 sE) h (V0 (trunkY n b)) (zone_F (trunkY n b) (post_H n)))
local notation "pβ" i:max t:max => tempo_v kT B0 (fun i=> Φ i) t i
variable {α : ∀ j:ℕ, StarPS (trunkY n b) → RegBudget (cell m B R.L j)}
    {φ : ∀ j:ℕ, StarPS (trunkY n b) → ForceBudget (cell m B R.L j)}
    {ν : ℕ→ StarPS (trunkY n b) → ℂ}
    {LW : ∀ i:ℕ, StarPS (trunkY n b) → Haro.ΘS (Jx i)}
    {Δ : ℕ → StarPS (trunkY n b) → ℝ} {ζw : ℕ → ℝ}
    (hL : Trailm V 1 2 6 N0 T m ht n b 0 B0 J q h R0 E Cf δ y D' hy V0 Jx Fp YQ W0 Ue sE α φ ν LW Δ ζw (buoy n))
local notation "Θcap" => (fun t=> (α kS t,φ kS t))
local notation "Qbeta" => (fun i t=> pβ i t)
local notation "YΤ" => Hymn_v V 1 2 6 N0 T m ht n b B0 α φ ν
local notation "body" i:max => (W.arm (T.large.trans ht) kT).Q i
local notation "gs" z:max i:max => (guess_Q kT (fun i=>Φ i) z i)
open Pitching Focus
include ht Y pY YQ hb hh w
include hL
set_option maxHeartbeats 800000 in
private lemma stitch :
    ∃ G t z, Pull_K V 1 2 6 N0 T m ht n b B0 J q h D V0 (coldQ R.L Q Jx x n) W0 Ue sE G t z ∧
             Refrigerated J q n b h P C T ht W0 f G t z := by
  let S:=kS
  let L:=kT
  let Z := Cooling.descends P BT kS Θcap Qbeta
  have ho:= deeper n b
  have hc : ∀ j < kS, _ := fun j p => Z.paid Y pY w ho.le hh (boost ht YQ hb w) (entrance ht YQ hL) j p
  obtain ⟨t,q',H⟩ := latch (Z:=Z) ht Y pY YQ hb hh w hL
  let vβ(i:ℕ) := pβ i t
  let yZ:= ν kS t
  let F (i:ℕ) : Corr (cell m B R.L i) := if i < S then Z.G i t else (α i t,φ i t)
  let u(i:ℕ) := if i < S then Z.v i t + yZ else ν i t
  let Yf(i:ℕ) := if i < S then Z.wave i t else (LW i t).val
  let G(i) := construct (T.a i) (V.L.path (L-i)) K.top.clip (body i) (vβ i) (F i) (u i)
  let z(i:ℕ) := gs t i
  have hpβ (i:ℕ) : vβ (i+1) - B0 (i+1) - (vβ i-B0 i)= z i := by unfold vβ; rw [boom_z]; unfold z; ring
  have hu' (i:ℕ)(p:S ≤ i) : G i= YΤ t i := by
    have he:F i=(α i t,φ i t) := if_neg (not_lt.mpr p)
    unfold G; rw [he, show u i=ν i t from if_neg (not_lt.mpr p)]
  have he (i:ℕ)(p:i ≤ S) : F i= Z.G i t ∧ u i=Z.v i t+yZ := by
    rcases p.eq_or_lt with H|H
    · subst i; rw [show Z.G S=Θcap from Z.fromTop, show Z.v S=0 from Z.fromZero]
      simp only [Pi.zero_apply,zero_add]; exact ⟨if_neg (lt_irrefl _),if_neg (lt_irrefl _)⟩
    exact ⟨if_pos H,if_pos H⟩
  have feePr(i)(t':i<S) : Charged (T.a i) (body i) K.j R.L.val h (Yb i /1000) (F i) := (he i t'.le).1 ▸ (hc i t').1.cost t
  refine ⟨G,Yf,z,⟨?_,?_,?_, fun i _=> ⟨rfl,rfl,rfl,rfl⟩, ?_,?_, fun i _=> hpβ i,?_,?_⟩,
      ⟨fun i=>rfl, feePr, fun i v=> (compatible_query ht YQ hb w v t).2, ?_⟩⟩
  · intro i hi a ha
    by_cases p : i<S; swap
    · have hx:kS ≤ i:= by omega
      rw [hu' i hx,hu' _ (by omega),show Yf i=(LW i t).val from if_neg p]
      exact hL.wear i hx hi t (H i hi hx).1 (H i hi hx).2 _ ha
    let J':= (LW i t).val
    have ht' := (hc i p).2.2.2 t
    have hu0:vβ (i+1) + (B').last.move i - Z.posted i t=vβ i := by
      have hE : Z.posted i t = z i := q' _ p; have hM : B0 i=B0 (i+1)+(B').last.move i := hb.fee i hi
      linarith only [hpβ i,hE,hM]
    have hZ : Z.launch i t= Z.guess i t := congrArg (fun b => construct _ _ _ _ b _ _) hu0
    have hs := ht'.2.2.2 a ha; rw [hZ] at hs
    rw [show Yf i=Z.wave i t from if_pos p]
    calc
      _ = Complex.exp yZ • stove U (W0 i) (Z.guess (i+1) t) (W0 (i+1)) (apt m B R.L i) (((B').address i).step V) q J.d (Z.wave i t).val a := by
        unfold G; rw [(he _ p).1,(he _ p).2]
        exact Focus.carP (q:=q) (Fo:=W0 i) (Fx':=W0 (i+1)) a U (Z.guess (i+1) t) (Z.v (i+1) t) yZ _ (Z.wave i t) J.d
      _ = Complex.exp yZ • denZ (Z.guess i t) U (W0 i) a := congrArg (Complex.exp yZ • ·) hs.symm
      _ = _ := by
        unfold G; rw [(he _ p.le).1,(he _ p.le).2]; exact (mountR U _ (Z.guess i t) a (Z.v i t) yZ).symm
  · intro i hi; unfold Yf coldQ; split_ifs with p; exact ((hc i p).2.2.2 t).2.1; exact (LW i t).property
  · intro i hi; unfold z mode_D; by_cases p:i < kS
    · rw [if_pos p,← q' i p]; exact ((hc i p).2.2.2 t).1
    rw [←(H i hi (not_lt.mp p)).2]; exact (show |Δ i t| ≤ _ from by have hh:= hL.fee i (not_lt.mp p) hi t; unfold mode_D at hh; rw [if_neg p] at hh; rw [if_neg p]; exact hh)
  · intro i p; by_cases u:i < S; swap; · rw [hu' i (not_lt.mp u)]; exact hL.paid i (not_lt.mp u) p t
    rw [zone_F, if_neg (show ¬ post_H n < i by unfold post_H; omega),YQ.vane _ u.le]
    exact ((feePr i u).mono (div_le_self (w.clocks i).leaf.le (by norm_num))).laurel ..
  · intro i p; exact tilt_a V 1 2 6 N0 T m ht 0 B0 J q h δ R0 E Cf y D' hy YQ hb t i p
  · change tempo_v _ _ _ _ 0=_; simp [tempo_v]
  · rw [hu' kT ho.le]; unfold Hymn_v; rw [hL.cash, hL.past, hL.heat]; rfl
  intro i p
  let X:= (BT).op P i
  change z i=X.posted (vβ (i+1)) (F (i+1)) ∧ Yf i=X.wave (vβ (i+1)) (F (i+1)) ∧ F i=X.realArr (vβ (i+1)) (F (i+1)) ∧ |(u i).re-(u (i+1)).re|≤ _
  rw [(he (i+1) p).1,(he i p.le).1,(he i p.le).2,(he (i+1) p).2,Complex.add_re,Complex.add_re,add_sub_add_right_eq_sub]
  exact ⟨(q' i p).symm,if_pos p,Z.step _ p _, ((hc i p).2.2.2 t).2.2.1⟩
omit hL
include pS
lemma stitched_exists :
    ∃ G t z, Pull_K V 1 2 6 N0 T m ht n b B0 J q h D V0 (coldQ R.L Q Jx x n) W0 Ue sE G t z ∧
             Refrigerated J q n b h P C T ht W0 f G t z := by
  obtain ⟨A,Q,v,W,D,p⟩:= leap_T V 1 2 6 N0 T m ht n b 0 B0 hb J q h R0 E Cf δ y D' hy V0 Jx Fp YQ W0 w.can.cape Ue sE pS hh w.can.admissible (kT-kS) (by omega)
  rw [Nat.sub_sub_self (deeper ..).le] at p
  exact stitch ht Y pY YQ hb hh w p
end LocalLimit
end YM.CF.Py.Rate
