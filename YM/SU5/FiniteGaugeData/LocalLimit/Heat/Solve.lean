import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Down
import YM.CF.Vp929.Ledger.Year

/-!
# Mixed election (one period, trunk cutoff)

Run Tar for the heat burn then the identical canonical step Service as used
on the sharp histories. Co-elected using Brouwer, only shifts predicted below
burn. No shooting comparison between periods. Cf `manuscripts/the earlier construction/VOLUME_PAVING`
(as distinct from the coherent W/bare sharing required in 503).
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

-- Structural declaration for the comparisons later. Not asserting offset equation at
-- the top of any canonical start (burn is intentionally not one).
structure Refrigerated (J:Robes N V W)(q:Chi)(n b:ℕ)(h:ℝ)(P:Prescription R B)(D:ℝ→ℝ)
    (T:Month x 1 6 2 N0 V W)(ht:T.q ≤ m.val)(W0:Cape m B R.L)(f:ℕ→ℝ)
    (G:Vestal m B R.L)(t:ℕ→SpaceM)(z:ℕ→ℝ) : Prop where
  represented (i:ℕ): G i=construct (T.a i) (V.L.path (trunkY n b-i)) K.top.clip
     ((W.arm (T.large.trans ht) (trunkY n b)).Q i) (G i).beta ((G i).F,(G i).K) (G i).v
  charged (i:ℕ) (p:i<buoy n): Charged (T.a i) ((W.arm (T.large.trans ht) (trunkY n b)).Q i) K.j R.L.val h (dleaf R.L (hat R.L x i)/1000) ((G i).F,(G i).K)
  enters (i:ℕ) (p:i ≤ buoy n): entersReal (hat R.L x i) (G i).beta
  related (i:ℕ) (p:i<buoy n):
     let S := Branch.op P (Actual T ht W0 f (trunkY n b)) i
     let b' := (G (i+1)).beta; let F:= ((G (i+1)).F,(G (i+1)).K)
     z i=S.posted b' F ∧ t i=S.wave b' F ∧ ((G i).F,(G i).K) = S.realArr b' F ∧
       |(G i).v.re-(G (i+1)).v.re| ≤ D (hat R.L x i)*sites (Ω i)

/-- Use `Pull_K` with enlarged wave below burn. -/
def coldQ (L:Side) (R0:ℝ→ℝ) (f:ℕ→ℝ) (x:ℝ) (n i:ℕ) := if i < buoy n then R0 (hat L x i) else f i

lemma pilot_eq (D : Due V 1 2 6 N0 T m ht (trunkY n b) B0) (f:ℕ→ℝ) (W0:Cape m B R.L) (i:ℕ)(p:i ≤ trunkY n b) : B0 i=(ActualSpine T ht W0 f (trunkY n b)).pilot x i := by
  let F:= ActualSpine T ht W0 f (trunkY n b)
  induction i with
  | zero => exact D.unit.trans F.pilot_zero.symm
  | succ i ih => exact add_right_cancel ((D.fee i p).symm.trans ((ih (by omega)).trans (F.pilot_move i)))

lemma deeper (n b): buoy n < trunkY n b := by unfold trunkY post_H; omega

section purchase
variable (Y : Service V U W J q h D C Q P N0 delay) (pY : ResponsiveService J q N0 h delay P)
    (YQ : Sculp V 1 2 6 N0 m 0 J q h δ R0 E Cf y D' hy Fp n b Jx V0)
    {Ue : RegBudget (cell m B R.L (trunkY n b))} {sE:ℂ}
    (hb : Due V 1 2 6 N0 T m ht (trunkY n b) B0) (hh : 1≤h) (hn : δ ≤ D)
    (w : Bon J q h D delay (Actual T ht W0 f (trunkY n b)))
    (pS:∀ b':ℝ,Provides R.L K.j (color_b (hueR V 1 2 6 N0 T m ht (trunkY n b) B0 (trunkY n b)) b' Ue 0 0 sE) h (V0 (trunkY n b)) (zone_F (trunkY n b) (post_H n)))
local notation "pβ" i:max t:max => tempo_v kT B0 (fun i=> Φ i) t i
include ht YQ hb w

lemma compatible_query {i : ℕ} (hi : i ≤ buoy n) (v : StarPS (trunkY n b)) :
    enters (hat R.L x i) (pβ i v) ∧ entersReal (hat R.L x i) (pβ i v) := by
  let F := (B').pilot x
  have hf:= pilot_eq ht hb f W0 i (hi.trans (deeper ..).le)
  have he:= w.pilots i (hi.trans (deeper ..).le)
  have hx := (w.clocks i).grade
  have hA := (w.clocks 0).grade; rw [hat_zero] at hA
  let Y:=hat R.L x i; let Z:=pβ i v; have hz:|Z-F i| ≤ Y/8 := by
    unfold Z tempo_v; rw [hf,add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i' p=> (credits_q _ _ (fun i=>(YQ.maxim i).le) v i').trans (show wage_B n b i' R.L x ≤ nu_B R.L from le_of_eq (if_pos (lt_of_lt_of_le (mem_range.mp p) hi))))).trans ?_)
    rw [sum_const,card_range,nsmul_eq_mul]; unfold Y nu_B ν_PS hat; linarith
  obtain ⟨hl,hu⟩:= abs_le.mp hz
  have he' : 3/4 * Y ≤ F i := he.1
  have ht' : F i ≤ 3/2*Y := he.2
  unfold enters entersReal; rw [Complex.ofReal_re,Complex.ofReal_im,abs_zero]
  refine ⟨⟨by linarith,by linarith,by linarith [strip_pos hx]⟩,by linarith,by linarith⟩

-- Split off the finite-dimensional fixed point. High waves are still guessed;
-- the unobserved wave components of guesses at low indices are sent to zero.
omit ht YQ hb w
private lemma root_combo {Jx:ℕ→ℝ}
    (Hope:∀ i,0<wage_B n b i R.L x)(Ψ:∀ i,0<Jx i)
    (W : ℕ → StarPS (trunkY n b) → SpaceM) (D : ℕ → StarPS (trunkY n b) → ℝ)
    (hD : ∀ i < trunkY n b, Continuous (D i) ∧ ∀ t, |D i t| ≤ wage_B n b i R.L x)
    (hW : ∀ i < trunkY n b, Continuous (W i) ∧ ∀ t, ‖W i t‖ ≤ Jx i) :
    ∃ t:StarPS (trunkY n b), ∀ i < trunkY n b, (θ_guess Jx (fun i=>(Ψ i).le) i t (l0:=trunkY n b)).val=W i t ∧ D i t=guess_Q _ (fun i=>wage_B n b i R.L x) t i := by
  let T:= StarPS kT
  let g (t : T)(i:Fin kT) := (D i t / Φ (i:ℕ),(Jx (i:ℕ))⁻¹ • W i t)
  have hg(t:T): ‖g t‖ ≤ 1:= by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>?_; let a:= Jx i; have hp:0<a:=Ψ i
    change max ‖D i t / Φ (i:ℕ)‖ ‖a⁻¹ • W i t‖ ≤ 1; rw [Real.norm_eq_abs,abs_div,abs_of_pos (Hope _),norm_smul,Real.norm_of_nonneg (inv_pos.mpr hp).le]
    exact max_le ((div_le_one (Hope _)).2 ((hD _ i.isLt).2 _)) ((mul_le_mul_of_nonneg_left ((hW _ i.isLt).2 _) (inv_pos.mpr hp).le).trans_eq (inv_mul_cancel₀ hp.ne'))
  let G(t:T) : T := ⟨g t,hg t⟩
  have hc : Continuous G := Continuous.subtype_mk
    (continuous_pi fun (i:Fin kT)=> (((hD _ i.isLt).1).div_const (Φ (i:ℕ))).prodMk (((hW _ i.isLt).1).const_smul ((Jx (i:ℕ))⁻¹))) _
  obtain ⟨t,p⟩:= Moen.Space.bow zero_lt_one G hc
  refine ⟨t, fun i hi=>?_⟩
  let j:Fin kT:=⟨i,hi⟩
  have ht:t.val j=g t j:=congrFun (congrArg Subtype.val p.symm) j
  have hθ (u:SpaceM) : Jx i • (Jx i)⁻¹ • u=u := smul_inv_smul₀ (Ψ _).ne' _
  unfold θ_guess guess_Q; rw [dif_pos hi,dif_pos hi]; constructor
  · change Jx i • (t.val j).2 = W i t; rw [ht]; exact hθ _
  rw [ht]; change _ = Φ i * (D i t / Φ i); rw [mul_comm,div_mul_cancel₀ _ (Hope _).ne']
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
include ht YQ hL
lemma entrance : Cleared W h (Yb kS) (T.a kS) (body kS) (kT-kS) (W0 kS) Θcap (Qbeta kS) 0 := by
    refine ⟨fun y _ => continuous_dens_raw y continuous_const (tilt_Qc ..) (hL.keep _) (hL.stay _), fun t=> ?_, ⟨0,fun t=> le_rfl⟩⟩
    have h : Laurel (YΤ t kS) K.j h (Yb kS) (Yb kS) R.L.val := by
      have h:= hL.paid kS le_rfl (deeper ..).le t
      rw [YQ.vane _ le_rfl,zone_F,if_neg (show ¬post_H n<kS by unfold post_H; omega)] at h; exact h
    obtain ⟨h,_,a,b,c⟩:= h
    exact ⟨⟨h,a⟩,b,c⟩

variable {Z:Cooling P (Actual T ht W0 f (trunkY n b)) (buoy n)
      (fun t=> (α (buoy n) t,φ (buoy n) t)) (fun i (t:StarPS (trunkY n b))=> tempo_v (trunkY n b) B0 (fun i=>wage_B n b i R.L x) t i)}

omit hL
include hb w
lemma boost : ∀ i ≤ kS, Continuous (Qbeta i) ∧ ∀ t, enters (hat R.L x i) (Qbeta i t) :=
  fun _ hi=> ⟨tilt_Qc ..,fun t=> (compatible_query ht YQ hb w hi t).1⟩
include Y pY hh hL
lemma latch : ∃ t:Γ, (∀ i < kS, Z.posted i t = gs t i) ∧ ∀ i<kT, kS ≤ i →
          θ_guess Jx (fun i=> (YQ.rateB i).le) i t = LW i t ∧ Δ i t=gs t i := by
    have H i (q:i<kS) := Z.paid Y pY w (deeper ..).le hh (boost ht YQ hb w) (entrance ht YQ hL) _ q
    let W'(i:ℕ)(t:Γ):SpaceM := if i<kS then 0 else (LW i t).val
    let D'(i:ℕ)(t:Γ) := if i<kS then Z.posted i t else Δ i t
    have gD : ∀ i < kT, Continuous (D' i) ∧ ∀ t, |D' i t| ≤ Φ i := by
      intro i hi; by_cases v:i<kS; swap
      · rw [show D' i=Δ i from funext fun _=>if_neg v]
        exact ⟨hL.contD i,fun j=> (hL.fee i (not_lt.mp v) hi j).trans (YQ.dose i hi)⟩
      rw [show D' i=Z.posted i from funext fun _=> if_pos v]
      refine ⟨(H i v).2.1, fun t=> ((H i v).2.2.2 t).1.trans ((w.clocks i).slow.trans ?_)⟩
      rw [wage_B,if_pos v]; unfold nu_B ν_PS; linarith [(w.clocks i).slope]
    have gW : ∀ i < kT, Continuous (W' i) ∧ ∀ t, ‖W' i t‖ ≤ Jx i := by
      intro i _; unfold W'; by_cases v:i<kS
      · simp_rw [if_pos v]; exact ⟨continuous_const,fun t=>by rw [norm_zero]; exact (YQ.rateB _).le⟩
      simp_rw [if_neg v]; exact ⟨continuous_subtype_val.comp (hL.contW i),fun t=> (LW i t).property⟩
    obtain ⟨t,e⟩ := root_combo (R:=R) YQ.maxim YQ.rateB W' D' gD gW
    refine ⟨t,fun i p=> ?_, fun i hi hv=>?_⟩
    · simpa only [D',if_pos p] using (e i (p.trans (deeper ..))).2
    obtain ⟨u,v⟩:= e i hi; unfold W' at u; rw [if_neg (not_lt.mpr hv)] at u; unfold D' at v; rw [if_neg (not_lt.mpr hv)] at v
    exact ⟨Subtype.ext u,v⟩


end purchase
end LocalLimit
end YM.CF.Py.Rate
