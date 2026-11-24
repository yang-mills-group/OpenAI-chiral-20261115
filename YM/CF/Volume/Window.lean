import YM.CF.Paxos.Rost
import YM.CF.Ups.Gul
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 1800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
namespace Volume
/-- Unnormalized Brioche histories obtained at any compatible period on the given MeterQ.
We do not include phase compensator as an independent consumer. -/
structure History (x : ℝ) (m : Side) (n : ℕ) where
  month : Month x a i p N0 V W
  tip : month.q ≤ m.val
  B0 : ℕ → ℝ
  gram : Vestal m B R.L
  cape : Cape m B R.L
  wave : ℕ → Haro.SpaceM
  tilt : ℕ → ℝ
  flow : Brioche V a p i N0 month m tip n B0 J q h R0 δ gram cape wave tilt

/-- Get History for each n with the same Month and same Cape, keeping offset
comparisons, also at the other compatible periods. -/
theorem allHistory (X : Month x a i p N0 V W)
    (Y : MeterQ V a p i N0 J q h R0 δ x X) (M : Side) (hM : J.h ≤ M.val)
    (hq : grainZ V W N0 x ≤ (M*N').val) (hst : 61 ≤ (M*N').val) :
    ∃ (w0 : Cape (M*N') B R.L) (ρ : ℕ → ℝ),
      (∀ j, 0 < ρ j) ∧ ∀ n,
       ∃ Z : History V a p i N0 J q h R0 δ x (M*N') n,
        Z.month = X ∧ Z.cape = w0 ∧
         ∀ j < n, ‖Complex.exp (Z.gram (j+1)).v‖*ρ j ≤ ‖Complex.exp (Z.gram j).v‖ := by
  have ht := Y.core.symm ▸ hq
  obtain ⟨w0,ρ,hρ,hr,hX⟩ := Y.ridge M hM ht hst
  refine ⟨w0,ρ,hρ,?_⟩
  intro n
  obtain ⟨B0,Z,Q,tilt,hD,hE,hP,hI,hB⟩ := hX n
  exact ⟨⟨X,ht,B0,Z,w0,Q,tilt,hP,hD,Y.tint,Y.pole,hI,hr,hB⟩,rfl,rfl,hE⟩

private lemma mesh_side (m : Side) : Vale.mesh m R.L 0 = m := by simp [Vale.mesh]
private lemma cell_zero_val (m : Side) : (cell m B R.L 0).val = m.val * 2 * B.val := by
  change (mid (Vale.mesh m R.L 0) B).val = _
  rw [mesh_side]
  rfl

variable {x' : ℕ→ℝ} (t : Tendsto x' atTop atTop)
variable {M : ℕ→Side} {n' : ℕ→ℕ} (Z : ∀ k, History V a p i N0 J q h R0 δ (x' k) (M k) (n' k))
local notation "Aξ" => (fun k => ((radiusB (x' k):ℕ) : ℝ))
local notation "Φ" => (fun k=>Lr (x' k))
local notation "SM" => (fun k => cell (M k) B R.L 0)
variable (Sb : ℝ) (b1 : ℕ)
variable (hm : ∀ k, grainZ V W N0 (x' k) ≤ (M k).val)
variable (hW : ∀ k, ((M k).val:ℝ) ≤ Sb * (((oYY V N0 J (x' k)).val:ℝ)^b1))

include t hW in
private lemma windowGray (F : ℕ→ℝ) (hF : Tendsto F atTop atTop)
    (hh : Gray F (eur fun k => cell (oYY V N0 J (x' k)) B R.L 0)) :
    Gray F (eur SM) := by
  let c := 2 * (B.val : ℝ)
  let mstar := fun k => ((oYY V N0 J (x' k)).val : ℝ)
  have hd : 0 < (B.val : ℝ) := by exact_mod_cast B.property
  have hc : 0 < c := by dsimp only [c]; positivity
  have hu : 1 ≤ c := by
    have hb : 1 ≤ B.val := B.property
    have : 1 ≤ (B.val : ℝ) := by exact_mod_cast hb
    dsimp only [c]; linarith
  have hw : Gray F mstar := hh.higher (Eventually.of_forall fun k => by
      dsimp only [eur,mstar]
      rw [cell_zero_val, Real.norm_of_nonneg (by positivity)]
      nth_rw 1 [Nat.cast_mul (m := (oYY V N0 J (x' k)).val * 2)]
      nth_rw 1 [Nat.cast_mul (m := (oYY V N0 J (x' k)).val) (n := 2)]
      rw [Nat.cast_ofNat]
      calc
        _ ≤ ((oYY V N0 J (x' k)).val:ℝ)*c := le_mul_of_one_le_right (by positivity) hu
        _ = _ := by dsimp only [c]; ring)
  apply ((Gray.coef hF c).mul ((Gray.coef hF Sb).mul (Gray.powG hF hw b1))).higher
  filter_upwards with k; dsimp only [eur,mstar]
  rw [Real.norm_of_nonneg (by positivity),cell_zero_val]
  rw [Nat.cast_mul (m := (M k).val * 2)]
  rw [Nat.cast_mul (m := (M k).val) (n := 2), Nat.cast_ofNat]
  exact le_trans (le_of_eq (by dsimp [c]; ring))
           (mul_le_mul_of_nonneg_left (hW k) hc.le)

include t hm in
private lemma windowTend : Tendsto (eur SM) atTop atTop := by
  have hA : Tendsto Aξ atTop atTop := tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp t)
  apply tendsto_atTop_mono _ hA
  intro k
  have hr : radiusB (x' k) ≤ grainZ V W N0 (x' k) := by
    simp only [grainZ]
    have : 1+Pressure.radiusB (x' k) ≤ (100+N0)*(1+Pressure.radiusB (x' k)) :=
       Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hc : radiusB (x' k) ≤ (cell (M k) B R.L 0).val := by
     rw [cell_zero_val]
     exact ((hr.trans (hm k)).trans (Nat.le_mul_of_pos_right _ (by decide))).trans
                  (Nat.le_mul_of_pos_right _ B.property)
  exact_mod_cast hc

open Graph Onyx Pyx Brioche
variable(hv:1 ≤ h)
local notation "X0" => (fun k : ℕ => (Z k).gram 0)

-- replay the budget and interest checks of sham_k on these other Histories.
include t hm hW hv in
lemma windowWindS : Roe.WindS B (fun k => mesh (M k) R.L 0) x' h (cashU W.C) (levelQ W.C)
    K.top.width K.top.paths K.top.clip.linear K.top.clip.direct (1/2) 2 Φ Φ (fun _=>V.W.bar) X0 := by
  obtain ⟨hG,hr,_⟩ := Py.front V N0 J t
  have hA : Tendsto Aξ atTop atTop := tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp t)
  have hg := windowGray V N0 J t Sb b1 hW (lum x') (tc t) hG
  have hw := windowGray V N0 J t Sb b1 hW Aξ hA hr
  have hu : Aqua Aξ Φ := fun n => (((sizeK.powC (sizeK.Bcash R.L) n).tint
             ((dev_R R).1.low (k:=1) (by decide))).spine.comp t)
  have hh := hu.through hA hw
  have pH (k) : hat R.L (x' k) 0 = x' k := by simp [hat]
  have q1 : Mint.RangeH x' (fun k => ((Z k).gram 0).beta) (1/2) 2 := by
    refine ⟨by norm_num,by norm_num,t,Eventually.of_forall fun k => ?_⟩
    have hx := (Z k).flow.close 0 (Nat.zero_le _); rw [pH k] at hx
    refine ⟨le_trans ?_ hx.1,hx.2⟩; ring_nf; exact Eq.le rfl
  refine ⟨q1,hg,windowTend V N0 t hm,hh,Gray.thin (tc t) hh.shrinks,
     Gray.coef (tc t) _,hv,level_p _,cash_v _,K.top.clip.tail_pos, ?_, Eventually.of_forall (fun j=>?_ )⟩
  · have hh : Nonempty PlaqAxes := ⟨⟨(0,1),by decide⟩⟩
    obtain ⟨b,z,u⟩ := (V.L.mood 0).rows hh.some
    exact le_trans (tsum_nonneg b) u
  let D := Z j
  let T' := D.flow
  have hx' := T'.note.owns 0 (Nat.zero_le _)
  let he := T'.note.note 0 (Nat.zero_le _)
  have hp := D.month.boot 0
  have hy : (D.gram 0).p=D.month.a 0:=hx'.width.symm
  have hf : (D.gram 0).funds=K.top.clip:=hx'.fund.symm
  have hQ : (D.gram 0).path=V.L.path (n' j-0):=hx'.path.symm
  have ht := frostQ (he.lot_p le_rfl le_rfl) (zero_le_one.trans hv)
                 (show InterestX W.C _ (D.gram 0).J from by
                    rw [←hx'.taste]; exact (W.arm ..).sound _)
  have he := hush_h (he.lot_p le_rfl le_rfl) (zero_le_one.trans hv); rw [pH] at ht hp he
  refine ⟨hy ▸ hp.1, ht,?_ ,le_of_eq (congrArg Clip.linear hf.symm),le_of_eq (congrArg Clip.direct hf),he⟩
  change (D.gram 0).path.Bounds (D.gram 0).funds _ _ _
  rw [hf,hQ]; exact V.L.mood _

-- Restart estimates as for zα but in the larger window, under independently allowed m.
def ell (X : Side) (x b b' : ℝ) : ℝ := Graph.gainS (More X) ((Real.sqrt x)⁻¹ /4)*
     Real.exp (-stoutY (More X) x (4*((Real.sqrt x)⁻¹/4)) K.top.clip.direct
            (temp x) K.top.paths V.W.bar) *Roe.horn X b*(b'/(2*Nova.poseX)/2)
variable {KX b' vL c' l' b a' D E' C0 h1 r:ℝ}{kT d' :ℕ}
variable (P_ : Pic.Span W.pearl KX b' vL c' l' b kT) (Q : Roe.Port P_ D E' C0 h1 r d') (hX : C0 ≤ h)

include t hm hW hv P_ Q hX in
lemma windowAlpha : ∀ᶠ k in atTop,
    0 < ell V (SM k) (x' k) b b' ∧
     ell V (SM k) (x' k) b b' ≤ ‖Complex.exp (-((Z k).gram 0).v)*
                              partitionZ ((Z k).gram 0) U ((Z k).cape 0)‖ := by
  let pY := windowWindS V a p i N0 J q h R0 δ t Z Sb b1 hm hW hv
  let X (k) := (Z k).cape 0
  have hT (k) : Graph.SkinT ((Z k).gram 0) (X k) d := by
      let Z' := (Z k).flow
      let F := (Z'.roof 0).paid
      let F' : Roof _ J.k d J.n (X k) := {F with paid:=fun i=>(F.paid i).shrink J.hr.le}
      exact Mint.Stop.sage _ _ _ F' ((Z'.note.owns 0 (Nat.zero_le _)).width ▸ Z'.pole 0)
  have hx := P_.pos; have hg := P_.rP; have hw : 0 < b'/(2*Nova.poseX)/2 := by
    have h := Nova.pose_p; positivity
  filter_upwards [Roe.fog P_ pY,(Roe.costR P_ pY X (Eventually.of_forall hT) Q hX).1,
                t.eventually_gt_atTop 0] with k ⟨p,v⟩ ⟨A,G,V',x,Z',u,hk,pU⟩ t
  constructor
  · unfold ell Graph.gainS Mint.Roe.horn
    have h := Ember.pinch_pos (cell (M k) B R.L 0); positivity
  let n := cell (M k) B R.L 0
  let f := (Real.sqrt (x' k))⁻¹ /4
  let z' := X0 k
  have he : z'.beta = x' k := (Z k).flow.note.color.trans (Z k).flow.day.unit
  change Graph.gainS (More n) f*Real.exp (-stoutY (More n) z'.beta (4*f) K.top.clip.direct
                (temp (x' k)) K.top.paths V.W.bar)* Roe.horn n b ≤ _ at p
  rw [he] at p
  exact le_trans (mul_le_mul_of_nonneg_right p hw.le) hk

include P_ Q hX hv in
/-- Uniform window lemma. No n threshold. -/
lemma Window : ∀ᶠ x : ℝ in atTop, ∀ (m : Side), grainZ V W N0 x ≤ m.val →
    (m.val:ℝ) ≤ Sb * (((oYY V N0 J x).val:ℝ)^b1) →
    ∀ (n : ℕ) (X : History V a p i N0 J q h R0 δ x m n),
      0 < ell V (cell m B R.L 0) x b b' ∧
       ell V (cell m B R.L 0) x b b' ≤ ‖Complex.exp (-(X.gram 0).v)*
                      partitionZ (X.gram 0) U (X.cape 0)‖ ∧
        ∀ j ≤ n, partitionZ (X.gram j) U (X.cape j) ≠ 0 := by
  suffices he : ∀ᶠ x : ℝ in atTop, ∀ (m : Side), grainZ V W N0 x ≤ m.val →
    (m.val:ℝ) ≤ Sb * (((oYY V N0 J x).val:ℝ)^b1) →
    ∀ (n : ℕ) (X : History V a p i N0 J q h R0 δ x m n),
      0 < ell V (cell m B R.L 0) x b b' ∧
       ell V (cell m B R.L 0) x b b' ≤ ‖Complex.exp (-(X.gram 0).v)*
                      partitionZ (X.gram 0) U (X.cape 0)‖ by
     filter_upwards [he] with x H
     intro m hm hW n X
     obtain ⟨p0,h0⟩ := H m hm hW n X
     refine ⟨p0,h0,?_⟩
     intro j hj
     rw [X.flow.balance j hj, ← X.flow.balance 0 (Nat.zero_le _)]
     intro hf; rw [hf,mul_zero,norm_zero] at h0; exact p0.not_ge h0
  rw [eventually_atTop]; by_contra! hh
  choose x hX' m h1 h2 n X t' using fun k:ℕ => hh (k:ℝ)
  have hU := windowAlpha V a p i N0 J q h R0 δ
             (tendsto_atTop_mono hX' tendsto_natCast_atTop_atTop) X Sb b1 h1 h2 hv P_ Q hX
  obtain ⟨k,v⟩ := hU.exists
  exact (not_lt.mpr v.2) (t' k v.1)

end Volume
end YM.CF.Py
#print axioms YM.CF.Py.Volume.Window
#print axioms YM.CF.Py.Volume.allHistory
