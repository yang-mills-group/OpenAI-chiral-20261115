import GaugeFieldConstruction.AcrossShots
import YM.SU5.FiniteGaugeData.LocalLimit.Heat.Down

/- supplemental analytic continuity (Wave also) on one-tape canonical attics. -/

/-!
# Canonical real shot credentials with the prescribed common bare
-/
set_option autoImplicit false
noncomputable section
set_option synthInstance.maxSize 18000
set_option maxRecDepth 2600
set_option maxHeartbeats 450000
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew

namespace AcrossShots
open LayerOverlap Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x delay : ℝ} {D C R0 : ℝ → ℝ} {m m' N B : Side} {U : Grasp V.U B d}
variable {W : GivenX V U} {J : Robes N V W} {q : Chi} {z:ℝ} {P : Prescription R B} {N0 k k' l₀ : ℕ} {T : Month x 1 6 2 N0 V W}

open AcrossLands
variable {X:Cape m B R.L} (p: T.q ≤ m.val) (H:Service V U W J q h D C R0 P N0 delay)(hh:1≤h)
 {f:ℕ→ℝ} {k:ℕ}
local notation "Ω"=> mid (mesh m R.L k) B
local notation "Y"=> Actual T p X f k
variable (hp:K.top.clip.direct≤1) (a:Bon J q h D delay (Actual T p X f k))

open LocalLimit
local notation "Mr" => (Actual T p X f k)
set_option quotPrecheck false
local notation "bℓ" n:max=> (fun z=> ((Actual T p X f k).gram P z n).beta)
local notation "Γℓ" μ:max=> (Actual T p X f k).gram P μ
local notation "Mℓ" n:max=> cell m B R.L n
variable (Yh:ResponsiveService J q N0 h delay P)
variable {g:Bet k}(u0:Solved P (Actual T p X f k) 0 g)
local notation "scale₀"=>(((Γℓ g) k).beta) -- token application trouble in let-s. write
local notation "US'" => Set.Ioo (- (Branch.Rx x)) (Branch.Rx x)
variable {W0:ℝ}{s:ℕ}(A:(Set.Ioo (- (Branch.Rx x)) (Branch.Rx x))→Bet k)(w:∀ z:↥(Set.Ioo (-(Branch.Rx x)) (Branch.Rx x)), Solved P (Actual T p X f k) z.val (A z)) (he:Continuous A)
local notation "ΩBet" => ↥(Set.Ioo (- (Branch.Rx x)) (Branch.Rx x))
include H a w he
set_option linter.unusedSectionVars false
lemma floor_cont (i:ℕ): Continuous fun v : ΩBet=> (bℓ i) (A v) := Complex.continuous_re.comp ((continuous_apply _).comp he)
lemma βfloor (i:ℕ)(hi:i≤k)(v:ΩBet): enters (hat R.L x i) ((bℓ i) (A v)):= (a.beta_ok H (w v).toRealQ _ hi).2
lemma projection_floor : (fun i:ΩBet=> (Actual T p X f k).chargeLevel P (A i) k)=0:=by
 funext i; rw[Branch.chargeLevel,Branch.corr_top]; rfl
def roomStamp : Cooling P (Actual T p X f k) k (fun _ : ΩBet=>0) (fun n t=> ((Γℓ (A t)) n).beta):= {
 G:=fun n t=> (Actual T p X f k).chargeLevel P (A t) n
 v:=fun n t=> (Actual T p X f k).offset P (A t) n
 fromTop:= projection_floor p H a A w he
 fromZero:= funext fun t=> by simp [Branch.offset]
 step:=fun i hi t=> a.corr_successor H (w t).toRealQ i hi
 offsets:=fun i hi t=>by rw [Branch.offset.eq_1,dif_pos hi]
}
lemma roofStamp : Cleared W h (dleaf R.L (hat R.L x k)) (T.a k) ((Actual T p X f k).last.Q k) 0 (X k) (fun _ : ΩBet=>0) (fun i:ΩBet=>(bℓ k) (A i)) (0: ΩBet→ℂ):=by
 refine ⟨fun y _=> continuous_dens_raw y continuous_const (floor_cont p H a A w he k) (?_) (?_),fun i=>?_,0,fun i=>le_rfl⟩ -- need parens around Last
 · intro i v; exact continuous_const
 · intro i v; exact continuous_const
 rw [← show (Actual T p X f k).chargeLevel P (A i) k=0 from (congr_fun (projection_floor p H a A w he) i)]; exact (a.charged H (w i).toRealQ k le_rfl).mono (by linarith [(a.clocks k).leaf])
include hh Yh
lemma visit_lower (i:ℕ)(hi:i ≤ k) : Cleared W h (dleaf R.L (hat R.L x i)) (T.a i) ((Actual T p X f k).last.Q i) (k-i) (X i) (fun t:ΩBet=> (Actual T p X f k).chargeLevel P (A t) i) (fun t:ΩBet=>((Γℓ (A t)) i).beta) (fun t:ΩBet=> (Actual T p X f k).offset P (A t) i) := (roomStamp p H a A w he).charged H Yh a le_rfl hh (fun i hi=> ⟨floor_cont p H a A w he i,fun t=> βfloor p H a A w he i hi t⟩) (Nat.sub_self k ▸ roofStamp p H a A w he) i hi
lemma wave_floor (i:ℕ)(hi:i<k): Continuous fun v : ΩBet=> (Actual T p X f k).wave P (A v) i:= ((roomStamp p H a A w he).paid H Yh a le_rfl hh (fun i hi=> ⟨floor_cont p H a A w he i,fun t=> βfloor p H a A w he i hi t⟩) (Nat.sub_self k ▸ roofStamp p H a A w he) i hi).2.2.1
abbrev trunk_r (s:ℕ)(v:Bet k):= denZ ((Actual T p X f k).gram P v s) U (X s)
abbrev trunk_p (s:ℕ)(v:Bet k):= partitionZ ((Actual T p X f k).gram P v s) U (X s)
abbrev trunk_n (s:ℕ)(v:Bet k):= (partitionZ ((Γℓ v) s) U (X s))⁻¹ • denZ ((Γℓ v) s) U (X s)
-- declarations above include data only `Prop`. #check.
local notation "ηn" i:max t:max=> (fun y => denZ ((Γℓ (A t)) i) U (X i) y)
local notation "νn" s:max=> city (cell m B R.L s)
local notation "Υn" i:max t:max=> (partitionZ ((Γℓ (A t)) i) U (X i))
local notation "k_n" i:max t:max y:max=> (partitionZ ((Γℓ (A t)) i) U (X i))⁻¹ • (denZ ((Γℓ (A t)) i) U (X i) y)
-- l1 budgets of actual density (already at every intermediate scale; includes exp of all offsets). nonzero partition propagated under this schedule.
lemma continuum_bill (i:ℕ)(hi:i≤k) :
     (∀ᵐ y∂city (Mℓ i), Continuous (fun t:ΩBet=> denZ ((Actual T p X f k).gram P (A t) i) U (X i) y))∧
     (∀ t: ΩBet, Envelope (trunk_r (X:=X) (f:=f) p (P:=P) i (A t)))∧
      ∃ C:ℝ,0≤C∧∀ t: ΩBet,∀ y, ‖denZ ((Actual T p X f k).gram P (A t) i) U (X i) y‖ ≤ C := by
 let X0:= Actual T p X f k; let R':= (visit_lower p H hh a Yh A w he i hi); let pT:= a.can.cape i; let U':Roof (Mℓ i) J.k d J.n (X i):={pT.paid with paid:=fun x=>(pT.paid.paid x).shrink J.hr.le}; have zR:=J.gran.trans pT.size
 refine ⟨(ae_fleet (a.can.isle i)).mono fun y hy=>R'.cont y hy, fun t:ΩBet=> denInt W U' _ zR _ _ ((R'.cost t).toCost.lot _ _),?_⟩
 have hz(t:ΩBet):= (a.beta_ok H (w t).toRealQ i hi).1
 have hz0(t:ΩBet): 0≤ ((A t).read i).re∧ ((A t).read i).re ≤ 2*hat R.L x i:=by constructor <;> linarith [(hz t).1,(hz t).2,(a.clocks i).grade]
 obtain ⟨C,hc⟩:=capped_exp (X0.last.sound i) (l:=k-i) U' zR _ _ _ hh (x:=2*hat R.L x i) hz0 R'.offset (fun t=> (R'.cost t).toCost)
 exact ⟨max 0 C,le_max_left ..,fun t y=> (hc t y).trans (le_max_right ..)⟩
lemma beam_floor (i:ℕ)(hi:i≤k): Continuous fun t:ΩBet=> partitionZ ((Γℓ (A t)) i) U (X i) := by
 obtain ⟨u,e,C,h,hC⟩:=continuum_bill p H hh a Yh A w he i hi; unfold partitionZ; apply continuous_of_dominated (bound:=fun _=> C); rotate_left
 · intro x; refine Eventually.of_forall fun _=>?_ ; apply le_trans (norm_inner_le_norm (𝕜:=ℂ) _ _); rw [(tickB _).2,one_mul]; exact hC x _
 · exact integrable_const _
 · exact u.mono fun y p=> continuous_const.inner p
 intro t; apply Measurable.aestronglyMeasurable; exact (Girt.pole_w _ _ (continuous_const.inner continuous_id) (e t)).meas
lemma l1_floor (i:ℕ)(hi:i≤k)(o:ΩBet)(u:Υn i o ≠0):
  Tendsto (fun t:ΩBet=> ∫ y, ‖ k_n i t y - k_n i o y‖ ∂city (Mℓ i)) (𝓝 o) (𝓝 0):=by
 obtain ⟨p',e,C,h,hC⟩:=continuum_bill p H hh a Yh A w he i hi; let Q(t:ΩBet):= (Υn i t )⁻¹; let L:=‖Q o‖+1; let F(t:ΩBet)(y:Orbit (Mℓ i)):= k_n i t y
 have h':‖Q o‖<L:= by change ‖_‖< ‖_‖+1; linarith
 have hw(t:ΩBet)(y: Orbit (Mℓ i))(v:‖Q t‖≤ L): ‖F t y‖ ≤ L*C:=by dsimp only[F]; rw [norm_smul]; exact mul_le_mul v (hC t y) (norm_nonneg _) ((norm_nonneg _).trans (le_of_lt h'))
 have hv:ContinuousAt Q o:= (beam_floor p H hh a Yh A w he i hi).continuousAt.inv₀ u
 have hh(t:ΩBet):Measurable (F t):= (e t).meas.const_smul (Q t)
 have he:ContinuousAt (fun t=>∫ y, ‖F t y-F o y‖ ∂city (Mℓ i)) o:=by
    apply continuousAt_of_dominated (bound:=fun _=>L*C+L*C); rotate_left
    · filter_upwards [hv.norm.eventually (gt_mem_nhds h')] with t ht
      apply Eventually.of_forall; intro y; rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]; exact (norm_sub_le ..).trans (add_le_add (hw t y ht.le) (hw o y h'.le))
    · exact integrable_const _
    · exact p'.mono fun y v=> ((hv.smul (v.continuousAt)).sub_const (F o y)).norm
    exact Eventually.of_forall fun t=> ((hh t).sub (hh o)).norm.aestronglyMeasurable
 convert he.tendsto using 1; simp [F]

private lemma cap_pace (o:ΩBet)(u:∀ i≤k,Υn i o ≠0)(ε:ℝ)(b:0< ε) : ∀ᶠ v in 𝓝 o,∀ i:ℕ, i≤ k→ (∫ y, ‖k_n i v y - k_n i o y‖ ∂city (Mℓ i)) ≤ ε∧ dist (((Γℓ (A v)) i).beta) (((Γℓ (A o)) i).beta) ≤ ε ∧ (i<k→dist ((Actual T p X f k).wave P (A v) i) ((Actual T p X f k).wave P (A o) i) ≤ ε):=by
 have hz:(∀ᶠ v in 𝓝 o,∀ (i:Fin (k+1)), (∫ y, ‖k_n (i:ℕ) v y-k_n i o y‖∂city (Mℓ (i:ℕ)))≤ε ∧ dist ((bℓ i) (A v)) ((bℓ i) (A o))≤ε ∧ ((i:ℕ)<k→ dist ((Actual T p X f k).wave P (A v) i) ((Actual T p X f k).wave P (A o) i)≤ε)):=by
   apply eventually_all.mpr; intro i; have he0 : (i:ℕ) ≤ k:=by omega
   refine ((l1_floor p H hh a Yh A w he _ he0 o (u _ he0)).eventually (ge_mem_nhds b)).and ((Metric.continuousAt_iff'.1 ((floor_cont p H a A w he i).continuousAt) ε b).mono (fun t y=> y.le)|>.and ?_)
   by_cases v:(i:ℕ)<k
   · refine (Metric.continuousAt_iff'.1 ((wave_floor p H hh a Yh A w he i v).continuousAt) ε b).mono fun t p _=>p.le
   exact Eventually.of_forall fun _ p=> (v p).elim
 filter_upwards [hz] with t v i h; exact v ⟨i,Nat.lt_add_one_iff.mpr h⟩
omit A w he
/- Use membership across WHILE moving the terminal by τ. In application integrate lower estimates directly at REAL tape. -/
structure EarnTrunkSt (G:Vestal m B R.L)(F:ℕ→SpaceM) (z b ε :ℝ) (r:Bet k) : Prop where
   trueMark : RealizedAt p X P k f b z r
   debt : CreditedBet (J:=J) (f:=f) (X:=X) (q:=q) (h:=h) (P:=P) (R0:=R0) (C:=C) (D:=D) p b z r
   owes (s:ℕ) (t:s ≤ k) :
      (∫ y, ‖((partitionZ ((Γℓ r) s) U (X s))⁻¹ • denZ ((Γℓ r) s) U (X s) y) - ((partitionZ (G s) U (X s))⁻¹ • denZ (G s) U (X s) y)‖ ∂city (Mℓ s)) ≤ ε ∧
       dist (((Γℓ r) s).beta) (G s).beta ≤ ε∧ (s<k→ dist ((Actual T p X f k).wave P r s) (F s) ≤ ε)
variable (Tt:ℝ)(hx:∀ i≤k,(trunk_p p (P:=P) (X:=X) (f:=f) i g)≠0)
include u0 hp hx
lemma joint_visit (ε d:ℝ)(vε: 0<ε)(hD:0<d): ∃ r> (0:ℝ),∀ (v:ℝ), |v-(scale₀)|≤r → sharpWeight (mesh m R.L k) U (T.a k) v≠0 → ∃ τ:ℝ, |τ|≤ε ∧ ∃ b:Bet k, EarnTrunkSt (K:=K) (P:=P) (J:=J) (q:=q) (h:=h) (D:=D) (C:=C) (R0:=R0) (X:=X) (f:=f) p (Γℓ g) ((Actual T p X f k).wave P g) τ v d b:=by
 obtain ⟨Z,e,hZ⟩:= (a.posts H).solve; let S':= ball (0:ℂ) (strip (hat R.L x 0)/8)
 let A(t:ΩBet):= Z (t.val:ℂ)
 have he(t:ΩBet): (t.val:ℂ)∈ S':= by unfold S'; rw [hat_zero,mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs]; exact abs_lt.mpr ⟨t.property.1,t.property.2⟩
 have hy:Continuous A:= by apply continuous_iff_continuousAt.mpr; intro x; exact (e.continuousOn _ (he x) |>.continuousAt (isOpen_ball.mem_nhds (he x))).comp (f:=fun x:ΩBet=> (x.val:ℂ)) (by fun_prop : ContinuousAt (fun x:ΩBet=> (x.val:ℂ)) x)
 have hv(t:ΩBet): Solved P (Actual T p X f k) t.val (A t):= by obtain ⟨_,u,hP,-,g⟩:=hZ _ (he _); exact ⟨⟨u,g rfl⟩,hP⟩
 let F:= Actual T p X f k; let G:= S'; let Tκ:=Branch.Rx x; have he':0 < Tκ:= Branch.Rx_pos (a.prices _ le_rfl).grade; let o:ΩBet := ⟨0,by change 0∈Set.Ioo (-Tκ) Tκ; exact ⟨neg_lt_zero.mpr he',he'⟩⟩
 have hm: g=A o:=(hZ _ (he o)).2.2.2.1 _ u0.paid u0.fixp
 obtain ⟨b,xh,hs⟩:=Metric.mem_nhds_iff.mp (cap_pace p H hh a Yh A hv hy o (fun i hi=>hm ▸ hx i hi) d hD)
 let r:= min (min ε (Tκ/2)) (b/2); have hr:0<r:=by unfold r; exact lt_min (lt_min vε (half_pos he')) (half_pos xh)
 have hX:r<Tκ:= lt_of_le_of_lt (le_trans (min_le_left ..) (min_le_right ..)) (half_lt_self he')
 refine ⟨r/2,half_pos hr,fun v u t=>?_⟩
 obtain ⟨τ,x,hq⟩:= feasible_payment (a.posts H) (g:=Z) (fun i p=>(hZ i p).2.1) (fun i p=> (hZ i p).2.2.1) e.continuousOn r hr (hat_zero.symm ▸ hX) v (by change |v-(Z (↑(0:ℝ)) (Fin.last k)).re|≤_ ; change |v - ((g.read k).re)|≤_ at u; rw [hm,Bet.read_of_le _ le_rfl] at u; exact u)
 let v':ΩBet:=⟨τ,abs_lt.mp (x.trans_lt hX)⟩; have hb:((A v').read k).re=v:=by rw [Bet.read_of_le _ le_rfl]; exact hq
 refine ⟨τ,x.trans ((min_le_left _ _).trans (min_le_left ..)), A v',tipBalance p H hh hp a (hv v') hb t,cashSet p H hh hp a v _ (hv v') hb,fun i hi=>?_⟩
 have hh:= (hs (show v'∈ Metric.ball o b from Metric.mem_ball.mpr (by change dist τ 0< b; rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt (x.trans (min_le_right ..)) (half_lt_self xh)))) i hi; rwa[hm]
#print axioms joint_visit
end AcrossShots
end YM.CF.Py.Rate
end
