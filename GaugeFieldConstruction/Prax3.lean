import GaugeFieldConstruction.Neale3
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Oath Roots Riant
open Oath Roots Riant TableF Lenten Layout Fren
open SectorNext.Remainder.Scales Stockpile
open CoeffArc
open Scree.Ing Scree.Ing.Iona Scree.Ing.Grotto Lattice.Corona.Hive Scree.Ing.Rio
open Lor Sault Scree.Ing.Ivey Scree.Ing.Ivey.ShoreQ
variable (R: Patch)(k:ℕ)
local notation "C0"=>sizeK R.L 0
local notation "C1"=>sizeK R.L 1
local notation "C2"=>sizeK R.L 2
open XGarden XGarden.Shield XGarden.MastTin
variable {d v a E E' V ε δ g:ℝ}{j j' j0 K B N:ℕ} {D:ℝ→ℝ}
local notation "ηT"=>fun i=> low_η (radiusB i) d (temp i)
abbrev SkinE (p:ℕ)(R Z:ℝ→ℝ)(k:ℕ)(x:ℝ):ℝ:=booty4 p (radiusB x) (GrayC Z R k x)
lemma BoneE(v:0<δ)(h:C1 ηT) : Chill_v (fun i=>curve_p δ (radiusB i))∧ Chill_v ηT:=⟨Chill_v.coin (Q:=R) (wing_x0 (L:=R.L) (a:=δ/2) (by positivity) _),Chill_v.coin h⟩
lemma OtherE (d:ℝ): C1 (fun x=> low_η (radiusB x) d (temp x)) :=by
    let B:=sizeK.Bcash R.L
    have h:BoreP (fun x=>((zeroStep (radiusB x)):ℝ)):=by unfold zeroStep; push_cast; exact ((BoreP.radius_c.join BoreP.radius_c |>.join (BoreP.still 1)).self 4)
    refine (sizeK.tempo R.L).tint (?_ : sizeK R.L 0 fun x=> (Sour.SliceRoof.highCreek (radiusB x+1) (zeroStep (radiusB x)) d + 1))
    apply sizeK.accrue _ (sizeK.mild _ _); unfold Sour.SliceRoof.highCreek; simp_rw[Nat.cast_add,Nat.cast_one,div_eq_mul_inv]; -- tune
    have hz:= h.creditK R.L; have hx:C0 fun x=> 2*((radiusB x:ℝ)+1)+1:=by exact ((((B.accrue (sizeK.mild _ _)).scale _)).accrue (sizeK.mild _ _))
    exact (((hz.scale 4).tint (((hx.powC 5).scale _).tint (sizeK.mild R.L _))).scale _ |>.tint (sizeK.mild R.L _))
-- high price. before h regime ℓ.V. definition base (escort multiplier). $A/16$ near.
abbrev FocusPay(v d a c δ:ℝ)(k j L m:ℕ)(C:ℝ)(h:ℝ):= Quips (Pressure_M v d a c (3*δ) h k j C) C 8 δ m L
abbrev preΓ(C:ℝ):=8*(crestP*C)*Real.exp πBirth
lemma γRise(v d a c δ:ℝ)(k j L m:ℕ)(C:ℝ): Tendsto (FocusPay v d a c δ k j L m C) atTop (𝓝 (preΓ C)):=by
    let f(h:ℝ):= TPrice v d a c (3*δ) h k j
    have hp:Tendsto f atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num)) -- tune
    have hy:Tendsto (fun h:ℝ=> Pressure_M v d a c (3*δ) h k j C) atTop (𝓝 0):=by unfold Pressure_M; simpa only [mul_zero, add_zero, sq, f] using (((hp.const_mul 2).add (hp.pow 2)).const_mul (Real.exp (3*δ*RtHead)*7*C))
    unfold FocusPay Quips preΓ; simpa only [mul_zero,add_zero] using ((hy.const_mul (tune3 δ πBirth m L 6*8)).const_add (8*(crestP*C)*Real.exp πBirth)) -- tune
variable (C:ℝ)
-- budget maturity.Body Status.Threshold chosen by proofs $Γ$ call.bH reduces denominator. $Quips(T)$ evaluated explicit before pose. Powers.
abbrev Lei3(g:ℝ)(R:Patch)(x:ℝ):=g*QLife R x
structure PoolAge (N K L:ℕ)(x Ω ℓ m t a d0 Z δ e e' U A:ℝ)(P:BudgetPoint):Prop where
    birth:0≤ Ω ∧ Boot4 P.B Ω (Eta4 N P.B) ℓ Z (Flow4 N P.B)
    cold : let q:= advanceC ℓ (Eta4 N P.B)*Z + stolon P.B Ω (Eta4 N P.B) ℓ* Flow4 N P.B; reserveT 3 6 P.B ζd *q ≤ e ∧ reserveT 2 6 P.B ζd*q ≤ e'
    cash : PassMark P N m a t δ+ e ≤ U
    cram : PawH3 P m t a + PawF3 P m δ+e≤ A
    hot : e' ≤ U
local notation "Γp"=> Work.E01.radiusB_tendsto
structure AgeTheta (k d L:ℕ)(R:Patch)(x t h δ:ℝ)(P:BudgetPoint):Prop where
    band: Hann P k t
    paid: 0 ≤ low_η P.B h P.threshold ∧ low_η P.B h P.threshold ≤1
    enough:24 ≤ P.B
    halo : ThermalH L*P.B≤ P.B+cape_B P.B
    tip :(πBirth+16*ζd)*2*↑(Yaw.χ (ThermalH L)) ≤ (P.B:ℝ)*(δ/2)
    port : ζd*2*(Yaw.χ 0:ℝ)≤d*(δ/2)
-- birth at exact.P.Can before.Rank
open BellPrice Focus
lemma era3 (y:0<δ)(a:0<d)(p:0<v)
   (j0:ℕ)(Hk:ζd*2*(Yaw.χ 0:ℝ) ≤ j0*(δ/2)) (L:ℕ)(r:ℕ)(hb: BoreP (fun x=>temp x)) : ∀ᶠ x in atTop, ∀ (P:BudgetPoint),P.power=2→P.order=6→P.B=radiusB x→P.threshold=temp x→AgeTheta r j0 L R x v d δ P:=by
    obtain ⟨m,h⟩:= exists_nat_gt ((πBirth+16*ζd)*2*(Yaw.χ (ThermalH L):ℝ)/(δ/2))
    have hg:= ((Work.E01.radiusB_tendsto.eventually_ge_atTop (max (max m (ThermalH L)) (max (cipherK r) 24))).and (((sizeK.tempo R.L).spine.eventually (ge_mem_nhds p)).and ((OtherE R d).spine.eventually (ge_mem_nhds zero_lt_one)))) -- thermal placeholder
    filter_upwards [hg] with x s' P hP hQ hB hz; obtain ⟨c,f,t⟩:= s'; rw [←hB] at c; obtain ⟨u0,v0⟩:= max_le_iff.mp c; obtain ⟨m',T⟩:= max_le_iff.mp u0; obtain ⟨f',q⟩:=max_le_iff.mp v0; refine ⟨⟨hz.trans_le f,le_trans f' (by omega),le_trans (by decide:3≤24) q,hQ⟩,?_, q, ?_,?_,Hk⟩
    · have hx : 0 ≤ low_η P.B d P.threshold:=by unfold low_η Sour.SliceRoof.highCreek; have he:BPress.Spin.sphereRate≥0:= BPress.Spin.sphereRate_cost.positive.le; have hi:=P.threshold_pos; positivity
      exact ⟨hx,hz.symm ▸ hB.symm ▸ t⟩
    · change ThermalH L*P.B≤ P.B+P.B^3
      refine (mul_le_mul_of_nonneg_right T (Nat.zero_le _)).trans ?_; nlinarith only [show 1≤ P.B from (le_trans (by decide:1≤24) q), Nat.mul_le_mul_right (P.B^2) (show 1 ≤ P.B from le_trans (by decide:1≤24) q)] -- tune nat.
    exact ((div_lt_iff₀ (half_pos y)).mp h).le.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr m') (half_pos y|>.le))
local notation "QP"=> QLife R
local notation "AΘ"=> RamoK R.L
lemma PoolG (L r:ℕ)(Z:ℝ→ℝ)(p:Chill_v Z)(hyz:∀ᶠ x in atTop,0≤Z x)(lk m b h:ℝ)(hd:0≤lk)(w:0<δ)(v:0≤ m)(u:0≤b)(D:ℝ)(sp:b<D/16)(t:0<h) (U:ℝ)(e:k*b<U/16) : let ℓ:=Lei3 lk R; Chill_v (fun i=> SkinE 2 ℓ Z k i/QLife R i) ∧∀ᶠ x in atTop,∀ (P:BudgetPoint),P.power=2→P.order=6→P.B=radiusB x→P.threshold=temp x → PoolAge k r L x (Speedy Z ℓ k x) (ℓ x) (m*QLife R x) (low_η P.B h P.threshold) (b*QLife R x) h (Z x) δ (SkinE 3 ℓ Z k x) (SkinE 2 ℓ Z k x) (U/16*QLife R x) (D/16*QLife R x) P :=by
    intro l; let f:= fun i=> GrayC Z l k i; have hu:C1 (Lei3 lk R):= ((sizeK.main R.L).square 2|>.low (by norm_num)).scale _
    let hp:= (year SU.group R.L).eventually_gt_atTop 0
    have tQ:∀ᶠ x in atTop, 0 < QP x:= hp.mono fun x p=>pow_pos (Scales.gauge SU.group R.L p) _
    have hv:= ‹∀ᶠ x in atTop,0≤Z x›.and (tQ.mono fun x t=>mul_nonneg hd t.le)
    have ht:= ΨAc R k p hu hv (show BoreP (fun i=>l i/QP i) from (BoreP.still lk).tune (tQ.mono (fun x t=> (by rw[show l x / QP x = lk from mul_div_cancel_right₀ _ (LT.lt.ne' t)])))) -- tune lambda
    let Zt(i p:ℕ)(x:ℝ):= SkinE p l Z i x/QP x
    have hz(b:ℕ):Chill_v (Zt k b):=by unfold Zt SkinE booty4; simp_rw [mul_div_assoc (reserveT _ _ _ _)]; exact ht.leanB (vale_u ..)
    obtain ⟨X,Y⟩:=BoneE R w (OtherE R h);
    let V(x):= reserveT 3 6 (radiusB x) ζd *low_η (radiusB x) h (temp x)*m
    let W(x):= reserveT 3 6 (radiusB x) ζd*curve_p δ (radiusB x)*m
    have hv':Chill_v V:=by unfold V; simp_rw[mul_comm (_*_) m]; exact (Y.leanB (vale_u ..)).cheap _
    have hw':Chill_v W:=by unfold W; simp_rw[mul_comm (_*_) m]; exact (X.leanB (vale_u ..)).cheap _
    have hy(x:ℝ):Flow4 k (radiusB x)=Flow4 k (radiusB x):=rfl
    have hh0 : Chill_v (fun i=> W i* Flow4 k (radiusB i)):=by simp_rw [mul_comm (W _)]; exact hw'.leanB (danceNew3 k).1
    let Q:= fun i=> (k:ℝ)*V i+W i*Flow4 k (radiusB i)+Zt k 3 i; have hQψ:= (show Chill_v Q from (((hv'.cheap k).noteR hh0).noteR (hz 3))).spine_a
    have hP :Tendsto (fun i=> V i+ W i+ Zt k 3 i) atTop (𝓝 0):= ((hv'.noteR hw').noteR (hz _)).spine_a
    refine ⟨hz 2,?_⟩; filter_upwards [(BootCl R k p hu hv).2,hQψ.eventually (ge_mem_nhds (show 0 < U/16-k*b from sub_pos.mpr e)),hP.eventually (ge_mem_nhds (show 0 < D/16-b from sub_pos.mpr sp)),(hz 2).spine_a.eventually (ge_mem_nhds ((show 0≤ k*b from mul_nonneg (Nat.cast_nonneg _) u).trans_lt e)),tQ] with i s g a f w P pQ hP0 hB ht
    let Z':= Z i; let q:= QP i; let F':= SkinE 2 l Z k i; let E:=SkinE 3 l Z k i
    refine ⟨⟨s.2.2.1,hB.symm ▸ s⟩, ?_,?_,?_,(div_le_iff₀ w).mp f⟩ -- hB dep? Sig powers.
    · rw [hB]; exact ⟨le_rfl, le_rfl⟩
    · unfold PassMark PawH3 PawF3; rw[show (KeyUp P).power=3 from rfl,hP0,hB, ht]
      have hg:=mul_le_mul_of_nonneg_right (show (k:ℝ)*V i+W i*Flow4 k (radiusB i)+E/q ≤ U/16-k*b from g) w.le -- tune RHS meta
      have he:E/q * QP i=E:=div_mul_cancel₀ _ w.ne'
      rw [add_mul, he] at hg; dsimp only [V,W,E] at hg; nlinarith only [hg] -- tune
    unfold PawH3 PawF3; rw[show (KeyUp P).power=3 from rfl,hP0,hB,ht]
    have hg:=mul_le_mul_of_nonneg_right (show V i+ W i+ E/q ≤ D/16-b from a) w.le; rw[add_mul,show E/q * QP i =E from div_mul_cancel₀ _ w.ne'] at hg; dsimp only [V,W,E] at hg; nlinarith only [hg]
#print axioms PoolG
end Focus
end Pitching
end YM.CF.Py.Rate
end
