import Organdy.Vitreous
import Organdy.Rare
import SatinThinCrest
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/

open Regis Lamour.Bridge Organdy Organdy.Optic
namespace Bazaar
open Larva (Chip Domaine dint)

open Papal Celeste Clock Hookah Rake Cliplet
local notation "θx" s:max=>hat P.R.L P.x s
local notation "N" s:max i:max=> (Journey.side Y i s)
local notation "ℰ" s:max=> meterC (θx s)
set_option linter.unusedVariables false
set_option maxRecDepth 4000
variable {v b ζ:ℝ}
 (Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s≤Y.uv k→ ShelterCost v Y s i k)
 (c:0<ζ)
include Z c

lemma thistle:
   ∀ᶠ s in atTop, ∀ᶠ i in atTop, ∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k →
      let x:=θx s; ∀ (a:ℝ), |a| ≤ knock x → ∀ (l:ℕ) (W:Pane (N s i)→ℂ)
       (A:Organdy.Ink (Chip (More (N s i)))) (z:Seat (N s i)),
       Domaine l ζ (temp x) (stow x) b W A → ∀(L:List (Hookah (N s i))),
         Rake.Sown W z l x a 0 L →
       ‖Journey.compass Y i k s (Hookah.buffet L)‖ ≤ Real.exp (14*(ℰ s)*sites (N s i)+ L.length*(a*parallax Y s i k A z+toll x)) :=by
 filter_upwards [offer Y ζ b c,Z,(turnover P).eventually (dock_v gaugeRules b c)] with s p q g
 filter_upwards [q] with i u k hz hk x a h l W A z t L χ
 obtain ⟨D,Q,r,m,n⟩:=Rake.Sown.pollen t g h χ
 let c:= u k hz hk
 have hx:= marketPack Y s i k c hz χ.occupy.env (nectarine t g z D).1 Q (Eventually.of_forall (fun i=>m (i.1,_))) n
    (p _ _ hk a h _ _ c.load.ready c.load.willing z D l W A r t)
 refine hx.trans_eq ?_
 congr 1
 rw [Fintype.card_fin]
 unfold Optic.toll x
 ring

variable (H:Real.exp 1≤ P.x)
include H
lemma thistle_paid:
   ∀ᶠ s in atTop, ∀ᶠ i in atTop, ∀ᶠ k in atTop,
     let x:=θx s; ∀ (l:ℕ)(W:Pane (N s i)→ℂ)
       (A:Organdy.Ink (Chip (More (N s i)))) (z:Seat (N s i)),
       Domaine l ζ (temp x) (stow x) b W A → (∀ y,cows y (Lattice.halo 0 (hatch l z)) (walkF x)) →
        ∀ (a:ℝ), |a| ≤ knock x →
       ‖Journey.compass Y i k s (1+(a:ℂ) • markPair x W z)‖ ≤ Real.exp (a*parallax Y s i k A z+toll x+3*yieldt x):=by
 let K:= tent Y H
 filter_upwards [(turnover P).eventually (funded (addgap K)),
   thistle (b:=b) Y Z c,
   (turnover P).eventually (dock_v gaugeRules b c)] with s ho hr hl
 let x:=θx s
 let g:=walkF x
 filter_upwards [hr,(count_grows Y s).eventually_ge_atTop (g+addgap K)] with i hf hX
 let N':=side Y i s; let B':=4*(g+addgap K)
 let ψ:= -(knock x*(b*clipper x)^2)
 let M:=Rake.portrait x
 let u₀:= yieldt x
 have hp:0<u₀:= BProof.coin_pos ..
 let D:= (More N').val ^ 4; let U:=Real.exp u₀
 have ht:M≥1:= portfolio x
 have hM:0<M:=zero_lt_one.trans_le ht; let E:= min 1 (Real.exp ψ); have hv:0<E:=lt_min one_pos (Real.exp_pos _); let g':= ((U-1)* E^D)/M^D; have he:1<U:=Real.one_lt_exp_iff.mpr hp; have hz:0<U-1:=sub_pos.mpr he; have hg:0<g':=by unfold g'; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y g' hg s] with k X V
 intro _ l w A z h t a pA
 let A':=zoopN l x w z a
 have D':Broach w z l x a A' := zoom (atHome h hl _)
 obtain ⟨T,t',h₀,h₁,h₃,e⟩:= Rake.trifecta (p₀:=0) (revive Y H s i k X) (terrain Y H (Y.ir i) s).symm (show g+addgap K≤ N'.val from hX) _ D' t
 let n:=T.length
 let x':= a*parallax Y s i k A z+Optic.toll x
 let y:=Real.exp (x'+u₀)
 have hy : ψ≤x':=faceup x b (monetary_lid _ _ _ _ _ _ z h.purse) pA
 have hy': E≤y:=min_le_right .. |>.trans (Real.exp_monotone (hy.trans (le_add_of_nonneg_right hp.le)))
 have y0:0<y:=Real.exp_pos _
 let F:= Journey.compass Y i k s;
 let F':= solder Y i k X.depth s; let W:= Hookah.buffet T; have hF:‖F W‖≤ y^n:=by
    refine (hf k X.depth X.enters a pA _ _ A _ h T t').trans ?_; rw [←Real.exp_nat_mul]; apply Real.exp_monotone; have ht: sites N' ≤ (n:ℝ)*(B':ℝ)^4:=by unfold sites; exact_mod_cast h₃
    have he: 14 * (ℰ s)*sites N' ≤ u₀*n:=by
       refine (mul_le_mul_of_nonneg_left ht (mul_nonneg (by norm_num) (BProof.coin_pos ..|>.le))).trans ((mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg (α:=ℝ) n)).trans' (Eq.le ?_)|>.trans_eq (mul_comm ..)); unfold B'; push_cast; ring
    change 14* _*_ + (n:ℝ)*x'≤(n:ℝ)*(x'+u₀); linarith only [he]
 have ha(c:ℕ)(t:c≤D)(v:Mark N')(H:Envelope v)(u:∀ x,‖v x‖≤ M^D): ‖F v-F' v‖ ≤ (U-1)* y^c:= by
    apply (V i X.depth v (M^D) H u).trans; unfold g'; rw [div_mul_cancel₀ _ (pow_pos hM _).ne']; exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hv.le (min_le_left ..) t).trans (pow_le_pow_left₀ hv.le hy' _)) hz.le
 change n≤D at h₁; change 1≤n at h₀
 have heP: ‖F W-F' W‖ ≤ (U-1)*y^n:= ha n h₁ _ t'.occupy.env (fun j=>by apply (t'.rain h hl pA j).trans; exact pow_le_pow_right₀ ht h₁); change ‖F' A'.x‖^n≤ ‖F' W‖ at e
 have hu : ‖F' A'.x‖≤ U*y:=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by unfold U; positivity) (by omega:n≠0)).1; rw [mul_pow]; refine (e.trans ((norm_sub_rev (F' W) (F W)) ▸ (norm_le_norm_sub_add (F' W) (F W)))).trans ?_
    refine (le_trans (add_le_add heP hF) ((show U ≤ U^n from by simpa only [pow_one] using (pow_le_pow_right₀ (a:=U) ‹1<U›.le h₀)) |> (fun g=> (mul_le_mul_of_nonneg_right g (pow_nonneg y0.le n)).trans' (le_of_eq (by ring)))))
 have hh: ‖F A'.x -F' A'.x‖≤ (U-1)*y:=by
    refine (ha 1 (Nat.le_trans h₀ h₁) _ D'.owner.env (fun j=> ?_)).trans_eq (by rw [pow_one]); have hx := D'.early h hl pA j; apply hx.trans; change M≤ M^D; exact (by simpa only [pow_one] using (pow_le_pow_right₀ ht (Nat.le_trans h₀ h₁)))
 apply (norm_le_norm_sub_add (F A'.x) (F' A'.x)).trans ((add_le_add hh hu).trans ?_)
 change _≤ Real.exp (x'+3*u₀); rw [show x'+3*u₀= u₀+(u₀+(x'+u₀)) from (by ring),Real.exp_add (u₀) (u₀+_),Real.exp_add (u₀)]; change _ ≤ U*(U*y); nlinarith only [mul_nonneg (sq_nonneg (U-1)) y0.le]

omit H Z c in
lemma tilt {s i k:ℕ} (f:Ferry Y s i k) {L:Mark (N s i)} {S:Finset (Seat (N s i))}
 (p:AtSupport false S L) (a:ℝ) :
 Journey.compass Y i k s (1 + (a:ℂ) • L) = 1+(a:ℂ)*Journey.compass Y i k s L:=by
 unfold Journey.compass
 rw [mark_add (roofage Y i s).bill (AtSupport.oneM S).env (p.smulM a).env (Marks.can_read _ _ _ _ (Y.each_level i k s f.depth f.enters)),
     mark_smul,add_div,markvac,mul_div_assoc]; congr 1; exact div_self (part_here Y i s k f)

lemma seaworthy:
   ∀ᶠ s in atTop, ∀ᶠ i in atTop, ∀ᶠ k in atTop,
     let x:=θx s; ∀ (l:ℕ)(W:Pane (N s i)→ℂ)
       (A:Organdy.Ink (Chip (More (N s i)))) (z:Seat (N s i)),
       Domaine l ζ (temp x) (stow x) b W A → (∀ y,cows y (Lattice.halo 0 (hatch l z)) (walkF x)) →
       |(Journey.compass Y i k s (markPair x W z)).re - parallax Y s i k A z|≤lakeZ x:=by

 filter_upwards [
   thistle_paid (b:=b) Y Z c H,
   (turnover P).eventually (dock_v gaugeRules b c),
   (turnover P).eventually (virgin b)] with s q p t
 filter_upwards [q] with i v
 filter_upwards [v,ferry_later Y s i] with k m n x l W A z F L
 refine Virgin.stable t (monetary_lid _ _ _ _ _ _ z F.purse) ?_
 intro a r
 have p':=m _ _ _ z F L a r
 rw [tilt Y n (atHome F p z) a] at p'
 refine le_trans ?_ ((Complex.re_le_norm _).trans p')
 simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im, zero_mul, sub_zero]; exact le_rfl
