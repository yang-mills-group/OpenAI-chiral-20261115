import GaugeFieldConstruction.Locators
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxSize 24000
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
local notation "Xq" s:max => Vale.hat P.R.L P.x s
structure Oak (s i :ℕ) where
 c : Side
 r : Ratio c (More (count Y s i))
 mark : clocks.Marked (Xq s) r.count P.R.L
 oddP : Odd r.count.val
 withH : 2*(r.count.val+1)< (More (count Y s i)).val
 T : Forest r
lemma trees_held : ∀ᶠ s:ℕ in atTop,∀ i:ℕ,Nonempty (Oak Y s i):=by
 filter_upwards [autumn_poses Y] with s x i; obtain ⟨c,r,h,t,k,T⟩:= x i; exact ⟨c,r,h,t,k,T.some⟩
-- retain both application: direct (44) and stokes-Clarity exposure.
structure Pantheon (s i k:ℕ) : Prop where
 support : ∃ (B:(gram Y s i k).path.Bounds (gram Y s i k).funds P.K.top.width P.K.top.paths P.V.W.bar)(Za:Attached (P.V.L.H (Y.uv k-s)) (gram Y s i k).path),
  ∀ (T:Oak Y s i), let X:= Xq s; let N:= count Y s i; let G:=gram Y s i k
  ∀ (κ τ ξ z w:ℝ)(φ: Signed → Pane N→ ℝ),
       (∀ S,Envelope (φ S)) →
       κ ≤ tauTicket P.K.top.clip G.beta X/8 → τ ≤ boldTicket P.K.top.clip G.beta X/8 →
       ξ ≤ tauTicket P.K.top.clip G.beta X/8 → z ≤ boldTicket P.K.top.clip G.beta X/8 →
       (∀ S:Signed,ModerateP B Za G.p T.T (clocks.height X) (badgeDust X) G.beta (suitCost P.R.L X) w ξ z (φ S)) →
       let F(s:Signed) (V:Pane N):= φ s (tailored T.T V)
       let Φ(x: Orbit N):= segments G.path G.funds G.p G.beta κ τ (badgeDust X) F x.1 -- sum in real numbers.
       Integrable Φ (city N) ∧ (∫ x,Φ x ∂city N) ≤ receipt_P Y s i k*Real.exp w
lemma houses_P : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤Y.uv k → Pantheon Y s i k:=by
 filter_upwards [actual_pan Y] with s H i k p; obtain ⟨B,Za,V⟩:= H i k p; constructor; refine ⟨B,Za,?_⟩
 intro T X N G κ τ ξ z w φ t u d l h p F Φ
 obtain ⟨(hh:Integrable _ (prior SU.group (More N))),hL⟩:= wind_purchase B φ (fun _=>T.T) t (receipt_P Y s i k * Real.exp w) (pZ:=fun S=> V T.r T.mark T.oddP T.withH T.T κ τ ξ z w (φ S) (t S) u d l h (p S)); let f(V:Pane N):=segments G.path G.funds G.p G.beta κ τ (badgeDust X) F V
 change Integrable f _ at hh; refine ⟨((measurePreserving_fst (μ:=prior SU.group (More N)) (ν:=depot N)).integrable_comp hh.aestronglyMeasurable).mpr hh,?_⟩
 change (∫ x:Orbit N,f x.1∂city N) ≤ _; rw [CF.Window.usesPrior _ hh]; exact hL
-- retained credit (44) thick/all path Pane. weighting grey via *broken* halo.
lemma badge_sub (q:Clip)(i:ℝ)(p:0≤ i)(L:Side): ∀ᶠ x:ℝ in atTop, ∀ β:ℝ,x/2≤β → ∀ W:Side,clocks.Marked x W L → i*21^4*(W.val:ℝ)^4 ≤ boldTicket q β x/8:=by
 let z(x:ℝ):=2*L.val*clocks.tileN x; have h:RunRate (4*gratuity) 0 (fun x=> i*21^4*z x^4):= by unfold z clocks.tileN; convert ((((RunRate.coins gratuity 0 0).cmul _).pow 4).cmul _) using 1 <;> push_cast <;> ring
 have he:0 < q.linear/16:=div_pos q.tail_pos (by norm_num)
 filter_upwards [logPrice _ _ h (w:=0) (c:=6*gratuity) (d:=2) (by norm_num [gratuity]) he,eventually_gt_atTop 0] with x u t β k w Y
 apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤ (w.val:ℝ) from Nat.cast_nonneg _) Y.2 (4:ℕ)) (show 0≤ i*21^4 by positivity)).trans (u.trans ?_); linarith only [boldTrade q _ t k]
def status_G (s i k:ℕ)(Cg:ℝ)(T:Oak Y s i)(V:Pane (count Y s i)):ℝ:=let G:= gram Y s i k; let X:= Xq s; let R:= T.r;
  -G.path.inChannels G.funds G.p G.beta V +(tauTicket P.K.top.clip G.beta X/10)*(misdemean G.p.threshold V).card + Cg*( (broken R (badgeDust X) V).card * R.count.val^4:ℕ)
lemma gauge_spike (Cg:ℝ)(wC:0 ≤ Cg): ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤Y.uv k → ∀ o:Oak Y s i,
 let N:= count Y s i
 (∫ V : Pane N, Real.exp (status_G Y s i k Cg o V) ∂prior SU.group (More N)) ≤ receipt_P Y s i k:=by
 let F:= P.K.top.clip; filter_upwards [(stage_slope P.V P.x).eventually_gt_atTop 0,(stage_slope P.V P.x).eventually (badge_sub F Cg wC P.R.L),actual_pan Y] with s u kL H i k p t N; let X:= Xq s; let U:=More N; let Q:=t.r; let K:= gram Y s i k
 obtain ⟨B,f,v⟩:= H i k p
 let μ:= prior SU.group U; let W (A: Pane N):= status_G Y s i k Cg t A; let κ:=tauTicket F K.beta X/10
 let Yq:= (fun (_:Signed) (_: Pane N)=> (0:ℝ)); let Qw:= (Q.count.val:ℝ); let b:= Cg * 21^4 * Qw^4; let T:= P.R.L
 have z(S):Envelope (Yq S):= Envelope.const _
 obtain ⟨_,_,_,hh,_⟩:=prices_plot Y s i k p; have hg:0 < K.beta:= (half_pos (show 0<X from u)).trans_le hh.1
 have he:0 ≤ tauTicket F K.beta X:=by unfold tauTicket; have ht:= F.tail_pos; positivity
 have hk:b≤ boldTicket F K.beta X/8:= kL K.beta hh.1 Q.count t.mark
 let Ω:= receipt_P Y s i k
 obtain ⟨hl,he'⟩:= wind_purchase B Yq (fun _=> t.T) z Ω (θ:=badgeDust X) (κ:=κ) (k:=b) (fun s=> by
      refine (v t.r t.mark t.oddP t.withH t.T κ b 0 0 0 (Yq s) (z s) ?_ hk ?_ ?_ ?_).trans_eq ?_
      · unfold κ; linarith only [he]
      · exact div_nonneg he (by norm_num)
      · exact (show 0≤ b from mul_nonneg (mul_nonneg wC (by positivity)) (by unfold Qw; positivity)).trans hk
      · exact moderated_vacuum B f _ _ _ _ _ le_rfl le_rfl (fun _=> le_rfl)
      simp [Ω])
 have e(A:Pane N) : W A ≤ (-K.path.inChannels K.funds K.p K.beta A) + κ* (misdemean K.p.threshold A).card + b* (misdemean (badgeDust X) A).card := by
    have hg: ((broken Q (badgeDust X) A).card:ℝ) ≤ (misdemean (badgeDust X) A).card*(21:ℝ)^4:=by exact_mod_cast broken_charge (r:=Q) (U:=A) (t:=badgeDust X); -- remove ;
    change _ + _ + Cg* _ ≤ _; apply add_le_add_right; push_cast; unfold b Qw Q; unfold Q at hg; nlinarith only [mul_le_mul_of_nonneg_left hg (show 0 ≤ Cg*(t.r.count.val:ℝ)^4 by positivity)]
 have hi: Envelope W:=by
    let L (A:Pane N):ℝ:= ∑ j:Support t.c, if broken t.r (badgeDust X) A=j then Cg* (j.card * t.r.count.val^4:ℕ) else 0
    have he:Envelope L:= Envelope.sum univ _ fun j=> Envelope.piece (p:=fun U=> broken Q (badgeDust X) U=j) (malaise_selector ..) (Envelope.const _) (Envelope.const _)
    rw [show W= fun V:Pane N=> -(K.path.inChannels K.funds K.p K.beta V)+κ* (misdemean K.p.threshold V).card + L V from ?_]; exact (((PathData.channels_env B K.p K.beta).neg.add (conduct ..)).add he)
    funext A; unfold L; rw [sum_eq_single (broken Q (badgeDust X) A),if_pos rfl]; rfl
    · intro i _ h; exact if_neg h.symm
    intro h; exact (h (mem_univ _)).elim
 refine (integral_mono (hi.exp.integrable μ) hl (fun i=> (Real.exp_monotone (e i)).trans ?_)).trans he'
 exact (add_zero ((-K.path.inChannels K.funds K.p K.beta i) + κ* (misdemean K.p.threshold i).card + b* (misdemean (badgeDust X) i).card)|>.symm ▸ season_average (p:=K.p) (U:=i) (θ:=badgeDust X) Yq (fun _=> le_rfl)) -- tune
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
