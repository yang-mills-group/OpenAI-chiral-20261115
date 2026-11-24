import ForceSatin.Chalk
set_option autoImplicit false
set_option maxHeartbeats 520000
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
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

-- **uniform** Pocket variant of WA.8 for the analytic p^C-spin stencils
variable {b C:ℝ} (c:0<b)(q':CF.Papyrus.Franc.postage 4 b) {s i k:ℕ}
local notation "ξ" => nₛ s i
local notation "φ"=> (gram Y s i k).J.M
variable (H:Real.exp 1 ≤ P.x) (w:∀ᶠ s:ℕ in atTop,∀ i k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → TiltWorld Y s i k b C) (m:ℕ)
include c q' H w
-- expose EB ancestry now (stronger variant than span_fee to preserve eligibility on path; remove outer version redundancy)
theorem span_joint : ∀ᶠ s:ℕ in atTop,∀ᶠ k:ℕ in atTop, ∀ i:ℕ, HaloTw 4 (count Y s i) → (Y.voyage i).kick ≤ k →
    ∀ d:ℝ,180^m*d ≤ pencilPrice (ℶ s) →∀ X:Ticket (nₛ s i) m d (gram Y s i k).J.M, ∀ u:ℕ,∀ (_:u+addgap (tent Y H) ≤ (nₛ s i).val) (_ : ∀ i,cows i X.S u),
    (↑(4*(u+addgap (tent Y H)):ℕ):ℝ)^4 ≤ poseTill (ℶ s) → ‖Journey.compass Y i k s (1+quietCon _ X.val)‖ ≤ Real.exp (3*integralTill (ℶ s)):=by
 filter_upwards [pureCommerce Y c q' m,(turnover P).eventually_gt_atTop 0,w] with s Ple e g
 let x:= pencilPrice (ℶ s); let D:= integralTill (ℶ s); have hD:0<D:= Real.rpow_pos_of_pos e _
 filter_upwards [Journey.circumvol Y s (x * LocalLimit.postage P.block P.R.L s) D hD] with k z i hi v' d h X u Q V αu
 specialize z i v'
 let v:=z.1
 apply Ticket.switched (solder Y i k v' s) (Journey.compass Y i k s) D (terrain Y H (Y.ir i) s).symm hi (revive Y H _ _ _ v) hD X x (ℶ s) (fun F E f=>?_) (fun L h' p=>?_) u Q αu V h
 · apply z.2 _ E; intro i'; apply (f i').trans_eq; apply congrArg Real.exp
   rw [show sites (P.Ctor (Y.ir i) s)=_ from sites_postage .., ←mul_assoc]
 · simpa [D] using Ple i k v.enters v.depth (g i k v.depth v.enters) _ _ _ _ (Ticket.chess_books Y L p h) (show sites (nₛ s i) ≤ _ from by simpa using h')

omit c q' H w
abbrev palmCo (x:ℝ):= x^(0.4*micr)
abbrev wane (x:ℝ):= x^(-(2.5*micr))
lemma wane_late (b:ℝ) : ∀ᶠ x:ℝ in atTop, 3*integralTill x≤1 ∧ 6*integralTill x ≤ forceDose x * wane x ∧
    (180:ℝ)^m*(forceDose x*(palmCo x+(180^m*palmCo x)*(1+b)^m)) ≤ pencilPrice x:=by
  let h:ℝ:= -(53.5*micr); have he(c:ℝ):Grade h (fun x=>c*integralTill x):= Grade.scaleB c (Grade.pitch _)
  let f:= fun x=> forceDose x; let v:= fun x=> palmCo x; have hp:Grade (0.4*micr) v:=Grade.pitch _
  have hr:Grade (-(50*micr)) f:=Grade.pitch _
  let W(x):=(180:ℝ)^m*(forceDose x*(v x+(180^m*v x)*(1+b)^m))
  have hw: Grade (-(50*micr)+(0.4*micr)) W:= Grade.scaleB _ (hr.mul (hp.plus (by simpa only [add_zero] using (Grade.scaleB ((180:ℝ)^m) hp).mul (Grade.block ((1+b)^m)))))
  filter_upwards [eventually_gt_atTop (0:ℝ),((he 3).roots (by norm_num [h,micr])).eventually (ge_mem_nhds zero_lt_one),(he 6).cost_p (b:=-(50*micr) + -(2.5*micr)) (by norm_num [h,micr]),hw.cost_p (b:=-(49.5*micr)) (by norm_num [micr])] with x p h e v'
  exact ⟨h,((le_abs_self _).trans e).trans_eq (Real.rpow_add p _ _),(le_abs_self _).trans v'⟩
lemma secant {t:ℝ}(p:0<t)(x:ℂ): ∃ z:ℂ, ‖z‖=t ∧ z*x=↑(t*‖x‖):=by
 by_cases h:x=0; · subst x; exact ⟨t,by simp [p.le],by simp⟩
 have hg:0<(t*‖x‖):= mul_pos p (norm_pos_iff.mpr h); refine ⟨(↑(t*‖x‖):ℂ)/x,?_,div_mul_cancel₀ _ h⟩; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hg.le,mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h)]

include q' c in
lemma palmPrice {N:Side}{M:Tulip.Male}{X:FC (Single N)}{S:Support (More N)}{a:ℝ}{q:Wave (Single N)}(h:Street S m a X)(u:IsStarProjection (FlatPaneP 4 M N))(v:Sea (FlatPaneP 4 M N) q): ‖alleyR (mateK N) q X‖ ≤ (180^m*a)*(1+b)^m:=by
 have he:alleyR (mateK N) q X= inner ℂ (mateK N) (acts X q)/inner ℂ (mateK N) q:=by change (inner ℂ (mateK N) q)⁻¹*inner ℂ (mateK N) (acts X q)=_; rw [div_eq_mul_inv,mul_comm]
 rw [he,flat_price 4 M N (by decide) u X v (tickB N)]
 let A:= (exactShear 4 M N (by decide) u).glow X
 apply (norm_inner_le_norm ..).trans; rw [v.2,one_mul]; apply (Graph.spentS _ A q).trans; rw [v.2,mul_one]; exact h.harvest.glow (exactShear_fiber 4 M N (by decide) u q' c.le) (le_add_of_nonneg_right c.le)

lemma affine_sharp (X:FC (Single (count Y s i))) {S:Support (More (count Y s i))} (h:AtSupport false S (quietCon _ X))(d z:ℂ) (p:Ferry Y s i k) :
 Journey.compass Y i k s (1+ z • (quietCon _ X+(-d) • 1))=1+z*(Journey.compass Y i k s (quietCon _ X)-d):=by
 let F:=Journey.compass Y i k s; have hf(X A:Mark ξ)(v:Envelope X)(w:Envelope A) : F (X+A)=F X+F A:=by
   unfold F Journey.compass; rw [mark_add (roofage _ _ _).bill v w (Marks.can_read _ _ _ _ (Y.each_level i k s p.depth p.enters)),add_div] -- use hP avoiding Y shadow
 have hv(x:Mark ξ)(c:ℂ):F (c • x)= c*F x:=by unfold F Journey.compass; rw [mark_smul,mul_div_assoc]
 have he: F 1=1:=by unfold F Journey.compass; rw [markvac]; exact div_self (Y.each_level i k s p.depth p.enters|>.valid)
 have h1:= AtSupport.oneM (n:=count Y s i) S; change F (1+ _)=1+z*(F _-d); rw [hf _ _ h1.env (((h.addM (h1.smulM _)).smulM _).env),hv,hf _ _ h.env (h1.smulM _).env,hv,he,mul_one, sub_eq_add_neg]

include c q' H w
lemma pencil_custody : ∀ᶠ s:ℕ in atTop,∀ᶠ k:ℕ in atTop, ∀ i:ℕ, HaloTw 4 (count Y s i) → (Y.voyage i).kick ≤ k →
    let v:=count Y s i; let M:=(gram Y s i k).J.M; let x:=ℶ s
    ∀ (S:Support (More v)) (X:FC (Single v)) (_:AtSupport false S (quietCon _ X)) (_:covariant (quietCon _ X)), Street S m (palmCo x) X →
    ∀ u:ℕ,∀ (_:u+addgap (tent Y H)≤v.val) (_:∀ i,cows i S u), (↑(4*(u+addgap (tent Y H)):ℕ):ℝ)^4≤poseTill x → ∀ q:Wave (Single v), Sea (FlatPaneP 4 M v) q → ‖Journey.compass Y i k s (quietCon v X)-alleyR (mateK v) q X‖ ≤ wane x:=by
 filter_upwards [span_joint Y c q' H w m,(turnover P).eventually (wane_late m b),(turnover P).eventually_gt_atTop 0] with s h p e
 filter_upwards [h,ferry_all Y s] with k h v i t hi N M x S X hS hG hP u g C₁ V q hg
 let d:=alleyR (mateK N) q X; let R:= X+ (-d) • 1; let β:=palmCo x; let κ:=(180^m*β)*(1+b)^m
 have hs:=spar_fit (M:=M) t.1; have hv:‖d‖≤κ:=palmPrice c q' m hP hs hg
 let D:=forceDose x; have hD:0<D:=Real.rpow_pos_of_pos e _; let F:=Journey.compass Y i k s
 let Y':= quietCon N X; let z0:= F Y'-d; obtain ⟨z,W,wz⟩:= secant hD z0
 have ht: Street S m (D*(β+κ)) (z • R):=by rw [←W]; exact Street.scale z (Street.add hP (Street.enlarge (by simpa using hv) (Nat.zero_le _) (Street.scale (-d) Street.one)))
 let gF:= z • (Y'+(-d) • 1)
 have hc: AtSupport false S gF:= (hS.addM ((AtSupport.oneM _).smulM _)).smulM _
 have hl: covariant gF:= by intro i v; have ht:= hG i v; change z • (X+(-d) • 1) = twist _ (z • R); unfold R; change X= _ at ht; rw [twist_scalar,map_add,twist_scalar,map_one]; exact congrArg _ (congrArg (· + (-d) • (1:FC (Single N))) ht)
 have hq: fixedSeaMean M (z • R) 0:=by
   apply sea_mean.mpr; intro w t0; rw [alley_match hs t0 hg]; unfold R
   have ht: alleyR (mateK N) q 1=1:=by change (inner ℂ (mateK N) q)⁻¹*inner ℂ (mateK N) (acts 1 q)=_; rw [act_one]; exact inv_mul_cancel₀ (norm_pos_iff.mp ((Real.exp_pos _).trans_le (flat_overlap 4 M N q (mateK N) hg (tickB N) (by decide) hs|>.ge)))
   rw [map_smul,map_add,map_smul,ht]; unfold d; simp
 let A:Ticket N m (D*(β+κ)) M:= ⟨S,z • R,hc,hl,ht,hq⟩
 let B:=integralTill x; have hb:B>0:= Real.rpow_pos_of_pos e _
 have he:1+D*‖z0‖≤Real.exp (3*B):=by
    have hk:= h i t hi _ p.2.2 A u g C₁ V
    rw [show (1:ℝ)+D*‖z0‖= ‖(↑(1+D*‖z0‖):ℂ)‖ from ?_ ]; swap; · rw [Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [Complex.ofReal_add,Complex.ofReal_one,←wz, show (1+z*z0)=_ from (affine_sharp Y _ hS d z (v i hi)).symm]; exact hk
 apply le_of_mul_le_mul_left _ hD
 have hx : |Real.exp (3*B)-1|≤ 2*(3*B):=by simpa [abs_of_nonneg (show 0≤3*B by positivity)] using Real.abs_exp_sub_one_le (x:=3*B) (by rw [abs_of_nonneg (by positivity)]; exact p.1)
 change D * ‖z0‖ ≤ D * wane x; linarith only [he,(abs_le.mp hx).2,show 6*B≤ D * wane x from p.2.1]
#print axioms pencil_custody
end Papal
end LocalLimit
end Rate
end YM.CF.Py
