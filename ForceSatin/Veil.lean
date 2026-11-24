import ForceSatin.Hollow
import ForceSatin.CutFare
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

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip


variable {N:Side} {b C:ℝ} (c:0<b)(mail:CF.Papyrus.Franc.postage 4 b)
def veilProd {J:Type*}(A:J→Evaluation N)(L:List J): Mark N:=toMark fun x=> affineProd (fun i=> A i x) L 1
lemma veilEq {J:Type*}(A:J→Evaluation N)(L:List J): veilProd A L=(L.map fun i=>1+toMark (A i)).prod:=by
 induction L with
 | nil=> exact rfl
 | cons i L ih=> rw [List.map_cons,List.prod_cons,←ih]; funext x; unfold veilProd toMark; dsimp only; rw [SatinForce.prod_cons,one_smul]; rfl
lemma veilEnv {J:Type*} (A:J→ Evaluation N)(L:List J) (p:∀ i∈L, Envelope (toMark (A i))): Envelope (veilProd A L):=by
 rw [veilEq]
 induction L with| nil=> exact (AtSupport.oneM (n:=N) univ).env|cons i L ih=> exact env_mult (Girt.kitE (1:Mark N) (toMark _) (·+·) (by fun_prop) ((AtSupport.oneM (n:=N) univ).env) (p i List.mem_cons_self)) (ih (fun i h=>p i (List.mem_cons_of_mem _ h)))
local notation "⚝" q:max => alleyR (mateK _) q
abbrev sampler {c':Side}{r:Lattice.Ratio c' (More N)}{J:Type*}[DecidableEq J] (L:List J) (T:Tiling c' N r)(q: Wave (Single N))(A:J→Evaluation N)(σ:Signed)(U:Pane N):=
 ∑ i∈L.toFinset,(alleyR (mateK N) q (A i (pull σ 0 (T.wash U)))).re

abbrev VeilBooks (s i k m:ℕ)(τ:ℝ){J:Type*}[DecidableEq J](L:List J)(A:J→Evaluation (count Y s i))(F:ℝ):=
 L.Nodup ∧ ∃ (c':Side)(r:Lattice.Ratio c' (More (count Y s i))), coveredWidth pio (ℶ s) r ∧ ∃ T:Tiling c' (count Y s i) r, (∀ X:Pane (count Y s i),∀ i∈L,∀ j∈L, Commute (A i X) (A j X)) ∧
 ∃ q:Wave (Single (count Y s i)),Sea (FlatPaneP 4 (gram Y s i k).J.M _) q ∧ ∃ S:J→ Finset (Tulip.Single (count Y s i)), Set.PairwiseDisjoint (L.toFinset:Set J) S ∧ (∀ i∈L,Envelope (toMark (A i)) ∧ covariant (toMark (A i)) ∧ ∀ x, Credential (S i) m (pencilPrice (ℶ s)) (A i x)) ∧ (∀ σ,Milage Y s i k τ 0 F T (sampler L T q A σ))

lemma veilCommerce (m:ℕ) (rate:ℝ) (p0:0<rate)(g0:rate≤1) (c:0<b) (mail:CF.Papyrus.Franc.postage 4 b):
    ∀ᶠ s:ℕ in atTop,∀ (i k:ℕ), s≤ Y.uv k → (Y.voyage i).kick ≤ k → TiltWorld Y s i k b C → ChannelWorld Y s i k b C →
    ∀ {J:Type*} [DecidableEq J] (L:List J)(A:J→ Evaluation (count Y s i)) (G:ℝ),
    VeilBooks Y s i k m rate L A G → sites (count Y s i) ≤ L.length * poseTill (ℶ s) →
    ‖Buffered.Afterglow.Journey.compass Y i k s (veilProd A L)‖ ≤ Real.exp (G+ L.length* integralTill (ℶ s)):=by
  let B:= tiltCost * (1+b); have hb':1≤tiltCost:=Real.one_le_exp (by norm_num)
  have hb:1≤B:=one_le_mul_of_one_le_of_one_le hb' (le_add_of_nonneg_right c.le)
  obtain ⟨κ,hκ,vκ⟩:= commuted_neumann 4 (by decide)
  filter_upwards [(turnover P).eventually (form_margin (m:=m) κ B hκ.le),(turnover P).eventually distance_margin,lake_credit Y rate (outerFee (tiltRent (1+b)) C) (fun _=>0) p0 g0 (BProof.PL.const _)] with s hL hM hl i k hs e uι hm J ij L A G gB hg
  let N:= count Y s i; let n:= sites N; let l:ℝ:= L.length
  let x:= hat pio P.x s; have h:x>0:=zero_lt_one.trans_le uι.1; let δ:=parcelF x
  let U:= gram Y s i k; let Φ:= room Y s i; let q₀:=mateK N; let R:= FlatPaneP 4 U.J.M N
  let μ:=city N; let Z:=‖Buffered.vac0 P.U U Φ‖; let M:=angleFin U.J.M N 4
  obtain ⟨hR,c',r',he,Tc,rV,q,qv,d,de,hd,hq⟩:=gB
  let F:= veilProd A L
  let f(X:Pane N):=fun i:J=> A i X; let wind:= outerFee (tiltRent (1+b)) C
  have hf: RG.Envelope F:=by
    exact veilEnv A L (fun i k=>(hd i k).1)
  let Y'(y:Orbit N):=rental Y s i k U F y
  have hi:Integrable Y' μ:=Buffered.mark_integrable (roofage Y i s).bill hf ((Marks.can_read _ _ _ _ (Y.each_level i k s e hs)).smul (Complex.exp (-U.v)))
  let S:=sampler L Tc q A; have hk(y:Orbit N)(σ:Signed) : ‖Y' y‖ ≤ mountain Y wind s i k y.1*Real.exp ((3*δ*n+l*formTill x+M)+S σ (silhouette σ y.1)):=by
    obtain ⟨p,Tv⟩:= hm
    let g:=Tc.arcs y.1 σ
    obtain ⟨gV,gM,H⟩:=Tv y he Tc σ
    let F':= f y.1
    let GBlue:=f (gauge g y.1); let Bv:= S σ (silhouette σ y.1); let d':=Bv+l*formTill x
    let T:=exactShear 4 U.J.M N (by decide) p; let g':= tradew N g
    let O:=T.foldC (tailor g'); let y':= Graph.recX P.U U Φ y
    let z:= -U.path.inChannels U.funds U.p U.beta y.1+greyFee Y wind s i k y.1+3*δ*n
    have he:‖advent R O 0 y'‖≤ Real.exp z:=by
      unfold SatinForce.advent; rw [sub_zero]; apply le_trans (H 1 (by norm_num) U (δ*n) ⟨rfl,rfl,rfl,rfl,rfl⟩ (uι.2.2.1 y)) (Real.exp_monotone ?_)
      apply le_trans (sub_le_self _ _) (le_of_eq (by unfold z; ring))
      have hp:(0:ℝ)≤ U.beta:= (half_pos h).le.trans (prices_plot Y s i k hs).2.2.2.1.1
      have w₁:=P.K.top.clip.tail_pos; unfold tiltMaskFee flagCup flakes; positivity
    let dP:= pencilPrice x; let η:=curveDiscard κ x; let K:=truncateStep x; let η':=dP*B^m
    have hK:0<K:=Nat.ceil_pos.mpr (Real.rpow_pos_of_pos h _)
    have ht:0<dP:=Real.rpow_pos_of_pos h _; have hx:0≤η:=mul_nonneg (Real.exp_pos _|>.le) (Real.sqrt_nonneg _)
    let D:=curveOp x
    have hv : ‖acts (quant O.sell) (acts (affineProd F' L 1) y')‖ ≤ Real.exp d'*‖advent R O 0 y'‖:=by
      apply (occupied_layout O p F' L hR (rV y.1) m B η dP D Bv η' hb hx ht.le hL.1 ?_ _).trans
      · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; change l*_+_ + _ ≤ Bv+l*_ ; nlinarith only [mul_le_mul_of_nonneg_left hL.2 (show 0≤l by unfold l; positivity)]
      intro t w KZ
      let V:= (tilt R t).foldC T; let A':= (tilt R t).foldC (Saber p (B:=tickA N) K)
      have he(i)(_:i∈L): KZ.glow (F' i)= V.glow (GBlue i):= by
        rw [show KZ=V.foldC (tailor g') from ?_, gauge_fold]
        swap; · unfold KZ V O Shaft.foldC; congr 1; all_goals simp [mul_assoc]; rfl
        exact congrArg V.glow ((hd i ‹i ∈ L›).2.1 g (y.1,y.1)).symm
      have hv:|t|≤1:=by rw [abs_of_nonneg w.1]; exact w.2
      have hu:fiber V B:= tilt_fiber p T (exactShear_fiber 4 U.J.M N _ p mail c.le) hv
      obtain ⟨⟨c',d''⟩,φ⟩:= vκ N U.J.M K hK p t hv
      refine ⟨fun i hi=> by rw [he i hi]; exact ((hd i hi).2.2 (gauge g y.1)).glow hu hb,?_⟩
      have hk:fiber A' B:= tilt_fiber p _ (Saber_budget p _ K c.le (mail N U.J.M K p)) hv
      refine ⟨d,V,A',GBlue,(fun _=>0),q,qv,de,hu,hk,c',d'',fun j=>(φ j).trans (trunc_pay κ hκ.le x uι.1),fun j hj=> ⟨(hd j hj).2.2 (gauge g y.1),by rw [he j hj,sub_self,norm_zero]⟩,?_⟩
      change _ ≤ Bv; unfold Bv S sampler
      apply sum_le_sum; intro i hi; apply le_of_eq; rw [add_zero,← sung]; apply congrArg Complex.re
      have hk:(alleyR (mateK N) q (GBlue i))=inner ℂ (mateK N) (acts (GBlue i) q)/inner ℂ (mateK N) q:=by change (inner ℂ (mateK N) q)⁻¹*inner ℂ (mateK N) (acts (GBlue i) q)=_; rw [div_eq_mul_inv,mul_comm] -- explicit
      change _= alleyR (mateK N) q (GBlue i); unfold V; rw [Shaft.fold_use,hk,flat_price 4 U.J.M N _ p _ qv (tickB N)]; exact glow_flat_price (P:=R) p _ qv t
    change ‖inner ℂ q₀ (acts _ y')‖≤_
    let p':=acts (affineProd F' L 1) y'; have hk:inner ℂ q₀ p' = inner ℂ (acts (quant (star O.buy)) q₀) (acts (quant O.sell) p'):=by simpa only [O.glow_nil,act_one] using O.lawn q₀ p' 1
    change ‖inner ℂ q₀ p'‖≤_; rw [hk]; apply (norm_inner_le_norm ..).trans; apply le_trans (mul_le_mul (gM _ (tickB _)).le (hv.trans (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le); unfold mountain; dsimp only; change Real.exp M * _ ≤ _; rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; unfold z d' Bv; unfold U; ring_nf; exact le_rfl
  rw [Buffered.Afterglow.Journey.compass,← same_ratio,norm_div]
  change ‖∫ y,Y' y∂μ‖/Z ≤ _
  apply (div_le_div_of_nonneg_right (norm_integral_le_integral_norm Y') (norm_nonneg _)).trans
  have he:= hl i k hs c' r' he Tc G S hq (fun y=> ‖Y' y‖) (3*δ*n+l*formTill x+M) hi.norm.aestronglyMeasurable (Eventually.of_forall fun y=> ⟨norm_nonneg _,hk y⟩)
  let k':= Fineness.gaugedBase P.L U.beta (More N) (P.V.L.H (Y.uv k-s)); have hm: Real.exp (k'+M-δ*n)≤ Z:= TiltWorld.paid Y uι
  have hz: k'+x^(-yieldA)*n≤ k'+ δ*n:= by gcongr; exact Real.rpow_le_rpow_of_exponent_le uι.1 (by norm_num [yieldA,tauA,claimV,ratioV])
  apply (div_le_iff₀ ((Real.exp_pos _).trans_le hm)).2
  apply le_trans he.2; apply le_trans _ (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)
  rw [←Real.exp_add]; apply Real.exp_monotone; change k'+ x^(-yieldA)*n+G+_ ≤ _
  have hδ:0≤δ:=(Real.rpow_pos_of_pos h _).le
  change n ≤ l*poseTill x at hg; change _≤G + l*_ +_; nlinarith only [hz,mul_le_mul_of_nonneg_right hg hδ,mul_le_mul_of_nonneg_left hM (show 0≤l by unfold l; positivity)]

#print axioms veilCommerce
end Papal
end LocalLimit
end Rate
end YM.CF.Py
