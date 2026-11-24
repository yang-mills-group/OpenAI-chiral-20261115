import ForceSatin.HomeTilt
import ForceSatin.ExactShear
import Verses.Glare

/-! Occupation tax on the Born numerator, *before* all the checker insertions.
Sparse grey-book variant of F1 / WA.1 on the actual Orbit.
Uses the existent LusterS sparse gauge purchase. Indices, footprints and
maturities use the construction notes convention. Unlike a fixed-loss L^1 in the Fock sector,
keep the excitation tilt through a full unit *in addition to* exact flat normalization.
Context and accounting and some proof scripts adapted from
Verses.Culinary & CellQ.Donate. No Sector/Divergence/Rotation assumptions.
-/
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
lemma count_room (q:ℕ) : ∀ᶠ s:ℕ in atTop, ∀ i:ℕ, q ≤ radiusB (ℶ s) ∧ radiusB (ℶ s) ≤ (count Y s i).val := by
 filter_upwards [cap_physic Y,(turnover P).eventually block_bill, (turnover P).eventually (Work.E08.eventual_radiusB q)] with s hs h0 ht i
 obtain ⟨w,h₀,h₁,L,r,hc,hu⟩:=hs i
 refine ⟨ht,?_⟩; have hv:radiusB (ℶ s)+1≤w:= (h0 w 0 h₀).2
 change 2*(w+1)<(count Y s i).val*2 at hu; omega

-- from Verses.Shade, strengthening binder order. This is a pointwise
-- cost on existence of a gauge; the gauge need not be chosen measurably.

set_option maxHeartbeats 1250000
lemma sloop_project_every {a C δ:ℝ}(p:P.d≤δ)(h:0<a)(v:0<C)(hg:0<δ)(H:∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val→Sow 4 N a C δ)(K:ℝ)(s0:0<K):∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k →
    let U:= room Y s i; let N:=count Y s i; let R:=gram Y s i k; let x:= ℶ s; let A:=spar 4 R.J.M; let Z:=A (1:Pane N)
    IsStarProjection Z ∧ ∀ y:Orbit N,let S:=A (U y); ∃ l: Seat N→SU.E, let Q:= twist (tradew N l) S; IsStarProjection S ∧ condor S C ∧ (K*K+1)*entryBudget (Q-Z) ≤ parcelF x * sites N + ((walls pio x:ℕ):ℝ)^4 * flakes (sax x) y.1 :=by
 let f:= ((K^2+1)*(C*2*180))
 obtain ⟨n₀,v₀⟩:=H.exists
 have hh:=grade_order pio a C δ h
 have hk:= Grade.plus ((hh.scaleB ((K*K+1)*180)).grow (b:=-marginV) (by norm_num [marginV,ratioV,tauA])) ((Grade.pitch (-marginV)).scaleB f)
 filter_upwards [cap_physic Y,(turnover P).eventually ((block_bill.and (metro_budget P.J.n pio f)).and gain_a), (turnover P).eventually_ge_atTop 1, (turnover P).eventually ((sax_b.roots (by norm_num [tauA])).eventually (ge_mem_nhds P.J.ht)),(turnover P).eventually (hk.cost_p (b:=-claimV) (by norm_num [claimV,ratioV,marginV,tauA])), count_room Y n₀] with s Hs hz he he' hx HQ
 intros i k tE U N R x A Z
 have e:Sow 4 N a C δ:=v₀ N ((HQ i).1.trans (HQ i).2)
 let T:=P.U.broadness N (P.J.gran.trans ((Y.voyage i).ownership s).size) R.J.M
 obtain ⟨w,h₀,h₁,L',r,hc,hu⟩:=Hs i
 obtain ⟨⟨bW,ψ⟩,G⟩:=hz
 let d:=radiusB x; let j:= w-(d+1)
 obtain ⟨hm,hf⟩:= bW w j h₀; have hr:j+d+1=w:=by change d+1 ≤ w at hf; unfold j; omega
 have hw:w ≤wallsF pio x:= (show w≤2*w+1 by omega).trans h₁
 have hT: Sparkle N P.d R.J.M 4:=by rw [←P.kJ]; exact T
 exact sl_prelude pio v s0 U P.J.k P.d P.J.n (roofage Y i s) x R.J.M p P.dpos.le h hg e hT w d rfl hw r hc hu j hr (hm hr) he' G ψ ((le_abs_self _).trans hx)

open Pannier

def mixedMatrixFee (b : ℝ) := tiltCost * ((1+b) * 180)

lemma tilt_mile {N: Side} {h B C w : ℝ} {Z : Op (Single N)} (R : GramM N) (V : Loom N) (y : Orbit N)
    (z : Z = spar 4 R.J.M (V y)) (L : Shaft (Single N)) (p : IsStarProjection Z) (hc : condor Z C)
    (c : fiber L B) (d : 0≤B) (e : 0≤C) (hB : B*(1+C)≤h)
    (hg : tier h (R.board y).val ≤ Real.exp w) :
    ‖L.glow (Graph.mile 4 R V y)‖ ≤ Real.exp (‖Pec.pigment R.J.I (V y)‖ + w +
      (B^2*((1+C)*C))*entryBudget (R.J.P.den (V y))) := by
  let D := R.J.P.den (V y)
  have hm : entryBudget ((1-Z)*D*Z) ≤ (1+C)*C*entryBudget D := by
    rw [mul_assoc]; exact (condor_budget _ _ (condor_one_sub _ hc)).trans
      ((mul_le_mul_of_nonneg_left (condor_right Z D (by rw [p.isSelfAdjoint]; exact hc)) (by positivity:0≤1+C)).trans_eq (mul_assoc _ _ _).symm)
  let E := B^2*((1+C)*C)*entryBudget D
  have hu : ‖L.glow (exp (dg ((1-Z)*D*Z)))‖ ≤ Real.exp E := by
    rw [glow_thermal]; apply (Graph.bootC _).trans (Real.exp_monotone ?_)
    change _ ≤ E
    exact (glow_dg L c d _).trans ((mul_le_mul_of_nonneg_left hm (sq_nonneg B)).trans_eq (mul_assoc ..).symm)
  have hv : ‖L.glow (tank Z (R.board y))‖≤ Real.exp w := by
    apply (tank_glow L Z h 0 ∅ _ (show 0≤h from (mul_nonneg d (by positivity)).trans hB) (le_refl _) ?_).trans
    · simp_rw [zero_mul,Real.exp_zero,mul_one]; exact hg
    intro i; simp only [notMem_empty,↓reduceIte,mul_one]; exact (price_saber p L c C hc e d i).trans hB
  let z' := Pec.pigment R.J.I (V y)
  have ht : ‖Complex.exp (-z')‖≤ Real.exp ‖z'‖ := by simpa using Complex.norm_exp_le_exp_norm (-z')
  unfold Graph.mile Graph.actF Kennel.capT
  rw [←z,Real.exp_add,Real.exp_add,L.glow_free,L.glow_mult,norm_smul,mul_assoc (Real.exp ‖Pec.pigment R.J.I (V y)‖)]
  exact mul_le_mul ht ((norm_mul_le ..).trans (mul_le_mul hv hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le

lemma tilt_action {I:Type}[LinearOrder I][Fintype I](P:Op I)(p:IsStarProjection P)(T:Shaft I)(t:ℝ)
    (A:FC I)(x:Wave I) :
    let f y:=acts (grow (excitation P) t) (acts (quant T.sell) y)
    f (acts A x) = acts (((tilt P t).foldC T).glow A) (f x) := by
  intro f; unfold f
  rw [tilt_quant_exp p]
  simp only [acts_scalar, ContinuousLinearMap.map_smul_of_tower]
  let L := (tilt P t).foldC T
  congr 1
  change acts (quant _) (acts (quant T.sell) _) = acts (L.glow A) (acts (quant (grow _ _)) (acts (quant T.sell) x))
  rw [←act_mul (quant (grow _ _)),←act_mul (quant (grow _ _)),←quant_mul]
  change acts (quant L.sell) (acts A x) = acts (L.glow A) (acts (quant L.sell) x)
  rw [←act_mul, ←act_mul, Shaft.glow,mul_assoc (quant L.sell * A), ←quant_mul,L.pay,quant_one,mul_one]

/-- sparse, same argument as G. Compare F1. We pay globally for *all* (strict)
    defect faces and may recover half that weight in F2. -/
def tiltMaskFee (N : Side) (k : Clip) (G : GramM N) (U : Pane N) :=
  flagCup G.p k G.beta/2 * flakes G.p.threshold U

/-- A pointwise simultaneous estimate using *one* lifted g in all tilts & queries.
    Interested, path, beta, funds, p of sharp gram must be unchanged. -/
def TiltAccount (s i k:ℕ) (b C:ℝ) : Prop :=
  let V := room Y s i; let A := gram Y s i k; let N:=count Y s i
  let S:= FlatPaneP 4 A.J.M N
  let x := ℶ s
  ∃ p : IsStarProjection S, ∀ y:Orbit N, ∃ l:Seat N→SU.E,
    let g:= ((exactShear 4 A.J.M N (by decide) p).foldC (tailor (tradew N l)))
    (fiber g ((1+b)*180) ∧ condor (spar 4 A.J.M (V y)) C) ∧
    (∀ w, Sea (tickA N) w → ‖acts (quant (star g.buy)) w‖=Real.exp (angleFin A.J.M N 4)) ∧
    ∀ t:ℝ, |t| ≤ 1 → ∀ R w, ProperT A R → tier P.h (R.board y).val ≤ Real.exp w →
      ‖acts (grow (excitation S) t) (acts (quant g.sell) (Graph.recX P.U R V y))‖ ≤
        Real.exp (- A.path.inChannels A.funds A.p A.beta y.1 + greyFee Y 1 s i k y.1 +
          w+ 2 * parcelF x*sites N - tiltMaskFee N P.K.top.clip A y.1)


lemma earnsTilt {δ C a b:ℝ} (p:P.d≤δ)(hs:0<δ)(v:0<C)(c:0<b)(h:0<a)
    (E:∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val → Sow 4 N a C δ)(f:CF.Papyrus.Franc.postage 4 b)
    (Z:mixedMatrixFee b*(1+C) ≤ P.h) : ∀ᶠ s in atTop, ∀ i k:ℕ,s ≤ Y.uv k → TiltAccount Y s i k b C := by
  let W:= tiltRent (1+b)
  let T:= mixedMatrixFee b
  let u:= T^2*((1+C)*C)
  have hu:0≤u:=by unfold u; positivity
  have hT:0≤T:=by unfold T mixedMatrixFee tiltCost; positivity
  have hW:0<W:=by unfold W tiltRent; positivity
  filter_upwards [sloop_project_every Y p h v hs E W hW, (turnover P).eventually (VelvetC.hunt_γ
      (r:=P.J.n) (t:=P.d) u hu (level_p P.W.C) (cash_v P.W.C) P.J.ht P.K.top.clip),
    count_room Y 0,(turnover P).eventually_ge_atTop 1] with s he hm ht hx i k e
  let x:=ℶ s
  let U:= gram Y s i k; let V:=room Y s i; let N:=count Y s i; let d:=parcelF x
  let n:=sites N; let L:= P.K.top.clip
  have hN:0≤n:=zero_le_one.trans (sites_pos _)
  let S':= FlatPaneP 4 U.J.M N
  obtain ⟨hp,H⟩ := he i k e
  have hS:IsStarProjection S':= hp
  unfold TiltAccount
  dsimp only
  refine ⟨hp,?_⟩
  intro y
  obtain ⟨g,gp,gc,yG⟩ := H y
  let F:=tradew N g; let G:=exactShear 4 U.J.M N (by decide) hS; let X:=G.foldC (tailor F)
  let S:=spar 4 U.J.M (V y)
  have hG:fiber G (1+b):= exactShear_fiber 4 U.J.M N (by decide) hS f c.le
  have b1:0≤1+b:=by positivity
  have hX:fiber X ((1+b)*180):=trim_saber F G hG b1 180 (uniform_trade _)
  have fS:IsStarProjection (twist F S):=⟨(by change twist F S*twist F S=_; rw [←map_mul,(show S*S=S from gp.1)]),(by change star (twist F S)=_; rw [←map_star,(show star S=S from gp.2)])⟩
  let j:=changeM P.U (V y) U.J.M
  have hg:Sea S j:=by
      have he : spar P.K.j U.J.M (V y)=S:=by rw [P.kJ]
      rw [←he]; exact (safety Y s i k y).2
  let j':=acts (quant F.val) j
  have ht':Sea (twist F S) j':= Lamour.Bridge.lifted F hg
  refine ⟨g,⟨hX,gc⟩,?_,?_⟩
  · intro w hw
    have hy : star X.buy = star G.buy * F.val := by unfold X Shaft.foldC tailor; simp
    have hf : twist F (tickA N)=tickA N:=Cascade.tick_g ..
    have hd : Sea (tickA N) (acts (quant F.val) w):=hf ▸ (Lamour.Bridge.lifted F hw)
    let w':=changeM (m:= Vale.mesh (Y.ir i) P.R.L s) P.U 1 U.J.M
    have hw':Sea S' w' := by
      rw [←(show spar P.K.j U.J.M (1:Pane N)=S' from by rw [P.kJ])]
      exact Spire.sea_g (P:=P.U) (P.J.gran.trans ((Y.voyage i).ownership s).size) _ (guard0 P.dpos.le) U.J.M
    change ‖acts (quant (star X.buy)) w‖ = _
    rw [hy,quant_mul,act_mul]
    exact shear_bra_norm 4 U.J.M N (by decide) hS hw' hd
  intro t h' R w pF hl
  let A := (tilt S' t).foldC X
  have hR:U.J=R.J:=pF.2.2.2.2
  have hh:S=spar 4 R.J.M (V y):=by unfold S; rw [hR]
  let Q:=Graph.mile P.K.j R V y
  let B(v:Wave (Single N)):= acts (Fock.grow (excitation S') t) (acts (quant X.sell) v)
  have hB (r:ℝ) (l:Wave (Single N)) : B (r • l)=r • B l:=by unfold B; rw [(acts _).map_smul_of_tower,(acts _).map_smul_of_tower]
  have hr:Graph.recX P.U R V y= Graph.past U y.1 • acts Q j := by
    rw [Graph.porch]; unfold Graph.beam; have hh:changeM P.U (V y) R.J.M=j:=by unfold j; rw [hR]
    change _ • acts Q _= _; rw [hh]; congr 1
    unfold Graph.past
    rw [show U.path=R.path from pF.2.2.2.1, show U.p=R.p from pF.1, show U.funds=R.funds from pF.2.2.1, show U.beta=R.beta from pF.2.1]
  have hA:fiber A T:= tilt_fiber hS X hX h'
  let μr := ‖Pec.pigment U.J.I (V y)‖ + u*entryBudget (U.J.P.den (V y))
  let q₀:=flagCup U.p L U.beta
  let q:=q₀ / 2
  let v':= flakes (temp x) y.1; let w':= flakes (sax x) y.1; let Δ:= ((walls pio x:ℕ):ℝ)^4
  have hv:‖A.glow Q‖ ≤ Real.exp (w+μr):=by
    have hv := tilt_mile R V y hh A gp gc hA hT v.le Z hl
    unfold μr; unfold Q; rw [P.kJ]
    unfold u; rw [hR]; convert hv using 2; ring
  have hw:‖B j‖ ≤ Real.exp (d*n+Δ*w'):=by
    have hS₁:G.sell*S'=S':= shear_on_flat 4 U.J.M N _ _
    have he:B j= acts (Fock.grow (excitation S') t) (acts (quant G.sell) j'):=by unfold B X j' Shaft.foldC tailor; dsimp only; rw [quant_mul,act_mul]
    rw [he]
    apply (tilt_bound_sea hS G hG b1 hS₁ h' fS j' ht').trans (Real.exp_monotone ?_)
    exact yG.trans' (mul_le_mul_of_nonneg_right (show W≤W*W+1 by nlinarith only [sq_nonneg (W-1), hW]) (entryBudget_ge _))
  change ‖B (Graph.recX P.U R V y)‖ ≤ Real.exp _
  rw [hr,hB,norm_smul,Real.norm_of_nonneg (Real.exp_pos _|>.le),show B (acts Q j)= acts (A.glow Q) (B j) from tilt_action S' hS X t Q j]
  have hk:=prices_plot Y s i k e
  have hτ: U.p.threshold=temp x:= (congrArg BudgetPoint.threshold hk.1).trans (Y.meter.boot s).1
  apply (mul_le_mul_of_nonneg_left ((Graph.spentS _ _ _).trans (mul_le_mul hv hw (norm_nonneg _) (Real.exp_pos _).le))
      (show 0≤Graph.past U y.1 from (Real.exp_pos _).le)).trans
  have hQ: μr≤ d*n + q*v':=by
    have hu := hm (ht i).2 hk.2.2.2.2 (roofage Y i s) y
    have hg:0≤v':=by unfold v' flakes; positivity
    have hps: q=U.beta*(L.linear*temp x^2)/20:=by unfold q q₀ flagCup; rw [hτ]; ring
    rw [hps]; change _≤ x^(-tauA)*n+x/2*(L.linear*temp x^2)/20*v' at hu
    have h1 : x^(-tauA)≤ d:=Real.rpow_le_rpow_of_exponent_le hx (by norm_num [claimV,tauA,ratioV])
    have h2 : 0≤ L.linear*temp x^2 * v':=by have h3:=L.tail_pos; positivity
    have h3 : x/2≤ U.beta:= hk.2.2.2.1.1
    unfold μr; nlinarith only [hu,mul_le_mul_of_nonneg_right h1 hN,mul_le_mul_of_nonneg_right h3 h2]
  unfold Graph.past; rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_monotone
  let Sx:=U.path.inChannels U.funds U.p U.beta y.1
  have hy:greyFee Y 1 s i k y.1=q₀*v'+Δ*w':=by
    unfold greyFee; dsimp only; rw [one_mul]; change q₀*flakes U.p.threshold y.1+_= _; rw [hτ]; rfl
  change (- Sx+(w+μr+(d*n+Δ*w'))) ≤ - Sx+ _+w+2*d*n-_
  rw [hy]
  change _ ≤ _ - q*flakes U.p.threshold y.1
  rw [hτ]
  change _ ≤ _ - q*v'; dsimp only [q] at *; linarith only [hQ]

end Papal
end LocalLimit
end Rate
end YM.CF.Py
