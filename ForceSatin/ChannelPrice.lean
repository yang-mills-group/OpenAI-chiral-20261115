import ForceSatin.HomeTilt
import ForceSatin.ExactShear
import ForceSatin.TiltCost
import ForceSatin.Wash

/-! Occupation tax on the Born numerator, *before* all the checker insertions.
Sparse grey-book variant of F1 / WA.1 on the actual Orbit.
Uses Orbit wash per σ & adapts preceding script. Uses the existent LusterS sparse gauge purchase. Indices, footprints and
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
open BPress.Spin Tiling
-- sign in the mark can be odd on ingredients, no pitch here; estimates at EVERY principal channel
lemma snow_rises {N:Side}(t:ℝ)(X:Pane N)(σ:Signed) : flakes t (pull σ 0 X)=flakes t X:=by
 let i:Equiv.Perm (Cell (More N)):= Equiv.ofBijective (Face.send σ 0) ⟨Face.injective_send σ 0,Finite.injective_iff_surjective.mp (Face.injective_send σ 0)⟩
 have h(z:Cell (More N)):z∈roughness t (pull σ 0 X) ↔ i z∈roughness t X:=by simp only [roughness,mem_filter]; rw [Face.send_price X z σ 0 SU.group.chord SU.group.chord_inv (fun i x=> SU.group.chord_conj x i)]; simp; rfl -- syntax check
 unfold flakes; apply congrArg (Nat.cast); exact Finset.card_equiv i h -- order
abbrev scarf (a C δ:ℝ) (L:Side)(F:ℝ):ℝ:= (2*Real.exp (-(a*radiusB F))+(radiusB F:ℝ)*4*(sphereRate*tuition L F)/δ)*C
theorem scarf_grade (a C δ:ℝ)(h:0<a) (L:Side): Grade (-2/5) (scarf a C δ L):=by
 let tZ(x):= Real.exp (-(a*(radiusB x:ℝ)))
 have hu:Grade (-1) tZ:=by convert trail_b h using 1; unfold trail tZ; ring_nf
 have hv:= Grade.plus ((hu.scaleB 2).grow (show (-1:ℝ)≤ -2/5 by norm_num)) ((radiusBill.mul (tuition_b L)).scaleB (4*sphereRate/δ) |>.grow (by norm_num))
 apply cash (hv.scaleB C); filter_upwards with x; apply le_of_eq; congr 1; unfold tZ; unfold scarf; ring

abbrev coveredWidth (L:Side)(x:ℝ){N c:Side}(r:Lattice.Ratio c (More N)):= cliffs x ≤ r.count.val ∧ r.count.val≤ walls L x
def outerFee (P C:ℝ) : ℝ:= (21:ℝ)^4*(2*C*180)*(P*P+1)

lemma scarf_bill {a C δ:ℝ}(p:P.d≤δ)(h:0<a)(v:0<C)(hg:0<δ)(H:∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val→Sow 4 N a C δ)(K:ℝ) : ∀ᶠ s in atTop,∀ i k:ℕ,
    let U:= room Y s i; let N:=count Y s i; let R:=gram Y s i k; let x:= ℶ s; let M:=R.J.M; let Z:= FlatPaneP 4 M N
    IsStarProjection Z ∧ ∀(c:Side)(r:Lattice.Ratio c (More N)),coveredWidth pio x r → ∀ (A:Tiling c N r)(σ:Signed)(y:Orbit N),let S:=spar 4 M (U y); let l:= A.arcs y.1 σ; let Q:=twist (tradew N l) S; IsStarProjection S ∧ condor S C ∧ (K*K+1)*entryBudget (Q-Z) ≤ parcelF x * sites N + outerFee K C*((walls pio x:ℕ):ℝ)^4 * flakes (sax x) y.1:=by
 obtain ⟨n₀,v₀⟩:= H.exists
 let f:= K*K+1; have hf:f≥0:=by unfold f; nlinarith only [sq_nonneg K]
 let q0:= -(tauA/2)
 have he:= Grade.scaleB f (((Grade.scaleB 180 (scarf_grade a C δ h pio)).grow (b:=q0) (by norm_num [tauA,q0])).plus ((Grade.pitch q0).scaleB (2*C*180)))
 filter_upwards [count_room Y (max n₀ (P.J.n+1)),(turnover P).eventually (he.cost_p (b:=-claimV) (by norm_num [claimV,ratioV,q0,tauA])),(turnover P).eventually (plaster_area 1 zero_lt_one),(turnover P).eventually gain_a,(turnover P).eventually (paceSize pio),(turnover P).eventually ((sax_b.roots (by norm_num [tauA])).eventually (ge_mem_nhds P.J.ht)), (turnover P).eventually_gt_atTop 0] with s e xQ y0 y1 y2 v1 y3 i k U N R x M Z
 have e:=e i; have uH:= v₀ N (((le_max_left ..).trans e.1).trans e.2); let T:=P.U.broadness N (P.J.gran.trans ((Y.voyage i).ownership s).size) R.J.M
 have vT: Sparkle N P.d M 4:=by rw [←P.kJ]; exact T
 let H:= roofage Y i s
 refine ⟨vT.projection (1:Pane N) (guard0 P.dpos.le),?_⟩; intro c r vh A σ y S l Q
 let d:= radiusB x; let k:=hallBill d
 have hX:P.J.n+1 ≤ d:= (le_max_right ..).trans e.1
 have hu:= y0 r.count A.odd_width vh.1
 let u:= sphereRate*tuition pio x; have hρ:=H.paid y
 refine ⟨vT.projection _ hρ,uH.daylight false M _ (hρ.shrink p),?_⟩
 have hv:= A.snow_cost (m:=d) (Y:=y) σ (roofage Y i s) (show 0≤ sax x from y1.2.le.trans y1.1) v1 v hg (show 0≤u from mul_nonneg sphereRate_cost.positive.le y2.1.le) (mul_le_mul_of_nonneg_left (y2.2 r.count.val r.count.property vh.2) sphereRate_cost.positive.le) M (l:=k) (show d+P.J.n+1 ≤ k from (by unfold k hallBill Sequest; omega)) uH p hu.1
 let w:ℝ:=r.count.val; let n:ℝ:=sites N; let F:=x^q0; let c2:ℝ:=Fintype.card (Site c); let q:=largerBill r.count.val k
 have hM:c2*w^4=n:=by unfold w c2 n sites; rw [site_card,r.exact_size]; push_cast; ring
 have ht:c2*q ≤ F*n:=by
    rw [←hM]; have hw:(q:ℝ) ≤ F*w^4:=by
       have hp:0≤ Real.log 2:=Real.log_nonneg (by norm_num)
       have hz:d≥1:=by omega
       have he:(1:ℝ) ≤ d:=by exact_mod_cast hz
       nlinarith only [he,Nat.cast_nonneg (α:=ℝ) q, hp,show (4:ℝ)*(1*(d:ℝ))*q+Real.log 2 ≤ F*w^4 from hu.2]
    calc _≤c2*(F*w^4):=by unfold c2; gcongr
         _ = _:=by ring
 let A':=broken r (sax x) (silhouette σ y.1)
 let D':= flakes (sax x) y.1; have hk:(A'.card:ℝ) ≤D'*21^4:=by
    rw [show D'= flakes (sax x) (silhouette σ y.1) from (snow_rises ..).symm]; have he:=Nat.cast_le (α:=ℝ).mpr (broken_charge (U:=silhouette σ y.1) (t:=sax x) (r:=r)); push_cast at he; norm_num; exact he
 let W:=(walls pio x:ℝ); have hw:(A'.card:ℝ)*w^4≤ D'*21^4*W^4:= mul_le_mul hk (pow_le_pow_left₀ (Nat.cast_nonneg _ ) (Nat.cast_le.mpr vh.2) _) (by positivity) ((by positivity:(0:ℝ) ≤ A'.card).trans hk)
 let L:=scarf a C δ pio x; have hL: 0 ≤ L:=by unfold L scarf; have h0:0 ≤ tuition pio x:= y2.1.le; have hl:=sphereRate_cost.positive; positivity
 have hn:L*(180*N.val^4) ≤ L*(180*n):=by
    unfold n sites; gcongr; exact_mod_cast Nat.le_mul_of_pos_right N.val two_pos
 let v:=2*C*180; have hV:v≥0:=by unfold v; positivity
 have hK: w^4>=0:=by positivity
 have hj:N.val^ (4:ℕ)≤ (More N).val^(4:ℕ):= pow_le_pow_left' (Nat.le_mul_of_pos_right N.val two_pos) _
 rw [show Q= _ from (Eq.symm (vT.covary (U y) (A.arcs y.1 σ) hρ))]; apply (mul_le_mul_of_nonneg_left hv hf).trans
 rw [Nat.cast_add, Nat.cast_mul,Nat.cast_mul,Nat.cast_pow]; change f * (L * _ + v*(_ +_)) ≤ parcelF x*n+outerFee K C * W^4 * _
 calc
    _ ≤ f * (L*(180*n)+ v*((F*n)+(D'*21^4*W^4))):=by exact mul_le_mul_of_nonneg_left (add_le_add hn (mul_le_mul_of_nonneg_left (add_le_add ht hw) hV)) hf
    _ = f*(180*L+v*F)*n+ outerFee K C * W^4* D':=by unfold outerFee f v; ring
    _ ≤ _:= add_le_add_left (mul_le_mul_of_nonneg_right ((le_abs_self _).trans xQ) (zero_le_one.trans (sites_pos _))) _
#print axioms scarf_bill
def ChannelWorld (s i k:ℕ) (b C:ℝ) : Prop :=
  let V := room Y s i; let A := gram Y s i k; let N:=count Y s i
  let S:= FlatPaneP 4 A.J.M N
  let x := ℶ s
  ∃ p : IsStarProjection S, ∀ y:Orbit N, ∀ {c:Side}{r:Lattice.Ratio c (More N)}, coveredWidth pio x r → ∀ (T:Tiling c N r)(σ:Signed), let l:= T.arcs y.1 σ;
    let g:= ((exactShear 4 A.J.M N (by decide) p).foldC (tailor (tradew N l)))
    (fiber g ((1+b)*180) ∧ condor (spar 4 A.J.M (V y)) C) ∧
    (∀ w, Sea (tickA N) w → ‖acts (quant (star g.buy)) w‖=Real.exp (angleFin A.J.M N 4)) ∧
    ∀ t:ℝ, |t| ≤ 1 → ∀ R w, ProperT A R → tier P.h (R.board y).val ≤ Real.exp w →
      ‖acts (grow (excitation S) t) (acts (quant g.sell) (Graph.recX P.U R V y))‖ ≤
        Real.exp (- A.path.inChannels A.funds A.p A.beta y.1 + greyFee Y (outerFee (tiltRent (1+b)) C) s i k y.1 +
          w+ 2 * parcelF x*sites N - tiltMaskFee N P.K.top.clip A y.1)


lemma channelTilt {δ C a b:ℝ} (p:P.d≤δ)(hs:0<δ)(v:0<C)(c:0<b)(h:0<a)
    (E:∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val → Sow 4 N a C δ)(f:CF.Papyrus.Franc.postage 4 b)
    (Z:mixedMatrixFee b*(1+C) ≤ P.h) : ∀ᶠ s in atTop, ∀ i k:ℕ,s ≤ Y.uv k → ChannelWorld Y s i k b C := by
  let W:= tiltRent (1+b)
  let T:= mixedMatrixFee b
  let u:= T^2*((1+C)*C)
  have hu:0≤u:=by unfold u; positivity
  have hT:0≤T:=by unfold T mixedMatrixFee tiltCost; positivity
  have hW:0<W:=by unfold W tiltRent; positivity
  filter_upwards [scarf_bill Y p h v hs E W, (turnover P).eventually (VelvetC.hunt_γ
      (r:=P.J.n) (t:=P.d) u hu (level_p P.W.C) (cash_v P.W.C) P.J.ht P.K.top.clip),
    count_room Y 0,(turnover P).eventually_ge_atTop 1] with s he hm ht hx i k e
  let x:=ℶ s
  let U:= gram Y s i k; let V:=room Y s i; let N:=count Y s i; let d:=parcelF x
  let n:=sites N; let L:= P.K.top.clip
  have hN:0≤n:=zero_le_one.trans (sites_pos _)
  let S':= FlatPaneP 4 U.J.M N
  obtain ⟨hp,H⟩ := he i k
  have hS:IsStarProjection S':= hp
  unfold ChannelWorld
  dsimp only
  refine ⟨hp,?_⟩
  intro y c₁ r hV X₀ σ; let g:= X₀.arcs y.1 σ
  obtain ⟨gp,gc,yG⟩:= H c₁ r hV X₀ σ y
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
  refine ⟨⟨hX,gc⟩,?_,?_⟩
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
  let v':= flakes (temp x) y.1; let w':= flakes (sax x) y.1; let Δ:= outerFee W C * ((walls pio x:ℕ):ℝ)^4
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
  have hy:greyFee Y (outerFee (tiltRent (1+b)) C) s i k y.1=q₀*v'+Δ*w':=by
    unfold greyFee; dsimp only; change q₀*flakes U.p.threshold y.1+_= _; rw [hτ]; rfl
  change (- Sx+(w+μr+(d*n+Δ*w'))) ≤ - Sx+ _+w+2*d*n-_
  rw [hy]
  change _ ≤ _ - q*flakes U.p.threshold y.1
  rw [hτ]
  change _ ≤ _ - q*v'; dsimp only [q] at *; linarith only [hQ]

#print axioms channelTilt
end Papal
end LocalLimit
end Rate
end YM.CF.Py
