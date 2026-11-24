import YM.SU5.FiniteGaugeData.Pannier.Exacts
import YM.SU5.FiniteGaugeData.Marked.Journey.Ignite
/-! # High-observing-cut estimate for Mark given Ward packet on its chosen points.
Sharp, whole-volume, companion yet to be used for the geometric estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
abbrev count (s i:ℕ):= P.Ctor (Y.ir i) s
abbrev gram (s i k:ℕ): GramM (count Y s i) := ((Y.voyage i).X (Y.uv k)).gram s
abbrev room (s i:ℕ): Loom (count Y s i) := (Y.voyage i).CapeT s
local notation "Dx" i:max => hat P.R.L P.x i
local notation "Dx₀" s i => count Y s i
local notation "ρ" s:max => P.V.L.path s
local notation "U" s i => room Y s i
local notation "M" s i k => gram Y s i k
open CF.Pannier.Damask
open Buffered
lemma prices_plot (s i k:ℕ) (e:s≤Y.uv k) : let R:=gram Y s i k; R.p= Y.meter.a s ∧ R.path= P.V.L.path (Y.uv k-s) ∧ R.funds= P.K.top.clip ∧ matchedX (hat P.R.L P.x s) R.beta ∧ Graph.Ledger P.h (dleaf P.R.L (hat P.R.L P.x s)) (dleaf P.R.L (hat P.R.L P.x s)) (levelQ P.W.C) (cashU P.W.C) R := by
 intro R
 let H:=(Y.voyage i).X (Y.uv k); have p:=H.pull.owns s e
 have v:InterestX P.W.C _ R.J := p.taste ▸ ((P.W.arm ..).sound s)
 exact ⟨p.width.symm,p.path.symm,p.fund.symm,H.pull.sift s e,frostQ ((H.pull.note s e).lot_p le_rfl le_rfl) (zero_le_one.trans P.height) v⟩
lemma roofage (i s:ℕ) : Roof (count Y s i) P.J.k P.d P.J.n (room Y s i) := { ((Y.voyage i).ownership s).paid with paid:=fun x=>(((Y.voyage i).ownership s).paid.paid x).shrink P.J.hr.le }
-- notation remove for projection
lemma safety (s i k:ℕ) (x:Orbit (count Y s i)) :
    let R:=gram Y s i k; let A:=room Y s i
    IsStarProjection (spar P.K.j R.J.M (A x)) ∧ Sea (spar P.K.j R.J.M (A x)) (changeM P.U (A x) R.J.M):=by
  intro R A
  let a:= (Y.voyage i).ownership s; have he:=P.J.gran.trans a.size; exact ⟨(P.U.broadness _ he R.J.M).projection _ ((roofage Y i s).paid x), Spire.sea_g (P:=P.U) he (A x) ((roofage Y i s).paid x) R.J.M⟩
lemma count_grows (i:ℕ):Tendsto (fun k=> (count Y i k).val) atTop atTop := by
 apply tendsto_atTop_mono _ Y.ir_grows.tendsto_atTop; intro k; unfold count Ctor cell CSide; calc _ ≤ _:=mesh_ge (Y.ir k) P.R.L i -- tune
                                                                                                 _ ≤ _ := (Nat.le_mul_of_pos_right _ (by decide : 0<2)).trans (Nat.le_mul_of_pos_right _ (block P).property)

abbrev sealPrice {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}(V: Grace K R L){B:Side}{d:ℝ}{U' : Grasp V.U B d}(W:GivenX V U') := cameo (cashU W.C)
variable {A C κ h : ℝ}
def Backlog (s i k:ℕ) (h C κ:ℝ) (F:Mark (count Y s i)) : Prop :=
    let G:=gram Y s i k; let A:=room Y s i
    ∀ x: Orbit (count Y s i), Yep h (acts (star (F (x.1,A x))) (mateK _)) (changeM P.U (A x) G.J.M) (Real.exp (-(C*sites (count Y s i))+κ*flakes G.p.threshold x.1))
local notation "μ" s:max i:max => sites (count Y s i)
lemma hinge {j i k:ℕ}(hj:j ≤ Y.uv k)(F: Mark (count Y j i)) (u: Backlog Y j i k h C κ F) {v:ℝ}
    (b: ∀ x: Orbit (count Y j i), Pays h (Graph.mile P.K.j (gram Y j i k) (room Y j i) x)
       (Real.exp ((sealPrice P.V P.W)*sites (count Y j i)+v*flakes (temp (hat P.R.L P.x j)) x.1)))
    (x: Orbit (count Y j i)) :
    let G:=gram Y j i k; let A:=room Y j i
    ‖letterRead (F (x.1,A x)) (Graph.recX P.U G A x)‖≤ Real.exp ( -(P.V.L.path (Y.uv k-j)).inChannels P.K.top.clip G.p G.beta x.1 + (κ+v)*flakes G.p.threshold x.1 +(sealPrice P.V P.W - C)*sites (count Y j i)):= by
 intro G A; let f:= F (x.1,A x); let y:=mateK (count Y j i); obtain ⟨g,w,q,_⟩:= prices_plot Y j i k hj
 let B:= Graph.beam G P.U A x
 have he':G.p.threshold=temp (hat P.R.L P.x j):= g.symm ▸ (Y.meter.boot j).1; have hc:= b x; rw [← he'] at hc; let x0:= Real.exp (- (C*μ j i)+ κ*flakes G.p.threshold x.1); let E:= Real.exp ((sealPrice P.V P.W)* μ j i+v*flakes G.p.threshold x.1)
 have ht:= Yep.val (show Yep h _ B (E*x0) from hc.2 (acts (star f) y) (changeM P.U (A x) G.J.M) x0 (Real.exp_pos _).le (u x))
 rw [Graph.porch, (letterRead f).map_smul_of_tower] -- tune
 let m:= Graph.past G x.1; rw [norm_smul,Real.norm_of_nonneg (r:=m) (Real.exp_pos _).le]; change m*‖inner ℂ y (acts f B)‖≤ _; rw [← act_inner]; apply (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le).trans_eq
 change m*(E*x0)=_; unfold m x0 E Graph.past; change G.path=P.V.L.path _ at w; change G.funds=P.K.top.clip at q; rw [← Real.exp_add,← Real.exp_add,w,q]
 congr 1; ring

lemma measured (hU:Inflation A P)(p:0≤h)(u:h ≤ P.h) (k₀ : ℝ) : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → s ≤ Y.uv k → ∀ F: Mark (count Y s i),∀ T:ℝ,Envelope F → Backlog Y s i k h T k₀ F →
   ‖Buffered.Afterglow.Journey.compass Y i k s F‖ ≤ Real.exp (((sealPrice P.V P.W - T)+ blossom P.K+(A+1))*sites (count Y s i)):=by
 let V:=P.V; let C:=P.W.C; let c:=cashU P.W.C; let v:=sealPrice P.V P.W
 let x:=hat P.R.L P.x
 obtain ⟨κ,_,r⟩:=wisps_budget (t:=P.d) (r:=P.J.n) p (cash_v C) P.J.ht (level_p C) -- J.ht may >?
 filter_upwards [compensates Y hU,(turnover P).eventually r, (turnover P).eventually (gaugedBudget P.V (k₀+κ)), (turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds zero_lt_one))] with s gp ⟨n,t⟩ ⟨N,Z⟩ ch
 filter_upwards [(count_grows Y s).eventually_ge_atTop (max N n)] with i g k hi hk F T h' X
 let D:= μ s i; let Q:= (gram Y s i k).p
 let B:=gram Y s i k; let L:=room Y s i
 obtain ⟨p,hq,hu,hv,gV⟩:= prices_plot Y s i k hk
 have he: SugarBill V (blossom P.K) (count Y s i) Q (Y.uv k-s) (x s) B.beta (k₀+κ) (v-T):=Z _ _ _ _ _ hv ((congrArg BudgetPoint.threshold p).trans (Y.meter.boot s).1) ((le_max_left ..).trans g)
 let f(y:Orbit (count Y s i)):= letterRead (F (y.1,L y)) (Graph.recX P.U B L y)
 have h₁: ∀ x:Orbit (count Y s i), ‖f x‖ ≤ _ := hinge Y hk F X (v:=κ) (fun x=> t (roofage Y i s) P.h _ _ _ gV u ((le_max_right ..).trans g) ch ch x (safety Y s i k x).1)
 let E:=Y.each_level i k s hi hk
 have hX:‖Buffered.num0 P.U B L F‖≤ Real.exp (((v-T)+blossom P.K-mulch (x s))*D):=he f (Buffered.mark_integrable (roofage Y i s).bill h' ((Marks.can_read _ _ _ _ E).smul (Complex.exp (-B.v)))) h₁
 let W:= ‖Buffered.vac0 P.U B L‖; let m:=Real.exp (-(mulch (x s)+(A+1))*μ s i); let z:=Real.exp (((v-T)+blossom P.K+(A+1))*D)
 have hp:m≤W:=gp i k hi hk; have hb:0<W:=(Real.exp_pos _).trans_le hp
 rw [Buffered.Afterglow.Journey.compass,← same_ratio,norm_div]; apply (div_le_iff₀ hb).mpr
 apply hX.trans; change _ ≤ z*W; apply (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans'; apply le_of_eq; change _= z*m; unfold z m D; rw [← Real.exp_add]; congr 1; ring
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.measured
