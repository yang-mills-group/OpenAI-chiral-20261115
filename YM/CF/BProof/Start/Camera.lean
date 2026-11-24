import YM.CF.BProof.Start.Torus
import YM.CF.BProof.Screen.Output

set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Start
open Function Filter MeasureTheory Finset
open Lattice Tenant Lat Cube Skye RG Angular Wilson Rhythm Hero Mark Branch
open scoped Topology BigOperators Classical
open Gates Gates.Stage Gates.Stage.Setup Mapping House
open Stint Tape Hearth Prime Estate Cliff
open Jet Paige Drapes Vault Oasis Bias Weights Cabinet Mint Contour
variable {N:Side}{d K:ℕ}{c:Clip}{w R v:ℝ}(S:Gates.Stage c w R v)
variable {m m' L B:Side}{j:ℕ}{a b l r:ℝ}{D:Spin.Ready j a b l r}{u:ℝ}(E:Essence D u)
variable {rₜ a':ℕ}(Δ: Rhythm.Note E (gap L a') rₜ)
variable {p:Odd L.val} {Y:Pricing j L p (Vault.Thread j)} {δ:ℝ}{F:Grasp Y B δ}
variable {E Δ S}{U H:ℝ} (J:Mote S E Δ F U H)
open Veil Anthem
-- this file specialized stage with `d₀.funds` clipping. expression grammar same even if FPL chosen estimated larger. stop packages all
open Seam Trek Spin Payment Palot
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
open Scree Scope
local notation "N_" => mid m B
namespace Mote
variable {d₀:GramM (mid m B)} {S:Gates.Stage d₀.funds w R v} {B':ℝ→ℕ}{Fp:ℝ→ℝ}{W:ℕ}{y h ν:ℝ} (J:Mote S E Δ F U H)(Γ: J.Licence B' Fp W y h)
variable (V:Setup S L a' (More (mid m B)) W y)(U₀:Loom (mid m B))
variable (P:J.Extent y W (mid m B))
local notation "pV"=>Γ.baseL
local notation "θP"=> (d₀.beta*BProof.g y^2)
-- Build binds occupancy Core K by raising Aim certificate. AMP members proof. C'

variable (Y':Spire.Pearl F)
namespace Show
variable (Z: School V d₀.path (d₀.beta*BProof.g y^2) E Δ U₀ ν δ 200) (t:Core j a b l r (mid m B))(KK:Fund₀ d₀ t Y') (pX:d₀.p.threshold=thresh y)
variable (Hc: Hinge F (Z.age Γ.baseL t) Δ.stage.c Hero.rateH Δ.stage.η J.arc d₀.J.I (Cliff.Economy.lipBill S.K.C) J.α J.A J.β J.C)
variable (To: Oasis.Marks (Z.age Γ.baseL t) J.oak Δ.stage.c Hero.rateH Δ.stage.η){q:Cargo d₀ h (Fp y)}(Bt:Pantry To q (BProof.g y))
abbrev KQ:= Scene.scoreP Γ.baseL Z J.k t F Hc To Bt pX
local notation "Q"=>KQ J Γ V U₀ Z t pX Hc To Bt
-- readability. Tube + aperture already buy. 
variable (pu:u≤ Y'.q)(qP: d₀.p.B=B' y)(uP:d₀.p.supportExponent=1) (vb:y ≤ 2*d₀.beta)(ub:d₀.beta≤2*y)(HP:Scene.Output.Warp (U:=U₀) (d₀:=d₀) F)
include Γ uP qP
abbrev Cg_ := feeVal B' J.oak Fp
lemma gas_H : Oasis.Tube d₀ J.oak h (BProof.g y) (Fp y) (feeα B' J.oak y) (J.ζy B' Fp y):= Γ.gasL uP qP -- Tube amb RG
include pu KK P vb ub HP uP qP
local notation "κC"=>mB (S:=S) (L:=L) (a':=a') y
local notation "λμ"=> piT (DP L a' y) y
abbrev Lv:= ((More (mid m B)).val:ℝ)
lemma Income : Lifted d₀ F U₀ Q (J.priceA B' Fp y) κC λμ w R v:=by
 let Ψ:= Scene.Output.outputs pV Z J.k t F Hc J.ζ To Bt (gas_H J Γ qP uP) pX vb ub HP -- tune parameter unused Γ? namespace
 have ht:J.priceA B' Fp y=Estate.wealth J.arc J.A J.C+(Oasis.Cargo.roomAge d₀.p.B (Fp y+Fp y)+4*(J.ζy B' Fp y)):=by rw [qP]
 rw [ht]; exact Ψ
lemma result : Real.exp (-(kA y)*((More (mid m B)).val:ℝ)^4)≤ ‖numerator d₀ F U₀ (Q).test‖:=by
 let e:=BProof.g y; have he:0<e:=coin_pos ..; let ξ:=sizeC J y; let Gt:=Hc; have hv: 0<y:=lt_of_lt_of_le (by norm_num) Γ.baseL.dull.threshY
 let A:=t; let p':=Γ.baseL; let M:=J.mode y W; let z':=Z
 have ht:= J.clock_Z Γ V d₀.path U₀ (d₀.beta* BProof.g y^2) Z
 have uZ:=Estate.cost_purchase (σ:=M.bias) pV z' J.k ξ t ht F d₀.J.I Hc J.ζ Γ.statL (pu.trans (Y'.roof.trans F.small)) J.aperture J.fuel_p.le P.near KK.pos (show _≤ J.houseE y from le_refl _) ?_; swap; · rw [V.width,V.space]; exact Γ.fuel
 have hh:= z'.silhouette_p Γ.baseL
 have hz : Scene.Good z' J.z (J.ζg B' y):=by
    constructor
    · rw [V.space,hh]; exact Γ.seekL
    rw [V.space,hh]; exact Γ.gas
 have he':‖(e:ℂ)‖=BProof.g y:= by rw [Complex.norm_real, Real.norm_of_nonneg he.le]
 have P' := Scene.Output.original pV z' J.k ξ A ht F Hc J.ζ To Bt (gas_H J Γ qP uP) (↑e:ℂ) pX Y' pu M uZ vb ub (by exact_mod_cast he.ne') KK ?_ (flux_p S.κ S.κ_pos (GP ..) y|>.le) ?_ hz (gas_p B' J.oak y|>.2.2) he'.le ?_ (solid J Γ V) HP rfl (J.tag_Z Γ V) le_rfl -- order uP? flux_p binder c implicit, goal
 refine le_trans (Real.exp_monotone ?_) P'
 · rw [V.width]; exact mul_le_mul_of_nonneg_right (neg_le_neg Γ.hit) (by positivity)
 · rw [he',V.width,V.space]
 · rw [V.width]; exact burn_le S.κ S.κ_pos (GP L a') hv d₀.beta vb
 unfold Scene.quo Pour.fŴ; rw [qP,V.space,V.width]; exact Γ.sumF
lemma marks (i:V.yard.Index): Allowed (V.yard.band i) ((Q).slot i) ∧ Paid ((Q).slot i) (Real.exp (kA y*((More (mid m B)).val:ℝ)^3)):=by
 let p:= Income J Γ V U₀ P Y' Z t KK pX Hc To Bt pu qP uP vb ub HP; refine ⟨(Q).allowed i p.grant,fun i'=>?_⟩; apply le_trans ((Q).scope_pay i i' p.grant); unfold Score.slotFee; rw [V.length Γ.baseL]; apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right Γ.markPrice (by positivity) -- arg order V U₀ P ? section
end Show
-- use existential commitment. tie every parameter/formula to duration & loosen
-- Return actual score in test for assembly. 
abbrev MakerBand(N:Side):= Manus.Poles N
variable (U0:Setup S L a' (More (mid m B)) W y) -- optional
variable (Pq: Score V.yard (Manus.Poles (mid m B)))
def Show(Pq: Score V.yard (Manus.Poles (mid m B))) : Prop:= ∃ (Z: School V d₀.path (d₀.beta*g y^2) E Δ U₀ ν δ 200) (t:Core j a b l r (mid m B)) (_k:Fund₀ d₀ t Y') (p:d₀.p.threshold=thresh y) (Hc: Hinge F (Z.age Γ.baseL t) Δ.stage.c Hero.rateH Δ.stage.η J.arc d₀.J.I (Cliff.Economy.lipBill S.K.C) J.α J.A J.β J.C)(To:Marks (Z.age Γ.baseL t) J.oak Δ.stage.c Hero.rateH Δ.stage.η)(q:Cargo d₀ h (Fp y))(t':Pantry To q (BProof.g y)), Pq= Scene.scoreP Γ.baseL Z J.k t F Hc To t' p
-- choose show given standard receipts. positivity output order not optimizing h.
include P
lemma chosen (q:δ≤ E.pre.limit)(z:δ≤ E.H.calm)(hL:0≤δ) (u:d₀.path.Bounds d₀.funds w R v)(pVs:thresh y≤ν)(hv:Roof (mid m B) ν δ rₜ U₀)
 (pv:d₀.J.P.toll a b l r)(p0:d₀.p.threshold=thresh y)(pp:Paint m B d₀.J.I U H)(g: Nonempty (Cargo d₀ h (Fp y))) (q': 1 ≤ j)(T: Stamped j L p Y)(S':F.roundZ≤(mid m B).val)(qP:d₀.p.B=B' y)(uP:d₀.p.supportExponent=1)(vb:y≤2*d₀.beta)(ub:d₀.beta≤2*y) : ∃ P,Show J Γ V U₀ (ν:=ν) Y' P:=by
 obtain ⟨M⟩:= J.studies Γ P V d₀.path U₀ (d₀.beta*BProof.g y^2) q z hL u (θ_t Γ.baseL d₀.beta vb ub) pVs hv
 let t: Core j a b l r (mid m B):=⟨d₀.J.M, d₀.J.P, pv⟩; have ht:Honor D t δ:= M.age Γ.baseL t; obtain ⟨Hx⟩:= J.pigment d₀.J.I ht pp S'; obtain ⟨Tg⟩:= J.gas ht; obtain ⟨C⟩:=g; obtain ⟨Hw⟩:= served Tg C (Show.gas_H J Γ qP uP) (clockEvent E Δ q')
 exact ⟨_, M,t,⟨rfl,rfl,T,q',S'⟩,p0,Hx,Tg,C,Hw,rfl⟩
end Mote
end YM.CF.BProof.Start
