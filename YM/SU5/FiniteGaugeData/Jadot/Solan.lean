import YM.SU5.FiniteGaugeData.Jadot.Nigra
import YM.SU5.FiniteGaugeData.Jadot.Celeste
import YM.SU5.FiniteGaugeData.Cuprite.Incan
/-! # WP23 to true finite density. Lens, macro. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 600000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py CF.Py.Rate
open SU Fock Reduction Reduction.Jersey Reduction.Drama Reduction.Drama.Pack Reduction.Hutch Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Nacre -- amb.Supply
open Rush Scroll Peaks Tap Tulip Fir Cascade Dial Spire Paige Vault
open Avenue RouteM Spindle
open Rhythm Pilot PhaseM Steve VolumeRate
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Reduction.Hutch Fist Reduction.Verna Reduction.Dinar Reduction.Dijon Reduction.Rheims Reduction.Ziz Reduction.Dijon.Currency Reduction.Celeste Window.Presidio Window.Presidio.Menton Window.Presidio.Gato Thera Gall Girt
namespace Turnist
variable {n B L:Side} {ε t tH t' v H μ C C' cₛ c a' a M u x h d e α₁ m₀ α β b f e' v' cE X₀:ℝ}{r s k w j:ℕ} {o: Odd L.val} {U: Pricing k L o (Thread k)} (G:Grasp U B d)
section
variable {A Z P Q X M N:Op (Single n)}(g:Mosquito n)
local notation "θ" A:max=> twist (tradew n g) A
local notation "η" A:max=> twist (quantU (tradew n g)) A
local notation "ζ" A:max=> twist (tradew n g⁻¹) A
include g
lemma twist_cols(p:cellU univ X a) (h:0≤a): cellU univ (twist (tradew n g) X) (45*a) := by
 intro i _; let U:=tradew n g; let y:= acts (star U.val) (basisKet i); have he:dialZ y ≤ 45:= lurk_n g i
 unfold cellZ; rw [twist_formula,act_mul,act_mul,act_unit_norm]; change ‖acts X y‖≤_; apply le_trans (b:=dialZ y*a) _ (mul_le_mul_of_nonneg_right he h)
 nth_rw 1 [←basis_expand y]; rw [map_sum]; unfold dialZ; rw [sum_mul]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (p i (mem_univ _)) (norm_nonneg _)
lemma twist_root (p:Milieu Q A)(Y:Op (Single n)): twist (tradew n g) (Hail A Y)=Hail (θ A) (θ Y):=by unfold Hail; rw [map_mul,map_add,map_star,map_one,Spiny.kinv _ p.litA]
lemma turncost(p:Milieu Q A)(v:Spear Q Z)(F:FC (Single n)):
 η (cost A Z F) = cost (θ A) (θ Z) (η F):=by
 unfold Celeste.cost; rw [←lever.twist_I (Pall.mun p v) (Pall.wun p v), twist_root g p, show θ (Pall A Z)=_ from by unfold Pall; rw [map_mul,map_sub,map_one,map_star]] -- tune
lemma beyond(p:Milieu Q A)(v:Spear Q Z)(F:FC (Single n)) : ‖acts (star (cost (ζ A) (ζ Z) F)) (mateK n)‖= ‖acts (star (cost A Z (η F))) (mateK n)‖:=by
 let V:=quantU (tradew n g); let Z':= η F; let K:=quantU (tradew n g⁻¹); let A':=cost A Z Z'; have he: twist K (cost A Z Z')=cost (ζ A) (ζ Z) (twist K Z'):= turncost g⁻¹ p v Z'
 have hp: twist K Z'=F:=by
    have he:K=star V:=by unfold K V; rw [Mono_tradew]; apply Subtype.ext; exact quant_star _
    rw [he]; exact twist_inv ..
 rw [hp] at he; rw [←he,←map_star]; nth_rw 1 [← show acts K.val (mateK n)= mateK n from mastC g⁻¹]; rw [←Fock.swivel,act_unit_norm]
end
abbrev PayR(c:ℝ):= 270*(3*c+2)
lemma payR_nn(b:ℝ)(h:0≤b):0≤PayR b:=by unfold PayR; positivity
-- point geometry.Separate stipend sobriety. pay Tickets
variable {T:GramM (mid n B)} (Y:Loom (mid n B))(X:Orbit (mid n B))(K:Roof (mid n B) tH d j Y) {g:Mosquito (mid n B)} -- p.
local notation "Θ"=> tickA (mid n B)
local notation "R"=> (spar k T.J.M (1:Pane (mid n B)))
local notation "Q"=> (spar k T.J.M (Y X))
local notation "TILT"=> (1+Graph.actF k T Y X)
local notation "U0"=> (mid n B)
variable {S B₀:Finset (Single (mid n B))} {X' : FC (Single (mid n B))}{T₁ P₁:Op (Single (mid n B))}
local notation "Vt" => twist (tradew (mid n B) g⁻¹)
local notation "L₀" => stageL S Θ R μ T₁
local notation "Z₀" => stageZ B₀ Θ R μ P₁
local notation "Ξ_"=> (CFolio e S + CFolio e' B₀)
-- compact macros.Payment retains height & Tick.Voy
open Ziz
abbrev BadgeKN (s v:ℝ):ℝ:= (3+v⁻¹)*(18*s)^2 -- temporal pay.B
abbrev BadgeK (x:ℝ):ℝ:=300*x+3*(330*x)+8*x
abbrev BraWeight (L Z:Op (Single n))(X:FC (Single n)):= ‖acts (star (cost L Z X)) (mateK n)‖ -- tilt bill (rename)
include K
-- overlap certificate.C includes bleed >0.Tile gravity for occupancy.X. Plan.Mis γ below.
lemma passportV(hQ:G.roundZ≤(mid n B).val)(I: Graph.Ledger h m₀ m₀ a C T)(k0:1≤ k)(lx:Invites k H (mid n B))(H0:PayR cₛ+2 ≤ h)
 (v₀:0< v)(f:0<a)(℘:0<μ)(d':μ ≤ 1)(w0:t=T.p.threshold)(he:t≤tH)
 (ch:0<v')(cc:0≤C)(w':w≤(More (mid n B)).val)(hi:T.p.threshold≤v')(z:2≤v'*Real.exp (a*w))
 (hx:0≤ d)(hn:0≤ C')(E:Casing (mid n B) d (blend k T.J false) c C' M)(F:Casing (mid n B) d (spar k T.J.M) c C' M)(ℵ:CoversU X Y w t x (M*α₁) g)(hg:r≤w)(O:2*tailCost c C' r+α₁*C'≤ ε)(Ψ: Currency Θ R μ e e' u cₛ T₁ P₁)(pC:0≤ cₛ)
 (Budge: BraWeight (stageL S Θ R μ T₁) (stageZ B₀ Θ R μ P₁) (twist (quantU (tradew (mid n B) g)) X') ≤ Real.exp X₀):
 ‖inner ℂ (mateK _) (acts X' (Graph.beam T G Y X))‖ ≤ Real.exp (
 Parcel.Tanin.photo_ψ k (mid n B) T.J.M + X₀ + BadgeK (CFolio e S + CFolio e' B₀) +
 (μ/2*H+v'^2*C)*((mid n B).val:ℝ)^4 +(3*m₀)*sites (mid n B)+ v*Fintype.card (Single (mid n B))+
 (BadgeKN u v)*Pilot.Ticket X t ε C' w + accrues w j C * once X t) :=by
 let S':= (mid n B); let J:= spar k T.J.M (Y X); let A:=stageL S Θ R μ T₁; let Z:=stageZ B₀ Θ R μ P₁; let V:= Vt; let Z':=V Z; let A':= V A; have hV:V Θ=Θ:= tick_g _
 have hz:=Ψ.buildZ (Gato.monograph B₀|>.symm); have hl:=Ψ.buildL (Gato.monograph S|>.symm); have hp':Milieu Θ A':=hV ▸ hl.glow (tradew S' g⁻¹); have hs':Spear Θ Z':=hV ▸ hz.twist_e (tradew S' g⁻¹)
 let T':=Graph.actF k T Y X; let M':=1+T'; let W:=Pall A Z; let B' := V W
 have hZ:Guard (Y X) d:=K.paid X; have hT:IsStarProjection J:= (G.broadness _ hQ T.J.M).projection _ hZ
 have he':T'*J=T':=by unfold T' Graph.actF CF.Kennel.capT; rw [mul_assoc, show _*J=J from hT.1]
 have ht:J*T'=0:=by unfold T' Graph.actF CF.Kennel.capT; change J*((1-J)*_*J)=_; rw [←mul_assoc,←mul_assoc,Porth hT,zero_mul,zero_mul]
 have hk:T'*T'=0:=by nth_rw 1 [←he']; rw [mul_assoc,ht,mul_zero]
 have hB:B'= Pall A' Z':= by unfold B' W A' Z' Pall; rw [map_mul,map_sub,map_one,map_star] -- good
 let T₀:= Pall (Lumi Θ R μ) (Zami Θ R μ); let Q':= V (T₀*R); let L':=blend k T.J false; have hM: M'*J=L' (Y X):= blend_motto _ hT; have hs:L' 1= R:=by unfold L'; rw [Brique.jewel]; unfold spar; rw [profile_trivial]
 let S₀:= Pilot.Ticket X t ε C' w; let i:= Ξ_; have pX:= Ψ.topP; have py:= Ψ.topE
 have hbadge: Ziz.Badge J M' (V R) B' Q' (18*u) (PayR cₛ) (300*i) (330*i) v S₀ :=by
    refine ⟨hT,pX.map V, egress Y X ℵ F hZ hx hg O,?_,by unfold M'; rw [mul_add,mul_one,ht,add_zero],?_,?_,(twist_norm ..).trans_le Ψ.fNormL,?_,v₀⟩
    · rw [hM,show V R=Pilot.tollX g (L' 1) from (by unfold Pilot.tollX; rw [hs])]; exact egress Y X ℵ E hZ hx hg O
    · unfold B' Q'; rw [←map_mul,←map_sub,show W*R-T₀*R=(W-T₀)*R from (sub_mul ..).symm]; exact (Ψ.cost_ready (S:=S) (T:=B₀)).twistP _
    · exact (twist_norm ..).trans_le (Rheims.authority Ψ.topE Ψ.topP Ψ.tLive Ψ.pace)
    unfold PayR; rw [show 270*(3*cₛ+2)=45*(6*(3*cₛ+2)) from by ring]; apply twist_cols
    · exact cellU.hegemon (A:=A) (b:=6) (fun i _=>Ψ.cellC i) Ψ.fee_turn
    positivity
 let j':= (m₀+m₀+m₀)*sites S'; let K':= (v'^2*C*(S'.val:ℝ)^4 + accrues w j C * once X t) -- placeholder
 let ρ:= 300*i; let E':= v*(Fintype.card (Single S'):ℝ) + Ziz.Badge.Pig (18*u) (300*i) (330*i) v S₀
 have hN:0≤h:= add_nonneg (payR_nn cₛ pC) zero_le_two|>.trans H0; let Y':= Y X; let f':= Parcel.Tanin.photo_ψ k S' T.J.M
 have he:‖acts (quant B') (Graph.beam T G Y X)‖ ≤ Real.exp (K'+(j'+E')):=by
    let x':= (changeM G Y' T.J.M); let q:Sea J x':= sea_g hQ _ hZ _; have hh: ‖Pec.pigment T.J.I (Y X)‖ ≤ K':= exactory X K he I.field.2 cc f ch (hi.trans' w0.le) w' z -- name
    let L:=Graph.beam T G Y X; rw [Graph.beam,Graph.mile,act_smul,act_mul,map_smul,norm_smul, tallied T' hk]; rw [Real.exp_add]; apply mul_le_mul _ _ (norm_nonneg _) (Real.exp_pos _).le
    · exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hh))
    exact (hbadge.bubble _ H0 q _ (backstage hN I X)).trans_eq (by rw [add_assoc]) -- tune binder
 have hA:‖acts (star (cost A' Z' X')) (mateK S')‖ ≤ Real.exp X₀:=(beyond g hl hz X').trans_le Budge
 have hℓ:-rueD A' ≤ f'+ μ/2*H*S'.val^4+i*8:=by
    obtain ⟨hr,gp,w,Hh,hℓ,Eℓ⟩:= lx.issued T.J.M g⁻¹ pX; -- g=1 proof twist
    let J:=spring Θ (Θ*R); have heJ:spring Θ (Θ*(V R))=V J:=(Spiny.town _ hV R).symm
    have hh:lit J:=iceT k0; have ht:TrR J⁻¹ ≤ H * S'.val^4:=by rw [heJ,show (V J)⁻¹ = V (J⁻¹) from Spiny.kinv _ hh] at w; exact le_trans (le_of_eq (Spiny.kTr _ _).symm) w -- hh implicit Q defeq
    let T':= Rheims.frost Θ R μ; have hv: rueD T'/2 ≤ f'+μ/2*H*S'.val^4:=by
       -- poem cost.Commute. call route_log
       have h1:= route_log (A:=T') (B:=J) Ψ.tLive hh; have hl:TrR (J⁻¹*(T'-J)) ≤ μ*(H*S'.val^4):=by
          have he: T'-J=μ • Θ:= by unfold T' J Rheims.frost Reduction.bloom; abel
          have hm:0 ≤ J⁻¹:= (lit_inv hh).1; rw [he]; apply ((abs_le.mp (TrR_quote hm _)).2).trans; rw [norm_smul,Real.norm_of_nonneg ℘.le]; exact mul_le_mul (mul_le_of_le_one_right ℘.le (py.norm_le _)) ht (TrR_nn hm) ℘.le -- typography Θ
       have h2:rueD J/2=f':=by rw [heJ,show rueD (V J) = rueD J from Spiny.klog _ _] at hℓ; exact hℓ
       linarith only [h1,h2,hl]
    unfold A'; rw [show rueD (V A) = rueD A from Spiny.klog _ _]; refine (Ψ.zRue ((Gato.monograph _).symm)).trans ?_; let A:= CFolio e S; let B:= CFolio e' B₀; have hb:0≤ B:= mul_nonneg Ψ.tinyB (by positivity); rw [show rueD (Lumi Θ R μ)=_ from rise_cost Ψ.tLive]; change -(-rueD T'/2) + A*8 ≤ _ + (A+B)*8; linarith only [hb,hv]
 apply (smokeX hp' hs' py (tickB _) X' (Graph.beam T G Y X)).trans; rw [←hB]; refine (mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr hℓ) hA (norm_nonneg _) (Real.exp_pos _).le) he (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)).trans_eq ?_; rw [←Real.exp_add,←Real.exp_add]; refine congrArg _ ?_; -- tune assoc
 unfold K' f' BadgeK i E' Ziz.Badge.Pig j' S₀ BadgeKN S'; ring
end Turnist
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
