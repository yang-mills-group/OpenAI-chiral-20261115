import YM.CF.BPress.Mount.Rosin
/- pointwise phase identity after Mark consumes primary and weak terms beyond gaps. Exact on all support irradiations. Compatible-slate provision implicit in using charge. $u0 scale Eq remains until apply on Reality$. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums --
variable {s m B N:Side} {D:BandWidth} {T: Sheet.Atlas}{X Y Z W:Pledge}{a:ℕ}{c d L y u v μ q ε:ℝ}{R:Driver (mid m B)}{P: Edition R}{G:Brace.Duet m B}{U:GramM (mid m B)}{p:Wish R X Y Z}
variable {K:Type}{g:K→R.Pose} (A:Bands (More (mid m B)) D)(F:Net (More (mid m B)) T L y c d a) (h:Tiling (More (mid m B))) (C:Calyx P g) (r:ℕ)
local notation "A0"=> Theatre (mid m B)
open Awards Silhouette
local notation "Λ"=> (mid m B)
variable (s:List A.Index)(x:Orbit (mid m B))(U': A.Slates)(w:K)(z:Shot (mid m B))
def ShotZ (A:Bands (More N) D)(u:ℝ)(x:Orbit N)(T: Paint (More N))(k:Support N)(v: ActY N)(z:Rod N):Shot N:=⟨x,ringF z,yKick k (u:ℂ) v,Lily.vacancy A,T⟩
lemma shotBudget (A:Bands (More N) D) {u:ℝ}(h:0≤u)(x:Orbit N) (T:Paint (More N)) (P:Support N)(v:ActY N)(z:Rod N)(p:MatPlan T): (ShotZ A u x T P v z).inBudget u:=by
 refine ⟨fun i=> (Wheel.ζ_price (forcePart i) z).le,fun i=>?_,p⟩; change ‖yKick _ _ _ i‖≤ _; unfold yKick; split; next hx=> simp [Real.norm_of_nonneg h]
 rw [norm_zero]; exact h
variable (J:Passports R U G p P W q ε u μ v)(N0 : Seeing A F h r U' (g w) x)
local notation "ψz"=> (g w)
local notation "ℳ"=> R.decks
abbrev ηLog(p:R.Pose)(G:Brace.Duet m B):= Spire.zen (Spire.hum m B G p.val.G p.val.X)
abbrev duesF(U:GramM (mid m B))(v:R.Pose):=Pec.pigment U.J.I v.val.G
variable (k:Phys (mid m B))(H:Paint (More (mid m B)))(Y:Support (mid m B))
structure TrueSpin (R:Driver (mid m B))(k:Phys Λ)(G:Brace.Duet m B)(v:R.Pose):Prop where
 topk: Pf.Top (mood (R.decks.A v) (R.decks.M v)) k
 log_t: inner ℂ (holdα (R.decks.seat v) (R.decks.KG v)) k=Complex.exp (stark v-ηLog v G)
include J N0
lemma public_log (t: TrueSpin R k G (g w))(s:Held P U A r x z)(Z:z.inBudget u):
 let A':= Complex.exp (- ∑ i,notary A F h C r U' x i)
 A'* (Complex.exp (-duesF U ψz)*spinInner (holdα ((ℳ).seat ψz) ((ℳ).KG ψz)) k (opus U z.field 1 z.f ((ℳ).KG ψz) z.stampX ((ℳ).A ψz) z.j z.inserts))= Complex.exp (ΔRest A r P ψz z):=by
 intro α; let V:= holdα ((ℳ).seat ψz) ((ℳ).KG ψz); let h:= opus U z.field 1 z.f ((ℳ).KG ψz) z.stampX ((ℳ).A ψz) z.j z.inserts; let p:= spinInner V k h; let W:= Complex.exp (∑ i,P.logG i ψz z); have htZ:p=W*inner ℂ V k:= (div_eq_iff (t.log_t ▸ (Complex.exp_ne_zero _))).mp (J.wick_p ψz z Z k t.topk); have he:=Mount.dot A F ‹Tiling _› C r U' x w z J N0 s -- tune there? inside Mount -> ambiguous
 rw [show spinInner _ _ _=p from rfl,htZ,t.log_t,←he]; unfold α W; rw [←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]; congr 1; unfold duesF ηLog; ring -- tune order htZ nonzero
abbrev Ωmask (N: Side)(V: Support (More N))(x: Rod N):ℂ:= (Wheel.ζ V x)⁻¹
-- outer Z/Y phase factors recover physical. sign kept
abbrev ΘSpin (R:Driver (mid m B)) (P:Edition R) (U:GramM (mid m B))(ψ:R.Pose) (u:ℝ)(T:Paint (More (mid m B)))(W: Support (mid m B))(V:ActY (mid m B))(Z: Rod (mid m B)):ℂ := bill_phase (u:ℂ) V W * Complex.exp (ΔRest A r P ψ (ShotZ A u x T W V Z)) -- tune U placeholder future μmask
lemma combined (p':s.Nodup)(v:∀ i,i∈s)(T': TrueSpin R k G ψz)(ah:0<u)(V:Lily.Vase ((ℳ).KG ψz) H ((ℳ).seat ψz) (Lily.vacancy A) Y)(X:autograph A F h U' x H)(f:∀ (v:ActY Λ)(Z:Rod Λ), Held P U A r x (ShotZ A u x H Y v Z)):
 beamZ Λ (acts (readout (T:=T) (y:=y) A s (candid A F h C r) U' x.1) (Complex.exp (-duesF U ψz) • acts (tank ((ℳ).A ψz) (U.board x)) k))= ∫ Z:Rod Λ, Ωmask Λ (trueFlags U x) Z * (∫ v,ΘSpin A r x R P U ψz u H Y v Z∂ Wheel.coin (Site Λ))∂ Wheel.coin (Site (More Λ)):=by
 let M:= Complex.exp (-∑ i, notary A F h C r U' x i); let d:=Complex.exp (-duesF U ψz); let A':=((ℳ).A ψz); let S':=Lily.vacancy A; have ht:= pays_total A F H h s (d • acts (tank A' (U.board x)) k) x U' p' v X V.t'
 rw [mint_mark A F h C r s U' x p' v]; rw [act_smul]; rw [show beamZ Λ (M • _)=M*beamZ Λ (acts (readout (T:=T) (y:=y) A s (fun i=> Chalk.pairTest A i F h) U' x.1) (d • acts (tank A' (U.board x)) k)) from inner_smul_right ..]; rw [ht,inner_smul_right]; change M*(d*spinInner (holdα S' H) k _)=_; rw [phase_integral (u:ℂ) k V U x _ (by exact_mod_cast ah.ne') (show IsStarProjection A' from (ψz).property.state.proj)]; rw [←integral_const_mul, ←integral_const_mul]; apply integral_congr_ae; apply Eventually.of_forall; intro z; dsimp only; rw [mul_left_comm d, mul_left_comm M,← integral_const_mul,← integral_const_mul]; apply congrArg; apply integral_congr_ae; apply Eventually.of_forall; intro v; set X:= ShotZ A u x H Y v z; dsimp only; unfold engross ΘSpin; rw [mul_left_comm d,mul_left_comm M]; apply congrArg; exact public_log A F h C r x U' w X J N0 k T' (f v z) (shotBudget A ah.le x H Y v z V.t') -- tune 
end YM.CF.BPress.Mount
