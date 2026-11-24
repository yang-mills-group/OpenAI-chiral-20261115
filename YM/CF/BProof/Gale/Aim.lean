import YM.CF.BProof.Gale.Folio
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
open Arbor
open Wager Frost Half Leg Rush Tulip Peaks TripD Scree Tap Haro ArborW RillW
namespace Gale
variable {N P:Side}{F G:Orbit N → Pane N}{a:ℝ} {R:Patch} {r l k:ℕ}
variable (i:Axis)(X: ClockD R r l k)
local notation "X_" t:max=> shade N i t X.gF -- names pos use
local notation "Xs" b:max=> shade N i b X.pF
local notation "Γs" b:max=> shade N i b X.uF
attribute [local instance] Wager.measureVal Wager.billVal
open Push.SectorMeasure -- Chi
variable (B:Ratio N P) (q:Chi) (z:ℝ) {T:StepData (More N) (More P)}
variable {W V:Part N P} {b:Bool}
variable (RT:T.patch=R) (h:T.ratio=ratio B) (hp:B.count=R.L) (t:0<z)(v:2*z < Next.SectorChange.firstRadius group)
variable {τ n:ℕ}{c e:ℝ}(L:Roof N c e l F) (Q: Vogue.Quartz N τ a l F)
-- preserve support under heal
variable (p:T.patch.Branches T.kernel SU.group) (β:ℝ)
section lift
variable {Y:Body N}(u:Soul i X Y) {j:ℕ}{Gm:Male}{Qm:SpaceM} (W':Rider (shade N i true X.uF) (Leg.reach B (shade N i true X.uF) k) i B j Gm Qm)
local notation "R_" => Γs true
local notation "Rι" => winter R_ false
abbrev footW(x:PairD N):Rι:=⟨Y x, u.free x⟩
def poleM:Part N P:= fun x=> W'.W (footW i X u x)
local notation "Πψ"=> poleM i X B u W'
local notation "Ωψ"=> wince B q z Πψ
private lemma trim_w{α β Y Z:Type}[MeasurableSpace α][MeasurableSpace β][TopologicalSpace β][CompactSpace β][SecondCountableTopology β][BorelSpace β][NormedAddCommGroup Y][ProperSpace Y][MeasurableSpace Y][OpensMeasurableSpace Y][NormedAddCommGroup Z][ProperSpace Z][MeasurableSpace Z][BorelSpace Z]{W: Y → β→ Z}(p:Continuous (Function.uncurry W))(F:α→Y)(h:Envelope F):Envelope (Function.uncurry (fun x=>W (F x)) ) := by
 obtain ⟨c,k⟩:= h.cost; obtain ⟨Z,l⟩:=((isCompact_closedBall (0:Y) c).prod (isCompact_univ (X:=β))).bddAbove_image p.norm.continuousOn; exact ⟨p.measurable.comp ((h.meas.comp measurable_fst).prodMk measurable_snd),Z,fun x=>l ⟨(F x.1,x.2),⟨(by rw [Metric.mem_closedBall,dist_zero_right]; exact k _),Set.mem_univ _⟩,rfl⟩⟩
lemma per_prec : Pear X i B true Πψ:=by
 let W0:=footW i X u; refine ⟨?_,fun U x y h v=>congrArg (fun k:Rι => W'.W k U) (Subtype.ext (u.bit x y h v)), fun x=> (W'.fee _).y⟩
 have he:Measurable W0:= u.env.meas.subtype_mk; exact trim_w W'.OK W0 ⟨he,u.env.cost⟩

local notation "Tμ"=>shade P i true X.uF
variable [hN:Nonempty (Forest (ratio B))]
include hN t v h hp
lemma poleWin (x: PairD N)(V:Pane P): Snow (shade P i true X.uF) false (Ωψ x V):=by
 let F(a:Forest (ratio B)):= generalizeP B q z Πψ a x V; let T':=winter Tμ false; change meanS _ F∈ T'; exact Wager.fund_s _ (T'.restrictScalars ℝ) (Wager.mean_f _) (fun y=> snown (X.fern i B hp true) ((W'.fee _).t _)) -- include unused t v h
local notation "Fθ"=> fuel T β F
include Q L p RT
lemma learnC : Soul i X (Fθ Ωψ):=by
 let W:= Πψ; have he:= per_prec i X B u W'; let Γ:=Ωψ; have hf:= winceC B q z t v he.envy
 refine ⟨carries L p β Γ hf, local_a i X B RT h hp L Q p β (winceP i X B q z h hp he) hf,fun x=>?_⟩
 let U:=(winter Tμ false).restrictScalars ℝ; let H:=upheld L p x.2 Γ hf
 refine Wager.abr (prior group (More N)) U H (RillW.density_E T p β x.1) ?_; intro y; let A(z: Ids N):= Γ (y,F (y,z)) x.2; have hx:Envelope A:= Law.pull (f:=Function.uncurry Γ) (q:=fun z : Ids N=>((y,F (y,z)),x.2)) hf (by have hF:=L.bill.comp (measurable_prodMk_left (x:=y)); exact (measurable_const.prodMk hF).prodMk measurable_const); exact Wager.fund_s _ U hx fun l=> poleWin i X B q z h hp t v u W' _ _ -- tune
omit RT t v L p Q hN
lemma windowF (V U:Part N P) (b:Pear X i B false V)(c:Pear X i B true U)[Nonempty (Forest (ratio B))]: wince B q z (V*U)=wince B q z V*wince B q z U:=by
 ext x y :2; have hL :0<X.pF:=by have h:=X.duty; have ht:=X.pos; omega
 exact Arbor.voteP (fun f=>generalizeP B q z V f x y) (fun f=>generalizeP B q z U f x y) (splits (N:=N) i false hL) (b.songE h hp _ _) (c.songE h hp _ _)
include t v p Q L hN
lemma rustic (W: Part N P)(u:Pear X i B true W):let K:=wince B q z W; Fθ (wince B q z (Travel i W*W))= sqR i (Fθ K):=by
 let f:= Travel i W; let K:=wince B q z W; let K':=wince B q z f; have hZ:Pear X i B false f:= turnP i X B u; intro K; rw [windowF i X B q z h hp f W hZ u,term i X L Q p β K' (wince B q z W) (winceP i X B q z h hp hZ) (winceC B q z t v hZ.envy) (winceP i X B q z h hp u) (winceC B q z t v u.envy)]; unfold K' f; rw [tallyX i B q z h W, mantle i L p β K (winceC B q z t v u.envy)]; rfl -- introduced K name collision
end lift
end Gale
end YM.CF.BProof.Bide
