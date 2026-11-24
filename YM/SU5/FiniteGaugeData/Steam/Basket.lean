import YM.SU5.FiniteGaugeData.Steam.Hearth
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
open LocalLimit Window Jade.Earn Period Window.Steve Graph
namespace Steam
variable {s : Side} (A:Scree.GramM (mid m B)) (S:Scree.Loom (mid m B)) (O:Next.Rank.HaarBudget SU.group)
open Next.Rank
-- pack upper volume with a normalized k ratio. F=raw and S chosen at lawful pivot, W known.
abbrev frost (P:Clip)(x:ℝ):= oneFlag x*P.linear/4
lemma frostT(F:Clip): Tendsto (frost F) atTop atTop:=by
 have ht := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
 have he:Tendsto oneFlag atTop atTop:= by
    apply Tendsto.congr' ((eventually_gt_atTop (0:ℝ)).mono fun i p=> (flag_value p).symm)
    exact Real.tendsto_exp_atTop.comp ((ht.atTop_mul_atTop₀ ht|>.const_mul_atTop (show (0:ℝ)<2 by norm_num)).congr (by intro i; rw [sq]; rfl))
 exact (he.atTop_mul_const F.tail_pos).atTop_div_const (by norm_num : (0:ℝ)<4)
structure Flacon (W:GivenX V U)(A:Scree.GramM (mid m B)) (S:Scree.Loom (mid m B))(x h:ℝ)(O:HaarBudget SU.group) :Prop where
 stamp : BigHeart x
 set_p : A.p.threshold=temp x
 member: matchedX x A.beta
 clip_p : A.funds = K.top.clip
 gauge : A.path.Bounds A.funds K.top.width K.top.paths V.W.bar
 book : Graph.Ledger h (dleaf R.L x) (dleaf R.L x) (levelQ W.C) (cashU W.C) A
 outside : ∀ y: Orbit (mid m B), Graph.past A y.1 ≤ Real.exp (unlit A K.top.paths V.W.bar - (↑(Steve.misses y.1 (temp x)).card:ℝ)* frost K.top.clip x)*Real.exp (-basal A (soaked A.beta) y.1)
 budget: ∀ y: Orbit (mid m B), ‖Graph.beam A U S y‖ ≤ Real.exp (flagBill (mid m B) (dleaf R.L x) (dleaf R.L x) (cashU W.C))
 full_z: Real.exp (flagBill (mid m B) (dleaf R.L x) (dleaf R.L x) (cashU W.C))*fullRate O A K.top.paths V.W.bar (soaked A.beta) ≤ Real.exp (Fare x (mid m B) (costPlan V (cashU W.C) O))

variable {hA:ℝ} {N0 k n' :ℕ}{R0 δ:ℝ→ℝ}
private abbrev bCost(C:ℝ):=4*C+3*1*2^4+180*45*6*C
lemma glazed (χ:BigHeart (hat R.L x k))(q:Chi)(N0:ℕ)(R0 δ:ℝ→ℝ)(S:Session V 1 2 6 N0 J q h R0 δ x m n')(hp: k ≤ n') (ht:1≤h) (hE:dleaf R.L (hat R.L x k)≤1): Flacon W (S.E k) (S.Y k) (hat R.L x k) h O:=by
 let y:=hat R.L x k; let T:= temp y; let Z:= S.E k; let M:= cell m B R.L k
 let N:=massMeter M; let t:= Z.beta; let F:= soaked t; let w:=S.scale.note.owns k hp; let q':= S.val.boot k; have hZ:Z.p.threshold=T:=show _ from w.width ▸ q'.1; have he:Z.funds= K.top.clip:= w.fund.symm
 let hA:= S.scale.note.sift k hp; obtain ⟨p0,pC,tq,v,qb⟩:=χ.budget t hA
 have hβ: F ≤ Z.p.threshold:= hZ ▸ pC; obtain ⟨-,_,hu,b⟩:=amplifier t tq
 let β':=upperMoney O K.top.paths V.W.bar (strength K.top.clip) 1; let G:=cashU W.C; have hk:0≤G:= cash_v _; let γ0:= dleaf R.L y; let C:=bCost G
 let hO:= footprint_B V 1 2 6 N0 J q h R0 δ S k hp; let u:= loomActs V 1 2 6 N0 J q h R0 δ S k; let bT:=Period.expense V 1 2 6 N0 J q h R0 δ S k hp ht
 refine ⟨χ,hZ,hA,he,hO,bT,?_, fun x=>operator_all _ _ bT u (J.gran.trans (S.scale.roof _).size) ht ((level_p _).le) hk x,?_⟩
 · intro x; let n:ℕ:= (Steve.misses x.1 T).card; let X:=unlit Z K.top.paths V.W.bar; have hv: Graph.past Z x.1 ≤ Real.exp (X - n*Steve.blow Z.funds Z.beta Z.p.threshold) * Real.exp (-basal Z F x.1):= weight_X _ hO hu b hβ x.1 n (by rw [hZ]); apply hv.trans; refine mul_le_mul_of_nonneg_right (Real.exp_monotone (sub_le_sub_left (mul_le_mul_of_nonneg_left ?_ (show (0:ℝ) ≤ (n:ℝ) by positivity)) _)) (Real.exp_pos _).le
   change frost K.top.clip y ≤ Steve.blow Z.funds t Z.p.threshold; unfold frost Steve.blow oneFlag; rw [hZ,he]; nlinarith only [mul_le_mul_of_nonneg_right (show y/2 ≤ t from hA.1) (show 0 ≤ K.top.clip.linear*temp y^2 from mul_nonneg K.top.clip.tail_pos.le (sq_nonneg _))]
 have hv: |Real.log F|≤ N*1:=by rw [mul_one]; refine qb.trans ?_; exact le_trans (by push_cast; exact le_rfl : (radiusB (hat R.L x k):ℝ)+1≤ ((radiusB (hat R.L x k)+1:ℕ):ℝ)) (epochAffordable V 1 2 6 N0 J q h R0 δ S k)
 apply le_trans (mul_le_mul_of_nonneg_left (upperRate O Z (wing_budget V) hu b hv (hZ.symm ▸ p0) _ (strength_pos K.top.clip) (by rw [he])) (Real.exp_pos _).le)
 rw [←port_eq (hat R.L x k) (costPlan V (cashU W.C) O) Z,←Real.exp_add]; apply Real.exp_monotone; let s:ℝ:=SU.group.lieDim
 have he: strengthLog F ≤ strengthLog (soaked y)+s*2:= (mul_le_mul_of_nonneg_left v (Nat.cast_nonneg _)).trans_eq (mul_add s (Real.log (soaked y)) 2)
 have hu: 0≤N:=zero_le_one.trans (money_pos _); change flagBill M γ0 γ0 G+ N*(3*strengthLog F+β') ≤ N*(3*strengthLog (soaked y)+(C+(β'+s*2*3)))
 have hC: flagBill M γ0 γ0 G ≤ N*C:= flagBound _ 1 G _ _ hE hE zero_le_one hk; linarith only [hC, mul_le_mul_of_nonneg_left he hu]

open Preparation
-- era-based predicates for participants. Budget independent of s value here, level goes to right. high h permitted.
noncomputable abbrev oracle:= Classical.choice (Next.Rank.exists_budget SU.group)
variable {Λ:Preparation}{l:ℕ} {F : (s:Side)→ Scree.Loom s→Prop}(Y:Course Λ F) {j i:ℕ}(s:ℕ)
local notation "T" i:max=> Λ.Ctor (Y.ir i)
local notation "Fₛ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Λx"=> Λ.x
variable {g:ℝ}
local notation "W₀" i:max=> (Y.voyage i).CapeT
structure Club (Y:Course Λ F)(g:ℝ)(s:ℕ):Prop where
 full (i k:ℕ) (p:s ≤ Y.uv k) : Flacon Λ.W (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s) (hat Λ.R.L Λ.x s) Λ.h oracle
 lower (i k:ℕ)(p:(Y.voyage i).kick ≤ k)(u:s ≤ Y.uv k): Real.exp (Fare (hat Λ.R.L Λ.x s) (Λ.Ctor (Y.ir i) s) (-(2*g+1)))≤ ‖compensated Λ.U (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s)‖
include Y
lemma from_history (χ:BigHeart (hat Λ.R.L Λ.x s))(hE:dleaf Λ.R.L (hat Λ.R.L Λ.x s)≤1)(i k:ℕ) (e':s≤Y.uv k) : Flacon Λ.W ((Fₛ i k).gram s) ((W₀ i) s) (hat Λ.R.L Λ.x s) Λ.h oracle:=by
 let X:= Fₛ i k
 let U:Session Λ.V 1 2 6 Λ.N0 Λ.J Chi.canonical Λ.h Λ.R0 Λ.δ Λ.x (Y.ir i) (Y.uv k):= ⟨Y.meter,(Y.voyage i).funds,X.pilot,X.gram,W₀ i,X.wave,X.fee,Y.history i k⟩
 exact glazed oracle χ _ _ _ _ U e' Λ.height hE
lemma clubbed (r: Pitching.Focus.Kettle g Λ.J Λ.P Λ.N0 Λ.h Chi.canonical) (u:0 ≤ g) : ∀ᶠ s in atTop, Club Y g s:=by
 filter_upwards [(horizons (V:=Λ.V) Λ.x).eventually (moneyK'.and (((dev_R Λ.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds zero_lt_one))), away (kT:=r) Λ.H u Y.oneP Y.revenue] with i p v; exact ⟨from_history Y _ p.1 p.2,fun n k p=> v _ (Fₛ n k) ((Y.voyage n).paths _) ((Y.voyage n).lower k p)⟩
end Steam
end YM.CF.Py.Rate
