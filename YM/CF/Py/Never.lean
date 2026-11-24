import YM.CF.Py.Dame
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
variable{B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a α:ℝ)(p i N0:ℕ)(T:Month x a i p N0 V W)
-- ultra-weak diagonal. enough for Wick plus true RG any number of scales.
open CF.Mint
variable {N:Side}(q:Chi)(J:Robes N V W) (h:ℝ) (Ta:Warm V U W N0 J.n i p q J.k J.d J.roomX a h)
variable {L':ℕ→ℕ}{x':ℕ→ℝ}
open Graph
variable (P':∀ i',Season V a p i N0 q J h Ta (L' i') (x' i') i')
variable (tP:Tendsto x' atTop atTop)
include tP
lemma tails_n (F:ℕ→ℝ→ℝ)(v:∀ i,leash (x' i) i (F i)): Aqua (fun i=> (radiusB (x' i):ℝ)) (fun i=>F i (x' i)):=by
 let f(i):ℝ:= radiusB (x' i); have he:Tendsto f atTop atTop:= tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp tP)
 intro n; rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ (tendsto_inv_atTop_zero.comp he)
 filter_upwards [he.eventually_ge_atTop 1,eventually_ge_atTop n] with i q h; have hi:= v i; rw [norm_mul,Real.norm_of_nonneg (pow_nonneg (show 0 ≤ (radiusB (x' i):ℝ) from zero_le_one.trans q) _)]; exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ q h) (norm_nonneg _)).trans hi
omit tP in
abbrev rimZ(i:ℕ):=Vale.mesh ((seat_u V J (x' i) N0)*N) R.L 0
-- careful implicit section var x' uses Π.Monot.
local notation "NP"=> rimZ V N0 J (x':=x')
local notation "S'"=> (fun i=> mid ((rimZ V N0 J (x':=x')) i) B)
local notation "Q'"=> (fun i' :ℕ => (radiusB (x' i'):ℝ))
lemma front : Gray (lum x') (eur (fun i'=> mid (rimZ V N0 J (x':=x') i') B)) ∧ Gray (fun i' :ℕ => (radiusB (x' i'):ℝ)) (eur (fun i'=> mid (rimZ V N0 J (x':=x') i') B)) ∧ Tendsto (eur (fun i'=> mid (rimZ V N0 J (x':=x') i') B)) atTop atTop:=by
 let K₀:=Q'; let C:=eur (fun i=>mid (rimZ V N0 J (x':=x') i) B); let F:=lum x'; let c:=((N.val:ℝ)*2*B.val); have h0:0<(N.val:ℝ):=(by exact_mod_cast N.property); have hp:0<(B.val:ℝ):=(by exact_mod_cast B.property); have hz:0<c:=by unfold c; positivity
 have he:Tendsto K₀ atTop atTop:= tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp tP); let m:= (100+N0:ℝ); let y:ℝ:= ((J.h+W.n:ℕ):ℝ)+m+1; have ht:C=(fun i=> y*c + (m*c)*K₀ i):=by
    funext i; change (↑((mid (rimZ V N0 J (x':=x') i) B).val):ℝ)=_; rw [show rimZ V N0 J (x':=x') i=seat_u V J (x' i) N0*N from by simp [rimZ,Vale.mesh]]; change (↑((J.h+grainZ V W N0 (x' i)+1)*N.val*2*B.val):ℝ)=_
    unfold y m c K₀ grainZ; push_cast; ring -- mul_one coercion
 have hm:0 < m*c:=mul_pos (by unfold m; positivity) hz; have hu:Gray K₀ C:=by
    rw [ht]; exact (Gray.coef he (y*c)).add he ((Gray.coef he _).mul (Gray.arg he)) -- order
 let tT:=tc tP; have hC:Gray F K₀:= Gray.higher ((Gray.powG tT (Gray.arg tT) 2).add tT (Gray.coef tT 1)) (by
    filter_upwards with i; change ‖(radiusB (x' i):ℝ)‖ ≤_; rw [Real.norm_of_nonneg (by positivity)]; exact (Nat.ceil_lt_add_one (sq_nonneg (F i))).le)
 refine ⟨hC.up hu,hu,?_⟩; change Tendsto C _ _; rw [ht]; exact tendsto_atTop_add_const_left _ _ (he.const_mul_atTop hm) -- tune
local notation "P_"=> (fun i=> (P' i).X 0)
local notation "fA"=> fun i:ℕ=> (P' i).F 0 (x' i)
local notation "fK"=> fun i:ℕ=> (P' i).G 0 (x' i)
variable (ph:1 ≤ h)
include tP P' ph
set_option maxHeartbeats 800000 in
lemma mintS:Roe.WindS B (rimZ V N0 J (x':=x')) x' h (cashU W.C) (levelQ W.C) K.top.width K.top.paths K.top.clip.linear K.top.clip.direct 1 1 (fun i=>(P' i).F 0 (x' i)) (fun i=>(P' i).G 0 (x' i)) (fun _=>V.W.bar) (fun i=>(P' i).X 0):=by
 let ys(i):=x' i; let k(i):=P' i; have hy(i): (P' i).act 0=x' i:= (P' i).pay.day.unit; let S:=rimZ V N0 J (x':=x'); let T:=eur (fun i=>mid (S i) B)
 have hz(i):hat R.L (x' i) 0=x' i:=by simp [Vale.hat]
 have hv(j:ℕ):=((P' j).pay).mark 0
 have hT(j) : ((P' j).X 0).beta=x' j∧ ((P' j).X 0).p=(P' j).out.a 0 ∧ ((P' j).X 0).path=V.L.path (L' j-0)∧ ((P' j).X 0).funds=K.top.clip:=by
    obtain ⟨i,M,h,x,g⟩:= Charted.mem_p V a p i N0 _ _ _ _ J q _ _ (P' j).pay (Nat.zero_le _); exact ⟨i.trans (hy j),M,h,g⟩
 obtain ⟨pX,x,w⟩:= front V N0 J tP -- order variable(N0) ... tune
 have q1:Aqua T (fun i=> (P' i).F 0 (x' i)):= (tails_n tP (fun i=> (P' i).F 0) (fun i=> (P' i).alive)).through (tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp tP)) x
 have q2:Aqua T (fun i=> (P' i).G 0 (x' i)):= (tails_n tP (fun i=> (P' i).G 0) (fun i=> (P' i).worth)).through (tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp tP)) x
 have he:0 ≤ h:=zero_le_one.trans ph
 refine ⟨⟨one_pos,one_pos,tP,Eventually.of_forall (fun i=>by simp only [(hT i).1,one_mul]; exact Set.left_mem_Icc.mpr le_rfl)⟩,pX,w,q1,Gray.thin (tc tP) q2.shrinks, Gray.coef (tc tP) _, ph,level_p _,cash_v _,K.top.clip.tail_pos, ?_, Eventually.of_forall (fun j=>?_ )⟩ -- '_' clip positivity
 · have h:Nonempty PlaqAxes:=⟨⟨(0,1),by decide⟩⟩; obtain ⟨b,z,u⟩:=(V.L.mood 0).rows h.some; exact le_trans (tsum_nonneg b) u
 · let Q:=P' j; dsimp only; let D:= (P' j).pay; have ht:=Q.out.boot 0; rw [hz j] at ht
   have hC:= Charted.fondV V _ _ _ _ _ _ _ _ _ _ _ _ D (j:=0) (Nat.zero_le _) he
   rw [hz j] at hC; let L:= D.unit.costP 0 (Nat.zero_le _) (Nat.zero_le _); have hi:= hush_h L he; rw [hz j] at hi
   obtain ⟨X,Y,Z,P⟩:= hT j; exact ⟨Y ▸ ht.1,hC,by rw [P,Z]; exact V.L.mood _, le_of_eq (congrArg Clip.linear P.symm),le_of_eq (congrArg Clip.direct P),hi ⟩
end YM.CF.Py
