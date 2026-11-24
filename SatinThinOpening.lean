import SatinThinShift
import SatinThinSifter

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- Overwrite the old unit & put in a NEW zero-shape price -/
variable {N B:Side}{J I:Type}[Fintype J][LinearOrder J][Fintype I][LinearOrder I]
attribute [-instance] instDecidableEqLex
local notation "Ω"=> mid N B
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
abbrev Prin(x:I): Article I:=phaseMark x 0
abbrev Astr(x:I): Article I:=phaseMark x 1
variable (U:Side)(X:GramM (mid N B))(p:I→ Site (mid N B))(q A h:ℝ)(E:Key (Article I)→ RegBudget (mid N B))(F:Key (Article I)→ ForceBudget (mid N B))(T: Fin 2→ Topic (mid N B))
local notation "P"=>X.p
local notation "Q"=> clothTable X.p q p
local notation "W"=> Bulletin
variable {T U X p q A h E F}
private lemma joined_price (z a:Υ)(x:Scree.Hub Ω)(w:∀ i, node (treeO p i)∈ x.val.2→ z i=a i)(i:Ξ)(v:node (treeO p i)∈ x.val.2): unison z i=unison a i ∧ strike z i=strike a i:=by
 unfold unison strike; rw [w i v,w (toGap i) v]; simp
-- General lemma actual density along *reindexed/scaled* keys arbitrary whole hill.
variable {K:Teller SU.group}{L:ChartRatio SU.group}{R:Patch}(V: Grace K R L){d:ℝ}(P_:Grasp V.U B d)(Lo:Scree.Loom (mid N B))
lemma chapter (a:Notice (treeO p) E F)(x:Orbit (mid N B))(U:Key J→Key (Article I))(u:Differentiable ℂ U): River (fun z=> Scree.denZ (dayShift X E F (U z)) P_ Lo x):=by
 let A':Key J→RegBudget Ω:= fun z=>X.F+E (U z); let F':Key J→ForceBudget Ω:=fun z=>X.K+ F (U z); let T':= fun _:Key J=>X.slip; let ℓ: J→Unit:=fun _=>()
 have hp {C: Type}[NormedAddCommGroup C][NormedSpace ℂ C][CompleteSpace C]{f:Key J→C}(p: River f): Law_C ℓ 0 [] f f:= ⟨p,p,fun i u=>by rw [List.sublist_nil.mp u]; rfl⟩
 refine (pulse_H V ℓ 0 [] (by simp [ψS]) X Lo A' A' T' T' F' F' (fun _=>X.v) (fun _=>X.v) x (fun i h=>hp ?_) (fun i x=>hp ?_) (fun i x=>hp ?_) (hp (zeroR _))).1
 · exact dub_V (zeroR (X.F _ _)) (river_all (fun z=>E (U z) i h) ((a.varE _ _).comp u)) -- needs explic
 · exact zeroR _
 exact dub_V (zeroR (X.K _ _)) (river_all (fun z=>F (U z) i x) ((a.varF _ _).comp u))
-- open bulletin
variable (u:Bulletin U X p E F h 2 (4*A) (A/8) q T)(t:Bulletin U X p (clothTable X.p q p) 0 h 2 (4*A) (A/8) q (clothSet X.p q))
variable (X E q p) in
def openTabs (z:Υ): RegBudget (mid N B):= E (unison z) + clothTable X.p q p (strike z)
def cyanRank (Pp:BudgetPoint)(q:ℝ)(T:Fin 2→ Topic Ω) (i:Fin 2): Topic Ω:=if i=0 then T 0 else (T 0).join ((clothSet Pp q 0).scale (-1))
#print openTabs
-- notation correct order
local notation "Zq"=> openTabs X p q E
local notation "Fq"=> F ∘ unison
include u t
lemma line_pr (i:I)(w:ℂ): Zq (update 0 (Prin i) w)=w • νTip E (Prin i) ∧ Fq (update 0 (Prin i) w)= w • emberTip F (Prin i):=by
 unfold openTabs Function.comp; rw [strike_update0,strike0, t.roll.1,add_zero,together 0 w (Prin i) (fun _ _=>rfl),unison0]; exact u.head ..
lemma line_pg (i:I)(w:ℂ): Zq (update 0 (Astr i) w)=w • (νTip E (Prin i)-νTip Q (Prin i)) ∧ Fq (update 0 (Astr i) w)= w • emberTip F (Prin i) :=by
 unfold openTabs Function.comp; rw [strike_update1,strike0,(t.head (Prin i) _).1,together 0 w (Astr i) (fun _ _=>rfl),unison0,show toPrin (Astr i)=Prin i from rfl,(u.head (Prin i) w).1, (u.head (Prin i) w).2]; rw [neg_smul,smul_sub]; abel_nf; simp
-- for enabling tip results without differentiation chain.
omit u t in
private lemma line_tip {E: Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f:Key J→ E)(p: River f)(x:E)(i:J)(t:∀ y:ℂ,f (update 0 i y)=y • x): tipI f [i]=x:=by
 rw [show tipI f [i]=cutI f i 0 from rfl,←(mitt p roots i).deriv, funext t]; simpa using ((hasDerivAt_id' (0:ℂ)).smul_const x).deriv
lemma dif_Pr (x:Scree.Hub Ω)(V:Pane Ω):Differentiable ℂ (fun z=> Zq z x V):=((u.varE x V).comp note_dif).add ((t.varE x V).comp strike_dif)
omit t in
lemma dif_Pg (x:Force Ω)(V:Orbit Ω): Differentiable ℂ (fun z=> Fq z x V):= (u.varF x V).comp note_dif
lemma tip_Pr (i:I):νTip Zq (Prin i)=νTip E (Prin i) ∧ νTip Zq (Astr i)=νTip E (Prin i)-νTip Q (Prin i)∧ emberTip Fq (Prin i)=emberTip F (Prin i) ∧ emberTip Fq (Astr i)=emberTip F (Prin i):=by
 refine ⟨funext₂ fun x y=>line_tip _ (river_all _ (dif_Pr u t x y)) _ _ (fun w=> congrFun (congrFun (line_pr u t i w).1 x) y),funext₂ fun x y=>line_tip _ (river_all _ (dif_Pr u t x y)) _ _ (fun w=> congrFun (congrFun (line_pg u t i w).1 x) y),funext₂ fun x y=>line_tip _ (river_all _ (dif_Pg u x y)) _ _ (fun w=> congrFun (congrFun (line_pr u t i w).2 x) y),funext₂ fun x y=> line_tip _ (river_all _ (dif_Pg u x y)) _ _ (fun w=> congrFun (congrFun (line_pg u t i w).2 x) y)⟩
lemma opening_tabs (e:0≤h)(x:0≤q)(v:0 ≤ A): Bulletin U X p Zq Fq h 1 (16*A) A q (cyanRank X.p q T):=by
 have he:= mul_nonneg v x
 refine ⟨⟨?_, fun i a b w=>?_, dif_Pr u t, fun i a b w=> ?_,dif_Pg u,fun i z=>?_⟩,fun z q=>?_,fun i=>art_fork (p:=fun i=> Axon U.val (treeO p i) X.p (νTip Zq i) h (A*q) (PointSk (readFee q (layer i))) ∧ (cyanRank X.p q T (layer i)).face (treeO p i) (νTip Zq i) (emberTip Fq i)) ?_ ?_ i⟩
 · unfold openTabs Function.comp; rw [strike0,unison0,u.roll.1,t.roll.1,u.roll.2]; simp
 · exact congrArg₂ HAdd.hAdd (u.col i (unison a) (unison b) (fun k v=> (joined_price a b i w k v).1)) (t.col i (strike a) (strike b) (fun k v=>(joined_price a b i w k v).2)) -- arguments implicit pattern
 · exact u.joinF i (unison a) (unison b) (fun k v=> (joined_price a b _ w k v).1)
 · rw [recover_art i]; generalize layer i=j; generalize host i=x; fin_cases j
   · obtain ⟨hz,_,hq,_⟩:=tip_Pr u t x; exact ⟨(line_pr u t x z).1.trans (congrArg (z • ·) hz.symm),(line_pr u t x z).2.trans (congrArg (z • ·) hq.symm)⟩ -- might need proof args
   have p:= (tip_Pr u t x).2; exact ⟨(line_pg u t x z).1.trans (congrArg (z • ·) p.1.symm),(line_pg u t x z).2.trans (congrArg (z • ·) p.2.2.symm)⟩
 · have hs(i:Ξ):‖unison z i‖≤2 ∧ ‖strike z i‖≤2:=by
      unfold unison strike; split; · rw [norm_neg]; exact ⟨(norm_add_le ..).trans (by have e:= q i; have ht:= q (toGap i); linarith only [e,ht]),(q _).trans one_le_two⟩
      simp
   obtain ⟨x,p⟩:=u.cover (unison z) fun i=>(hs i).1
   exact ⟨Provides.liftE _ X _ _ (Larch.add_v _ _ _ x (t.cover (strike z) (fun i=>(hs i).2)).1) (by linarith),Provides.liftQ _ X _ _ p (by linarith)⟩
 · intro i; change Axon U.val (treeO p (Prin i)) X.p (νTip Zq (Prin i)) h (A*q) (PointSk (readFee q (layer (Prin i)))) ∧ (cyanRank X.p q T (layer (Prin i))).face (treeO p (Prin i)) (νTip Zq (Prin i)) (emberTip Fq (Prin i)); obtain ⟨t0,_,t1,_⟩:=tip_Pr u t i; rw [t0,t1,show layer (Prin i)=0 from rfl,show cyanRank X.p q T 0= T 0 from if_pos rfl] -- layer
   exact ⟨turf_A _ _ _ _ _ _ _ (by linarith) (u.boss (Prin i)).1,(u.boss (Prin i)).2⟩
 intro i; change Axon U.val (treeO p (Astr i)) X.p (νTip Zq (Astr i)) h (A*q) (PointSk (readFee q (layer (Astr i)))) ∧ (cyanRank X.p q T (layer (Astr i))).face (treeO p (Astr i)) (νTip Zq (Astr i)) (emberTip Fq (Astr i)); obtain ⟨_,a,_,r⟩:=tip_Pr u t i
 have hV:= real_E _ (-1) (t.boss (Prin i)).1 e; have hτ:= Axon_add _ _ _ (u.boss (Prin i)).1 hV e; have ht:= topic_join (u.boss (Prin i)).2 (topic_scale (-1) (t.boss (Prin i)).2)
 rw [a,r,show layer (Astr i)=1 from rfl,show cyanRank X.p q T 1= (T 0).join _ from if_neg (by decide)]
 rw [point_Z,point_Zadd,neg_one_smul] at hτ; rw [neg_one_smul,show emberTip (0:Key (Article I)→ForceBudget Ω) (Prin i)=0 from funext₂ fun i x=>Mew.tip_0 _,smul_zero,add_zero] at ht -- after rewriting _ with wildcard? tune
 simp only [show layer (Prin i)=0 from rfl,(read_up (A)).1] at hτ ht
 rw [(read_up q).1,neg_one_mul,add_neg_cancel,abs_neg,abs_one,one_mul] at hτ
 change Axon _ _ _ _ _ _ (PointSk (readFee q 1))∧_
 rw [(read_up q).2,sub_eq_add_neg]
 exact ⟨turf_A _ _ _ _ _ _ _ (by linarith) hτ,ht⟩
omit t
lemma loosen_tabs (x:0≤q) (e:0≤A): Bulletin U X p E F h 1 (16*A) A q T:=by
 have h:=mul_nonneg e x; refine ⟨u.toNotice,fun z p=>?_,fun i=> ⟨turf_A _ _ _ _ _ _ _ (by linarith only [h]) (u.boss i).1,(u.boss i).2⟩⟩
 obtain ⟨X',F⟩:=u.cover z fun i=>(p i).trans one_le_two; exact ⟨Provides.liftE _ X _ _ X' (by linarith), Provides.liftQ _ X _ _ F (by linarith)⟩
#print axioms opening_tabs
end YM.CF.QuadClock
