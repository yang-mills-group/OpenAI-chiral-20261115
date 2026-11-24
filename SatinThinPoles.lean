import SatinThinPattern

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


/- Repeat the Topic after repricing. Extended qualifications. -/
variable {n:Side}
def Topic.scale (T:Topic n)(c:ℝ):Topic n where
 face x E F:=∃ d f,T.face x d f∧ E=c • d ∧ F=c • f
 color s h x y E V F W p:=by
    rintro ⟨d,f,r,rfl,rfl⟩ ⟨d',f',r',rfl,rfl⟩; obtain ⟨A,B⟩:= T.color s h x y _ _ _ _ p r r'; rw [smul_comm (bandSign s) c,smul_comm (bandSign s) c]; exact ⟨passingR.smul s A _,passingF.smul s B _⟩
def Topic.join (T U:Topic n):Topic n where
 face x E F:=∃ d f,T.face x d f∧∃ d' f',U.face x d' f'∧ E=d+d' ∧ F=f+f'
 color s h x y E V F W p:=by
    rintro ⟨d,f,r,d',f',r',rfl,rfl⟩ ⟨d0,f0,r0,d1,f1,r1,rfl,rfl⟩; obtain ⟨A,B⟩:= T.color s h x y _ _ _ _ p r r0; obtain ⟨C,D⟩:= U.color s h x y _ _ _ _ p r' r1; rw [smul_add,smul_add]; exact ⟨passingR.add s A C,passingF.add s B D⟩
lemma topic_scale {T:Topic n}{E F}{x}(c:ℝ)(v:T.face x E F): (T.scale c).face x (c • E) (c • F):=⟨E,F,v,rfl,rfl⟩
lemma topic_join {T U:Topic n}{E F E' F'}{x}(p:T.face x E F)(q:U.face x E' F') : (T.join U).face x (E+E') (F+F'):=⟨E,F,p,E',F',q,rfl,rfl⟩
lemma point_Z (a b:ℝ) : a • PointSk b=PointSk (a*b):=Prod.ext (smul_smul ..) (smul_zero ..)
lemma point_Zadd (a b:ℝ): PointSk a+PointSk b=PointSk (a+b):=Prod.ext (add_smul ..).symm (add_zero _)

variable {J I: Type} [Fintype J][Fintype I][LinearOrder J][LinearOrder I]
variable {N P B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{d u t q h Vp Va M D Yp BQ Rt Zt κp W VZ VX VY A:ℝ}
local notation "Ω"=>mid N B
local notation "Ξ"=>mid P B
local notation "uN"=>Domain N B
attribute [-instance] instDecidableEqLex
variable {r:I→Site (mid N B)}
def readFee (s:ℝ)(j:Fin 2):ℝ:=if j=0 then s else 0
variable (σ:J→Site (mid N B))
/-- Full hill for spending, unbounded complex key for regularity & own-root silence. -/
def Quiet {U V:Type}(g:J→U)(S:Finset U)(f:Key J→ V) : Prop:=∀ x y:Key J,(∀ i,g i∈S→x i=y i)→ f x=f y
lemma quiet_hush {U V:Type}{g:J→U}{S:Finset U}{f:Key J→ V}(w:Quiet g S f): Hush g S f:=fun z _ w' _ r=>w z w' r
lemma river_all {U:Type*} [NormedAddCommGroup U][NormedSpace ℂ U][CompleteSpace U](f:Key J→ U)(h:Differentiable ℂ f):River f:=by
 refine ⟨h.continuous.continuousOn,fun i p j x t=>?_⟩
 let k:= fun y:ℂ=> update i j y; have he: Differentiable ℂ k:= differentiable_pi.mpr (fun z=>by by_cases v:z=j<;>simp [k,v,differentiable_fun_id,differentiable_const])
 exact h.differentiableAt.comp x he.differentiableAt
structure Notice (E:Key J→RegBudget (mid N B))(K:Key J→ForceBudget (mid N B)):Prop where
 roll: E 0=0 ∧ K 0=0
 col: ∀ x: Scree.Hub (mid N B),Quiet (Cube.node∘σ) x.val.2 (fun z=> E z x)
 varE: ∀ x y, Differentiable ℂ (fun z:Key J=> E z x y)
 joinF: ∀ i:Force (mid N B),Quiet (Cube.node∘σ) i.val.1.val.2 (fun z=> K z i)
 varF: ∀ x y, Differentiable ℂ (fun z:Key J=> K z x y)
 head: ∀ i:J, ∀ w:ℂ, E (update 0 i w)=w • νTip E i ∧ K (update 0 i w)=w • emberTip K i
-- uses Topic while seating labels. Repetition OK (2 uses per call). W multiple =1 unit qualification, or 2 for stronger. H price. Real Ξ.
structure Bulletin (L:Side) (X:GramM (mid N B)) (p:I→Site (mid N B)) (E:Key (Article I)→RegBudget (mid N B))(K:Key (Article I)→ForceBudget (mid N B))(h W H A q:ℝ)(T:Fin 2→Topic (mid N B)):Prop extends Notice (treeO p) E K where
 cover: ∀ k:Key (Article I), (∀ i, ‖k i‖ ≤ W) → IncX primeU (E k) X.p h (H*q) ∧ Dark primeU (K k) X.p h (H*q)
 boss: ∀ i:Article I, Axon L.val (treeO p i) X.p (νTip E i) h (A*q) (PointSk (readFee q (layer i))) ∧ (T (layer i)).face (treeO p i) (νTip E i) (emberTip K i)
variable (V:Grace K R L)
variable {U:Grasp V.U B d} {G:Ratio (mid N B) (mid P B)}{S:StepData (Domain N B) (Domain P B)}{G₀:Scree.Loom (mid N B)}{G₁:Scree.Loom (mid P B)} {X:GramM (mid N B)}{Y:GramM (mid P B)}{Xp:Op SU.Slot}{q':Chi}
variable (Xo Yo:Key J→RegBudget (mid P B))(Zo:Key J→ForceBudget (mid P B))(Q:J→ℝ)(F:J→ArcΦ)(E:Key J→ RegBudget (mid N B))(Yf:Key J→ForceBudget (mid N B))(C:J→ArcΦ)(s:J→ℂ)
variable (Fz: Cause_P V U G S G₀ G₁ X Y Xo Yo Zo Xp q' u h Vp Va σ Q F E Yf C s M D Yp BQ Rt Zt κp)
local notation "Ψc"=> (Cube.node ∘ σ)
include Fz
variable (H:J→J→ℂ)
lemma tranquil_E (Ue:Scree.Hub (mid N B)): Quiet (Cube.node∘σ) Ue.val.2 fun z=> FlameX σ E H z Ue:=by
 intro z w t; unfold FlameX Gem_U Gem_Q; simp_rw [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]; have he(i:J)(u:(Cube.node∘σ) i∈ Ue.val.2):(toV_C (Cube.node∘σ) H z) i=(toV_C (Cube.node∘σ) H w) i:=sum_congr rfl fun j g=>congrArg (H i j*·) (t _ ((mem_filter.mp g).2 ▸ u));
 apply congrArg₂ _ (sum_congr rfl (fun i _=>?_)) (sum_congr rfl (fun i v=>?_)) -- tune
 · by_cases g:(Cube.node∘σ) i∈ Ue.val.2; rw [he i g]
   have hx: νΦX E {i} Ue=0:=by contrapose! g; exact (tiltP_S V σ E Yf Xo Yo Zo Xp Q F C s Fz _).2 _ g _ (Finset.mem_singleton_self _)
   rw [show νTip E i Ue=0 from (funext fun x=> (cue_1 _ _).symm.trans (congrFun hx x)),smul_zero,smul_zero] -- tone
 by_cases g:νΦX E i Ue=0; rw [g,smul_zero,smul_zero]; exact congrArg (· • νΦX E i Ue) (Finset.prod_congr rfl (fun j v=> he j ((tiltP_S V σ E Yf Xo Yo Zo Xp Q F C s Fz i).2 Ue g j v)))
lemma tranquil_K (x:Force Ω): Quiet (Cube.node ∘ σ) x.val.1.val.2 fun z=> FlameK σ Yf H z x:=by
 let U:=x.val.1.val.2; intro z w v; unfold FlameK Gem_K; simp_rw [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]; have he(i:J)(u:(Ψc) i∈U):(toV_C (Cube.node ∘σ) H z) i=(toV_C (Cube.node ∘σ) H w) i:=sum_congr rfl fun j t=>congrArg (H i j*·) (v _ ((mem_filter.mp t).2 ▸ u));
 refine congrArg₂ _ (sum_congr rfl (fun j _=>?_)) (sum_congr rfl (fun j _=>?_))
 · by_cases q: νΦK Yf {j} x=0; rw [q,smul_zero,smul_zero]; exact congrArg (· • νΦK Yf {j} x) (he j ((tiltP_S V σ E Yf Xo Yo Zo Xp Q F C s Fz _).1 _ q j (by simp)))
 by_cases y:νΦK Yf j x=0; rw [y,smul_zero,smul_zero]; exact congrArg (· • νΦK Yf j x) (prod_congr rfl (fun j h=>he j ((tiltP_S V σ E Yf Xo Yo Zo Xp Q F C s Fz _).1 _ y j h)))
lemma partK (i:J) : emberTip (FlameK σ Yf H) i=∑ j∈pipe_ζ Ψc i,H j i • emberTip Yf j:=by
 funext x y; let L:=FlameK σ Yf H; have hx:River (fun z=>L z x y):=by
    have ht':Roots.ψS Ψc [i]:=by simp [Roots.ψS]
    let w:=(axis_P V σ E Yf Xo Yo Zo Xp Q F C s Fz H [i] ht').2 x y; apply (river_minus (fun z => (X.K+L z) x y) (fun _=> X.K x y) w.2.1 (zeroR _)).cong; exact fun z _=> (add_sub_cancel_left (X.K x y) (L z x y)).symm
 rw [emberTip]; have ht':Roots.ψS Ψc [i]:=by simp [Roots.ψS]
 calc
    _ = tipI (fun z:Key J=> (X.K+L z) x y) [i]:=by
       symm; change tipI (fun z=> X.K x y+L z x y) [i]=_; rw [tip_A (zeroR (X.K x y)) hx, proper,zero_add]
    _ = _:=by rw [((axis_P V σ E Yf Xo Yo Zo Xp Q F C s Fz H [i] ht').2 x y).2.2 [i] (List.Sublist.refl _),fuelΦ,Roots.snow]; simp_rw [Finset.sum_apply]; rfl
lemma melt_F (z:Key J) : FlameK σ Yf H z = (∑ i:J,z i • emberTip (FlameK σ Yf H) i)+∑ i∈MixT σ,pine i (toV_C Ψc H z) • νΦK Yf i:=by
 unfold FlameK Gem_K -- careful RHS expanded Yf/H Flame all; use change
 change (∑ i:J, _ • _)+_= (∑ i:J,_ • emberTip (FlameK σ Yf H) i)+_; simp_rw [partK σ V Xo Yo Zo Q F E Yf C s Fz H]; refine congrArg₂ (·+·) ?_ rfl
 classical
 let L(i j:J):= z j • H i j • emberTip Yf i; have ht(i:J): (toV_C Ψc H z) i • νΦK Yf {i}=∑ j:J,if Ψc j=Ψc i then L i j else 0:=by
    rw [show νΦK Yf {i}=emberTip Yf i from funext₂ fun x y=>cue_1 _ i]; unfold toV_C; rw [Finset.sum_smul, ←sum_filter]; refine sum_congr rfl fun j _=>?_ ; unfold L; rw [smul_smul,mul_comm]
 have hy(i:J): z i • (∑ j∈ Roots.pipe_ζ Ψc i,H j i • emberTip Yf j)= ∑ j:J, if Ψc j=Ψc i then L j i else 0:=by rw [←sum_filter,Finset.smul_sum]
 simp_rw [ht,hy]; rw [sum_comm]; refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> by split_ifs <;> (first |rfl|expose_names; grind)

omit Fz
lemma diff_cost (i:J) : Differentiable ℂ (fun z:Key J=> toV_C Ψc H z i):= by
 unfold toV_C; exact Differentiable.fun_sum fun j _=> (show Differentiable ℂ (fun z:Key J=> z j) from differentiable_apply j).const_mul _
lemma diff_pine (i:Finset J) : Differentiable ℂ (fun z:Key J=> Mew.pine i (toV_C Ψc H z)):=by
 induction i using Finset.induction_on with
 | empty=> simp_rw [Mew.pine,prod_empty]; exact differentiable_const _
 | insert j i x ih=> unfold Mew.pine; simp_rw [prod_insert x]; exact (diff_cost σ H j).mul ih
lemma diff_E (x:Scree.Hub (mid N B))(y:Pane Ω) : Differentiable ℂ (fun z:Key J=>FlameX σ E H z x y):=by
 unfold FlameX Gem_U Gem_Q; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]; exact (Differentiable.fun_sum fun i _=> (diff_cost σ H i).smul (differentiable_const _)).add (Differentiable.fun_sum fun i _=> (diff_pine σ H i).smul (differentiable_const _)) -- order tune
lemma diff_Y (x:Force (mid N B))(y:Orbit Ω) : Differentiable ℂ (fun z:Key J=>FlameK σ Yf H z x y):=by
 unfold FlameK Gem_K; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply]; exact (Differentiable.fun_sum fun i _=> (diff_cost σ H i).smul (differentiable_const _)).add (Differentiable.fun_sum fun i _=> (diff_pine σ H i).smul (differentiable_const _))
lemma pine_null (i:Finset J)(v:1 < i.card): Mew.pine i (0:Key J)=0:=by
 obtain ⟨j,u⟩:= card_pos.mp (show 0 < i.card from by omega); exact Finset.prod_eq_zero u rfl
lemma pine_axis (i:Finset J)(v:i∈MixT σ)(j:J)(t:ℂ) : Mew.pine i (toV_C Ψc H (update 0 j t))=0:=by
 obtain ⟨x,u⟩ := (mem_filter.mp v).2; obtain ⟨a,ha,b,hb,h⟩ := Finset.one_lt_card.mp u
 have hφ: Ψc a≠ Ψc b:=fun z=> h (x ha hb z)
 have he(y:J)(χ: Ψc j ≠ Ψc y):toV_C Ψc H (update 0 j t) y=0:=sum_eq_zero fun x m=>by
    rw [Function.update_of_ne (fun g=>by subst x; exact χ (mem_filter.mp m).2)]; exact mul_zero _
 by_cases p: Ψc j= Ψc a
 · exact prod_eq_zero hb (he b (fun q=>hφ (p.symm.trans q)))
 exact prod_eq_zero ha (he a p)
include Fz
lemma flame_notice : Notice σ (FlameX σ E H) (FlameK σ Yf H):=by
 let Xk:= FlameX σ E H; let Yk:= FlameK σ Yf H; let f:= toV_C Ψc H
 have hp:= melt_H V σ E Yf Xo Yo Zo Xp Q F C s Fz H; have hk:= melt_F σ V Xo Yo Zo Q F E Yf C s Fz H
 have hz:f 0=0:=funext fun _=>sum_eq_zero (fun _ _=>mul_zero _)
 have htL(i)(h:i∈MixT σ): Mew.pine i (f 0)=0:=by rw [hz]; exact pine_null _ (mem_filter.mp h).2.2 -- param order
 refine ⟨?_,tranquil_E σ V Xo Yo Zo Q F E Yf C s Fz H,diff_E σ E H,tranquil_K σ V Xo Yo Zo Q F E Yf C s Fz H,diff_Y σ Yf H,?_⟩
 · constructor
   · rw [hp]; exact (congrArg₂ (·+·) (Finset.sum_eq_zero (fun _ _=> zero_smul ..)) (show Gem_Q σ E (f 0)=0 from Finset.sum_eq_zero (fun i h=>((congrArg (· • νΦX E i) (htL i h)).trans (zero_smul ..))))).trans (add_zero _)
   rw [hk]; exact (congrArg₂ (·+·) (Finset.sum_eq_zero (fun _ _=> zero_smul ..)) (Finset.sum_eq_zero (fun i h=> ((congrArg (· • νΦK Yf i) (htL i h)).trans (zero_smul ..))))).trans (add_zero _)
 intro i z
 let v:= update (0:Key J) i z; have hb (x)(t:x∈MixT σ): Mew.pine x (f v)=0:= pine_axis σ H x t i z
 have hU{D:Type}[AddCommMonoid D][Module ℂ D](p:J→D) : ∑ k:J,v k • p k=z • p i:= by
    rw [Finset.sum_eq_single i]; rw [show v i=z from update_self ..]; exact fun j _ p'=> by rw [show v j=0 from update_of_ne p' ..,zero_smul]
    simp
 constructor
 · rw [hp]; change _+ (∑ i∈MixT σ, _ • _)=_; rw [hU (νTip Xk), Finset.sum_eq_zero (fun i h=> by rw [hb i h,zero_smul]),add_zero]
 rw [hk]; rw [hU (emberTip Yk),Finset.sum_eq_zero (fun i h=> by rw [hb i h,zero_smul]),add_zero]
end YM.CF.QuadClock
