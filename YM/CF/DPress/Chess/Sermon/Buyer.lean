import YM.CF.DPress.Chess.Sermon.Festival
import YM.CF.Continuum.Algebra
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
open Lat Scroll Peaks
-- Learn.P1m not comparing to actual until evaluating with stove
structure Learn (W:Wall)(ℓ:ℕ)(A:HT n):Prop where
 bits : Lit W ℓ A
 envelope : Envelope A
 issue(i): RefineE (W.crop n (2*ℓ)) false (A i)
abbrev alight (K:Ratio n m) (x:Tour K):Stage n:= (x.2.1,x.2.2.2)
def crop_U (K:Ratio n m)(q: Chi)(l:ℝ)(x:Tour K) : Nom n m:= (seine K x.2.2.1 q l x.1.2 x.2.2.2, x.2.2.2)
local notation "R_" => W.crop n Wall.rail
local notation "Q_" => W.crop n ℓ
local notation "ΨA"=> W.boost K.count
namespace Scope
variable {L:Side}(X: Scope L K S P ℓ d)
variable {T:HT n}(h:Learn W ℓ T){q:Chi}{k:ℝ}{j:ℕ}{M:Tulip.Male}{v:Op SU.Slot}(g:Tide j M K d v (W.crop n (2*ℓ)))
def emit :Fold K (ReOp m):= fun x=> g.F (crop_U K q k x) (T (alight K x))
include h X
lemma emitHi : Hi W ℓ (emit W (q:=q) (k:=k) g (T:=T)) :=by
 obtain ⟨k₁,u₁,r,p,v,h₂⟩:= X.goodP; let H:=twig (ratio K) (Q_); intro i w v; let Z:=crop_U K q k; let l:=Wall.Lot_u K p (show 4≤K.count.val from (X.medi.symm ▸ X.hl)); have hx:H⊆ (ΨA).crop _ (2*ℓ):= W.pay_c K l; have hp:T (alight K i)=T (alight K w):= h.bits _ _ ⟨v.2.1, agrees_mono (show Agrees (Q_) _ _ from v.2.2.2) (Finset.coe_subset.mpr (W.grade (by omega : ℓ ≤2*ℓ) n))⟩ -- tune Agrees type
 unfold emit; rw [hp]; exact (g.issue _ (h.issue _)).Port _ _ (agrees_mono (Bough.seine_t q k (X.medi.symm ▸ X.odd) (S:= Q_) v.2.2.2 (agrees_mono v.1.2 (Finset.coe_subset.mpr hx)) v.2.2.1) (Finset.coe_subset.mpr (W.spread K (Wall.Lot_p p))))
lemma emit_I (x:Tour K):RefineE ((ΨA).crop m (2*ℓ)) false (emit W (T:=T) (q:=q) (k:=k) g x):=by
 obtain ⟨k₁,u₁,r,p,v,h₂⟩:= X.goodP; have ht:= (g.issue _ (h.issue (alight K x))).FineF (crop_U K q k x); apply Window.fine_enlarge _ (ht); -- import Mirror? avoid implement
 have hp : spreadB K (W.crop n (2*ℓ)) d ⊆ (ΨA).crop m (2*ℓ):= Subset.trans (W.spread K (Wall.Lot_p p)) (W.pay_c K (Wall.Lot_u K p (X.medi.symm ▸ X.hl))); exact fun x v=> (Fixed.mem_matterRegion ..).2 (hp ((Fixed.mem_matterRegion ..).1 v))
omit X h
lemma mane (p:0<k)(t:2*k < Next.SectorChange.firstRadius SU.group): Measurable (crop_U K q k):=by
 let f(X:Tour K):= X.2.2.1; let w(X:Tour K):= X.1.2; let x(X:Tour K):= X.2.2.2; let z:=fun (i:Forest (ratio K))(j:Tour K)=> seine K i q k (w j) (x j)
 let F:Measurable (Prod.snd:Tour K→Pane n × Ticket K):=measurable_snd (α:=Stage m) (β:=Pane n × Ticket K); have he:Measurable f:=by change Measurable (Prod.fst (β:=Pane n) ∘ Prod.snd (α:=Pane n) ∘ Prod.snd); exact measurable_fst.comp (measurable_snd.comp F)
 have ht:Measurable x:=by change Measurable ((Prod.snd (β:=Pane n)) ∘ Prod.snd (α:=Pane n) ∘ Prod.snd); exact measurable_snd.comp (measurable_snd.comp F);
 have hl : Measurable w:= by change Measurable ((Prod.snd (β:=Pane m)) ∘ Prod.fst); exact measurable_snd.comp measurable_fst;
 have hj(i:Forest (ratio K)):Measurable (z i):=by change Measurable ((uncurry (seine K i q k)) ∘ fun s=>(w s,x s)); exact Measurable.comp (brake K q k i p t).measurable (hl.prodMk ht)
 exact (mealM (fun i=>he (measurableSet_singleton i)) hj).prodMk ht
lemma fpCouple{X Y Z A:Type*}[TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X][CompactSpace X][SecondCountableTopology X][NormedAddCommGroup Y][ProperSpace Y][SecondCountableTopology Y][MeasurableSpace Y][BorelSpace Y][NormedAddCommGroup Z][MeasurableSpace Z][BorelSpace Z][MeasurableSpace A] (f:X×Y→Z)(l: A→X)(g:A→Y)(h: Measurable l)(v:Continuous f) (p: Envelope g) :Envelope fun x=> f (l x,g x):=by
 have ht:= Env.coupled h p _ v.norm; obtain ⟨C,k⟩:= ht.cost; exact ⟨v.measurable.comp (h.prodMk p.meas),C,fun x=> (Eq.symm (Real.norm_of_nonneg (norm_nonneg (f (l x,g x))))).trans_le (k x)⟩
include h in
lemma emits (p:0<k)(t:2*k < Next.SectorChange.firstRadius SU.group): Envelope (emit W (T:=T) (q:=q) (k:=k) g):=fpCouple (fun x:Nom n m × ReOp n=> g.F x.1 x.2) (crop_U K q k) (fun x=> T (alight K x)) (mane p t) ((g.nature.comp continuous_fst).clm_apply continuous_snd) (Env.along h.envelope (g:=fun x:Tour K=> alight K x) ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))))
include h X
variable [Nonempty (Forest (ratio K))]
lemma grav (p:0<k)(t:2*k< Next.SectorChange.firstRadius SU.group)(β:ℝ): Learn (ΨA) ℓ (guide S β P (emit W (T:=T) (q:=q) (k:=k) g)):= by
 let A:=emit W (T:=T) (q:=q) (k:=k) g; have he:Envelope A:= emits W h g p t; exact ⟨X.trip W he (X.emitHi W h g) β,housing X.kernel X.fee_m he β,X.estate he (X.emit_I W h g) β⟩ -- tune
end Scope
end YM.CF.DPress.Chess.Sermon
