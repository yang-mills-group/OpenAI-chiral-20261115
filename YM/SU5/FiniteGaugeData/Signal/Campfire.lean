import YM.SU5.FiniteGaugeData.Signal.Composer
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic
namespace Play
variable {n m:Side}{a b c u v H g W:ℝ}{j k d:ℕ}
variable (o:Seat n)(f: SU.Slot)(i:List (Site n))(F:Finset (Site n))
local notation "B" r=> bay (terr (More n)) o r
local notation "Φ"=> family f
local notation "S'"=> floors o F k
lemma patch_size(g:Plum.Troupe n) {S:Support (More n)} {x:Ket (Single n)} (p:withinM (colorWall S) x):withinM (colorWall S) (acts (star (tradew n g).val) x) := by
 apply sectorwiseCut _ p; rintro ⟨i,l⟩ p ⟨j,b⟩ u; rw [Matrix.star_apply]; by_cases h:i=j; · subst j; exact False.elim (u ((locate_wall ..).2 ((locate_wall S ((i,l):Single n)).1 p)))
 simp [tradew,jump_apply,h]
lemma port_size(S:Support (More n)): colorWall S=modesIn n S:= by ext; rw [locate_wall,modes_at]

variable {T:Support (More n)}{V k0 k1:ℕ}
variable {M:Male}{A: Aim n} (K:Site n→ Ket (Single n)) (s:∀ v∈F, Column (bay (terr (More n)) o k) j M f F H a c (Baby f v) (K v))
-- Budget around mask acquisition; enough supports
variable (R:Pane n→Plum.Troupe n)(e:∀ x∈i, x∈F)
variable (l:k ≤ V)(t:LocalOn (bay (terr (More n)) o V) R)

def rise (V:Pane n)(x: Ket (Single n)):=acts (star (tradew n (R V)).val) x
def rpair (v:Site n)(x:Pane n):= Fock.remove (rise R x (Baby f v))*create (acts (cutM (Tset n)) (rise R x (K v)))
def yoke (V:Pane n) := (i.map (fun j=>rpair f K R j V)).prod

def radiant (T:Support (More n))(g:ℝ): Mark n:= toMark (maskT T g (fun x=> (i.map (fun j=>1+rpair f K R j x)).prod))
def flames (T:Support (More n))(g:ℝ): Mark n:= toMark (maskT T g (yoke f i K R))
lemma rise_cont (v:Ket (Single n))(h:Measurable R): Measurable (fun x:Pane n => rise R x v) :=by
 unfold rise; refine Continuous.measurable (f:=fun g: Plum.Troupe n=>acts (star (tradew n g).val) v) ?_ |>.comp h
 exact ((acts_cont.comp (continuous_star.comp (Plum.twistContinuous (N:=n)))).clm_apply continuous_const) -- tune
lemma rpair_meas(u:Site n)(h:Measurable R): Measurable (rpair f K R u):= by unfold rpair; apply Measurable.mul; exact (continuous_star.comp create_cont |>.measurable.comp (rise_cont R (Baby f u) h)); exact (create_cont.comp (acts (cutM (Tset n))).continuous).measurable.comp (rise_cont R (K u) h)
lemma local_pair {S:Support (More n)}(u:Site n)(p:LocalOn S R): LocalOn S (rpair f K R u):=fun x y h=> by simp only [rpair,rise, p x y h]
-- Booking (R membership, Q upper payment)
include s
lemma highways {v:Site n}(p:v∈F)(x:Pane n): rpair f K R v x ∈ books (family f) (floors o F k) v:=
 books_l _ _ v _ _ (still _ _ (R x) {2} (clip f v)) (liftTo o f F (s v p) (R x)) -- syntax
lemma budgeting {v:Site n}(p:v∈F)(x:Pane n): ‖rpair f K R v x‖ ≤ a:=by
 unfold rpair; apply le_trans (norm_mul_le ..); refine le_trans (mul_le_mul ?_ ?_ (norm_nonneg _) (show 0≤(1:ℝ) by positivity)) (le_of_eq (one_mul a))
 · apply le_trans (Flare.cost_pe true (rise R x (Baby f v))); rw [rise, ←baby_fee f v]; exact (act_unit_norm (star (tradew _ _)) _).le
 apply le_trans (Flare.cost_pe false _ |>.trans (Sparkle.Retain.cap (cutM_idp _) _)); exact (act_unit_norm (star (tradew n (R x))) (K v)).trans_le (s v p).cost
omit s
lemma mask_local (T:Support (More n))(g:ℝ) {S:Support (More n)}{F:Evaluation n}(u:LocalOn S F)(hv:inspected T⊆S): LocalOn S (maskT T g F):= by
 intro x y h; unfold maskT; have ht: Healthy g T x↔ Healthy g T y:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty, flags_agree g x y T (agrees_mono h hv)]
 unfold Set.indicator; by_cases k: Healthy g T x; · rw [if_pos (show x∈ _ from k),if_pos (show y∈ _ from ht.1 k)]; exact u _ _ h
 rw [if_neg (show x∉{x|Healthy g T x} from k),if_neg (show y∉ _ from mt ht.2 k)]
lemma mask_env (T:Support (More n))(g:ℝ){F:Evaluation n}(p:Envelope F): Envelope (maskT T g F):= env_indicator _ (RG.healthy_closed .. |>.measurableSet) p
lemma mask_bound (T:Support (More n))(g:ℝ){F:Evaluation n}(hp:0 ≤ a)(p:∀ x, ‖F x‖ ≤ a) (x:Pane n) :‖maskT T g F x‖ ≤ a:= by
 by_cases h:Healthy g T x; · rw [maskT, Set.indicator_of_mem h]; exact p x
 rw [maskT,Set.indicator_of_notMem h,norm_zero]; exact hp
include s e
-- bounding same functional heat. fund inputs (approximations may use generation loops AFTER election H etc)
lemma pilot (V:Support (More n))(g:ℝ)(hx:∀ v∈F,node v∈B k)(hr:Measurable R)(t:LocalOn (inspected V) R) (u:(B k) ⊆ inspected V) (a0:0≤a):
    Envelope (maskT V g (yoke f i K R))∧(∀ x:Pane n,‖maskT V g (yoke f i K R) x‖ ≤ a^i.length) ∧ LocalOn (inspected V) (maskT V g (yoke f i K R)) ∧∀ x, maskT V g (yoke f i K R) x∈ generous (family f) (floors o F k) i:=by
 have H(i:List (Site n))(h:∀ v∈i,v∈F) : Envelope (yoke f i K R) ∧ (∀ x,‖yoke f i K R x‖≤ a^i.length) ∧ LocalOn (inspected V) (yoke f i K R) ∧∀ x, yoke f i K R x∈ generous (family f) (floors o F k) i:=by
    induction i with
    | nil=> rw [show yoke f [] K R=(fun _=>1) from rfl]; refine ⟨Girt.rite_c (1:FC (Single n)),by simp,fun _ _ _=>rfl,fun _=>?_⟩;  exact Submodule.one_le.mp (le_refl (1:Submodule ℂ (FC (Single n))))
    | cons x i ih=>
         let A:=rpair f K R x; let T:=yoke f i K R; have hh:=h x List.mem_cons_self; have hb:= budgeting o f F K s R hh; obtain ⟨u,v,t',w⟩:= ih (fun i v=>h i (List.mem_cons_of_mem _ v)); rw [show yoke f (x::i) K R=(fun k=> A k*T k) from rfl,generous,List.map_cons,List.prod_cons]; refine ⟨env_mult (f:=A) (g:=T) ⟨rpair_meas f K R x hr,a,hb⟩ u,fun i=>?_, fun X Y v=> congrArg₂ (fun a b:FC (Single n)=> a*b) (local_pair f K R x t X Y v) (t' X Y v),fun i=> Submodule.mul_mem_mul (highways o f F K s R hh i) (w i)⟩
         rw [List.length_cons,pow_succ']; exact (norm_mul_le ..).trans (mul_le_mul (hb _) (v _) (norm_nonneg _) a0)
 let G:=H i e; refine ⟨mask_env V g G.1, mask_bound V g (pow_nonneg a0 _) G.2.1, mask_local V g G.2.2.1 (subset_refl _), fun x=>?_⟩; unfold maskT; exact (by by_cases h:x∈ {x:Pane n|Healthy g V x}; rw [Set.indicator_of_mem h]; exact G.2.2.2 x; rw [Set.indicator_of_notMem h]; exact Submodule.zero_mem _) -- tune
lemma radiant_b (V:Support (More n))(g:ℝ)(hx:∀ v∈F,node v∈(B k))(hr:Measurable R)(t:LocalOn (inspected V) R)(u:(B k) ⊆ inspected V): AtSupport false (inspected V) (radiant f i K R V g):=by
 let T:= fun x:Pane n=> (i.map (fun j=>1+rpair f K R j x)).prod; have he: AtSupport false (inspected V) (toMark T):=by
   unfold T; induction i with
   | nil=> exact AtSupport.oneM _
   | cons x i ih=> 
      let Y:=rpair f K R x; have ht:= e x List.mem_cons_self; have hm:AtSupport false (inspected V) (toMark Y):= by
        apply AtSupport.fromEval; exact ⟨rpair_meas f K R x hr, a,budgeting o f F K s R ht⟩; exact local_pair f K R x t; exact fun Vv=> core_price _ _ _ (u (hx x ht)) (fun i v=> u ((flo ..).1 v).1) (highways o f F K s R ht Vv)
      exact AtSupport.mulM (b:=false) (c:=false) (P:=1+toMark Y) ((AtSupport.oneM _).addM hm) (ih (fun i v=> e i (List.mem_cons_of_mem _ v)))
 unfold radiant; apply AtSupport.fromEval; · let M0: Pane n→Fields n:= fun x=>(x,1); exact mask_env _ _ (show Envelope T from Girt.snap (F:=toMark T) (X:=M0) he.env (measurable_id.prodMk measurable_const))
 · apply mask_local _ _ _ le_rfl; exact fun x y v=> he.dep (x,1) (y,1) v (fun _ _ _=>rfl)
 intro x; unfold maskT; by_cases p:Healthy g V x; · rw [Set.indicator_of_mem p]; exact he.allV (x,1)
 rw [Set.indicator_of_notMem p]; exact Reed.Fine.empty _
end Play
end YM.CF.Signal
