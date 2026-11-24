import YM.SU5.FiniteGaugeData.Signal.Boon
import YM.SU5.FiniteGaugeData.Reliance.Expenditure
/-! # Compare total and prices of nonconstant legs -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
namespace Boon
variable {n m:Side}{z p a:ℝ} (v:Cover)(d:ℕ) (g:ℝ)

variable {α β:Type*}[Semiring β] (s:Finset α)
lemma all_lists (T:List α)(f:α→β): (T.map (fun i=>1+f i)).prod= (T.sublists'.map (fun l=> (l.map f).prod)).sum:=by
 induction T with
 | nil=> simp
 | cons j t ih=>
    have he (l:List (List α)): f j*(l.map (fun x=>(x.map f).prod)).sum=(l.map (fun x=>(List.map f (j::x)).prod)).sum:= by induction l with
      | nil=>simp
      | cons a v ih=> simp [mul_add,ih]
    rw [List.sublists'_cons,List.map_append,List.sum_append,List.map_map]; simp only [List.map_cons,List.prod_cons,add_mul,one_mul,ih]; exact congrArg (_ + ·) (he _)
lemma radiant_sum (T:List Cover)(f:SU.Slot)(W:Site n → Ket (Single n))(G:Pane n→ Plum.Troupe n)(Ω:Support (More n))(p:T.Nodup) : radiant f (T.map (wrap n)) W G Ω g = ∑ i∈T.sublists'.toFinset, flames f (i.map (wrap n)) W G Ω g:=by
 funext x; rw [Finset.sum_apply]; unfold radiant flames maskT toMark yoke; by_cases h:Healthy g Ω x.1; · simp only [Set.indicator,h,Set.mem_setOf,if_true,List.map_map]; change (T.map _).prod=_; rw [List.sum_toFinset _ (List.nodup_sublists'.2 p)]; exact all_lists T (fun i=>rpair f W G (wrap n i) x.1)
 simp [Set.indicator,h]
variable {K:Calibration}{e:K.c m=n}{L:Loom n}{X:Mark n→ℂ}(M:fares K m e L X)
private lemma shine_sum (f:α→Mark n)(p:∀ i∈s,Envelope (f i)): Envelope (∑ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty]; exact (AtSupport.zeroM (b:=false) (S:=(∅:Support _))).env
 | @insert j s h ih=> rw [sum_insert h]; exact Girt.kitE _ _ (·+·) (by fun_prop) (p _ (mem_insert_self ..)) (ih (fun i v=> p i (mem_insert_of_mem v)))
include M
lemma shines (f:α → Mark n)(p:∀ i∈s,Envelope (f i)) : X (∑ i∈s,f i) = ∑ i ∈ s,X (f i):=by
 induction s using Finset.induction_on with
 | empty=> simp [nullX M]
 | @insert j s h ih=>
   have ht (i:α)(v:i∈s):= p i (mem_insert_of_mem v); rw [sum_insert h,sum_insert h, addition M _ _ (p _ (mem_insert_self ..)) (shine_sum s f ht),ih ht]
local notation "E0·" i=> (1/2:ℝ)/ (2^List.length i:ℝ)
def atomPay (l:List Cover):=E0· l
omit M in
lemma atom_pos(l):0<atomPay l:=by unfold atomPay; positivity
lemma illuminated (T:List Cover)(f: SU.Slot)(W:Site n→ Ket (Single n))(G:Pane n→ Plum.Troupe n)(Ω:Support (More n))(p:T.Nodup)
    (w:∀ i:List Cover,i.Sublist T→ Envelope (flames f (i.map (wrap n)) W G Ω g))
    (v:‖X (radiant f (T.map (wrap n)) W G Ω g)‖ ≤ 1/8)(u:‖1-X (paneOff g Ω)‖ ≤ 1/8):
        ∃ i:List Cover, i.Sublist T ∧ i≠[]∧ atomPay T < ‖X (flames f (i.map (wrap n)) W G Ω g)‖:=by
 let F(i:List Cover):= flames f (i.map (wrap n)) W G Ω g; let S:= T.sublists'.toFinset; have hh:[]∈ S:= List.mem_toFinset.mpr (List.mem_sublists'.mpr (List.nil_sublist _)); have hp(i: List Cover)(t:i∈S): i.Sublist T:= List.mem_sublists'.mp (List.mem_toFinset.mp t)
 let P:= S.erase []; let Z : List Cover→ℂ:=fun i=> X (F i); let y:=Z []
 rw [radiant_sum _ T f W G Ω p, shines _ M _ (fun i t=>w i (hp i t)), ←Finset.add_sum_erase _ _ hh] at v -- tune
 by_contra! t; let A:=∑ i ∈ P, Z i; let K':= atomPay T
 have hi: ‖A‖ ≤ 1/2:=calc
   _ ≤ ∑ i ∈ P, ‖Z i‖ :=norm_sum_le ..
   _ ≤ ∑ i ∈ S, K':= (sum_le_sum (g:=fun i=> K') (fun i p=> t _ (hp i (mem_of_mem_erase p)) (ne_of_mem_erase p))).trans (sum_le_sum_of_subset_of_nonneg (erase_subset ..) (fun _ _ _=> (atom_pos T).le))
   _ = 1/2:= by rw [sum_const, (show S.card= 2^T.length from (List.toFinset_card_of_nodup (List.nodup_sublists'.2 p)).trans (List.length_sublists' _))]; unfold K' atomPay; simp; field_simp
 change ‖y+A‖ ≤ _ at v; change ‖(1:ℂ)-y‖≤ _ at u
 have hb: ‖y‖ ≤ ‖y+A‖+‖A‖:=by nth_rw 1 [←add_sub_cancel_right y A]; exact norm_sub_le ..
 have ht:= norm_sub_norm_le (1:ℂ) y; rw [norm_one] at ht; linarith
end Boon
end YM.CF.Signal
#print axioms YM.CF.Signal.Boon.illuminated
