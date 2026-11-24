import YM.SU5.Selected.Cor.Diamond
import YM.SU5.FiniteGaugeData.Tower.Reflect
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Stencil( pulseNode pval )
open Rubric
open Afterglow Afterglow.Tapestry
attribute [local instance] opCStarAlgebra
namespace Mezz
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
open Caste Payroll
variable {N:Side} {T:Type}[Fintype T][DecidableEq T]
variable (A:Mezz)(P:Society T)(b:Bool)(i:A.Lot)(X Z:Coast→ Wq A.marks)(C:ℝ) (V:Pane N)
local notation "l"=> park N (A.yard i.1 b)
local notation "F₀" b:max j:max=> A.pole (N:=N) P i b j X Z C
local notation "S" i:max b:max=> A.yard i b
local notation "p"=> P.qu.kin
local notation "D"=> A.Zumba
-- all late and early. output structural distances. Capsule not relying graph support outside.
def coast_b (b:Bool):= Finset.biUnion (Finset.univ:Finset A.BlockDay) fun i=> A.yard i b
local notation "Λ" a:max=> A.coast_b a
local notation "Γ" V:max T:max=> Rubric.Marble V p D (Λ true) (Λ false) T
lemma shore_enroll (a:A.BlockDay) : S a b⊆ Λ b:= fun x v=> mem_biUnion.mpr ⟨a,mem_univ _,v⟩
lemma shore_rest (e:A.Legate): Λ b ⊆ A.Core:= fun x v=>by obtain ⟨a,_,g⟩:= mem_biUnion.mp v; exact (A.yard_core a b e) g
lemma shore_separated (h:A.Legate): Disjoint (Λ true) (Λ false):=by apply disjoint_left.mpr; intro x l' v; obtain ⟨i,_,x0⟩:= mem_biUnion.mp l'; obtain ⟨j,_,t⟩:= mem_biUnion.mp v; exact disjoint_left.mp (A.yards_separate h (show (i,true)≠(j,false) from fun e=> Bool.noConfusion (Prod.mk.inj e).2)) x0 t
lemma shore_active : D⊆ Λ true:= fun x v=> by obtain ⟨i,w,v⟩:=mem_biUnion.mp v; exact A.shore_enroll true i (mem_filter.mp v).1
-- extra: separation lower global × time **both directions**. planned.
lemma view_sea (x y:Cover) (h:A.Legate)(v:x∈ Λ true)(g:y∈ Λ false): A.ℓ.val*100 ≤ (x 3-y 3).natAbs:= by
 obtain ⟨i,_,t⟩:= mem_biUnion.mp v; obtain ⟨j,_,w⟩:=mem_biUnion.mp g; have h':=(A.yard_test ..).1 t; have hf:=(A.yard_test ..).1 w; rcases lt_trichotomy i j with v|q|v; have hp:=A.yards_progress h v true false; omega; subst i; have hK:= A.horizon j h; omega; have hz:=A.yards_progress h v false true; omega
-- stamp support membership exact after dress. 
variable (t:Bool)
private lemma narrowZ : Contained (labelQ N (P.qu.kin)) (A.Front P X Z i b t):=by
 cases b
 · rw [frontZ]; let S':= labelQ N (P.qu.kin); let U:= A.cork P N i t (A.dart P N Z); have hp:Contained S' U:= (A.dart_label P N Z).times _; change Contained S' (cutM (Tset N)*U); apply (containedP ..).mpr; intro i' k a; rw [cutM, Matrix.diagonal_mul,(containedP ..).1 hp _ k a,mul_zero]
 rw [frontX]; exact (A.dart_label P N X).times _
lemma clan_spin (k:Axis)(t':k≠2)(u:k≠3): gleams (A.clan i.1 true b) k:=by
 have hp(x:Cover): (plane k 0).motion ((plane k 0).motion x)= x:= motion_inv k x; have ht(x): x∈ D ↔ (plane k 0).motion x∈ D:= ⟨fun e=> A.Zumba_spin k t' u ▸ mem_image_of_mem _ e,fun e=> hp x ▸ (A.Zumba_spin k t' u ▸ mem_image_of_mem _ e)⟩
 apply GleamHome; intro x l'; have he:gleams (A.yard i.1 true) k:= A.yard_spin i.1 true k u; cases b; · exact mem_sdiff.mpr ⟨he ▸ mem_image_of_mem _ (mem_sdiff.mp l').1, fun z=> (mem_sdiff.mp l').2 ((ht x).2 z)⟩
 exact mem_inter.mpr ⟨he ▸ mem_image_of_mem _ (mem_inter.mp l').1,(ht x).1 (mem_inter.mp l').2⟩
variable {M:Tulip.Male}{ε:ℝ}{w:ℕ}(c:A.Caste (N:=N) M C ε w X Z)
include c
lemma pole_hold_cl : Contained (modesIn N (park N (A.clan i.1 true t))) ((F₀ true t) V):=by
 unfold pole; apply spangle_hold; · rw [frontX]; exact c.rooted_x A P i t
 · exact A.clan_spin _ _ _ (by decide) (by decide)
 exact A.clan_spin _ _ _ (by decide) (by decide)
lemma pole_hold_hp : Contained (labelQ N (p)) ((F₀ b t) V):= A.spangle_label _ _ _ _ _ (narrowZ A P b i X Z t) _ -- args tune. C unused required? 
-- exact Ribbon construction room on $K.c m$ and lifts χ. count orientation.
abbrev lv_one (b:Bool):ℕ:= if b then 10 else 0
abbrev priorityR(b:Bool):ℕ:= if b then 1 else 0
omit c
variable (K:Calibration)(m:Side) (d:A.Caste (N:=K.c m) M C ε w X Z)
local notation "P'"=> K.c m
local notation "Q" T:max => Rubric.Reach K p D (Λ true) (Λ false) T m
include d
lemma light_charge (U:Pane (K.c m)) : A.spanOne P b i X Z C U ∈ (Q (A.yard i.1 b)) (lv_one b) (lv_one (!b)) (priorityR b):=by
 have e(F Z:WRect (Single (K.c m)) P.Club)(P₁:Bool)(r s n:ℕ)(v:∀ t:P.Club, creed P₁ (col F t)∈ (Q (A.yard i.1 P₁)) r s n)(u:∀ t:P.Club, creed P₁ (col Z t)∈ (Q (A.yard i.1 P₁)) r s 0): countOne F Z P₁ ∈ (Q (A.yard i.1 P₁)) (10*r) (10*s) n:=by
    have ht:= Reach.rake_reserves _ _ v u Finset.univ.toList 1; rw [rung_len P.club_card, one_mul] at ht; exact ht
 let a:= A.yard i.1; let g(b t'): WRect (Single (P')) P.Club := A.pole P i b t' X Z C U; have ht(b k t): withinM (labelQ (P') (p)) (col (g b k) t):= (containedT ..).1 (pole_hold_hp _ _ _ _ _ _ _ _ k d) _
 cases b
 · have hd:=Disjoint.mono A.shore_active (A.shore_enroll false i.1) (A.shore_separated d.value); have hu(k t): creed false (col (g false k) t) ∈ (Q (a false)) 0 1 0:=
       Reach.create_zone (ht ..) ((col_lim ..).2 (pole_x A P i false k X Z C d U) _) (a false) ((containedT ..).1 (A.talent P i false k X Z C d U) t) (A.shore_enroll false i.1) (subset_refl _) hd; exact e _ _ false 0 1 0 (hu true) (hu false)
 have hu(k t): creed true (col (g true k) t)∈ (Q (a true)) 1 0 (priorityR k):=by
    let L:= A.clan i.1 true k; have hx:=pole_hold_cl A P i X Z C U k d; let F':=g true k; have hf: L ⊆ a true:=by cases k; exact sdiff_subset; exact inter_subset_left
    apply Reach.remove_zone (ht ..) ?_ L ((containedT ..).1 hx t) (hf.trans (A.shore_enroll true i.1)) hf
    · intro u v; cases k; exact if_neg (mem_sdiff.mp v).2; exact if_pos (mem_inter.mp v).2 -- defeq
    change acts _ (col F' t)=_; rw [dim_cut]; exact (col_lim ..).2 (pole_x A P i true k X Z C d U) t
 exact e _ _ true 1 0 1 (hu true) (hu false)
omit d in
private lemma negative_test {X:Finset Cover}{f:Buffered.Family K}(v: InTest K false X false f): InTest K true X false (-f):= by rw [← neg_one_smul ℂ]; exact InTest.smul _ v.widen
-- symbol property of legs from counts on both sides. orientation pointer.
omit d
structure Spry (b:Bool)(i:A.Lot)(F:Buffered.Family K): Prop where
  marb: F∈ Rubric.Marble K P.qu.kin (D) (A.coast_b true) (A.coast_b false) (A.yard i.1 b) (lv_one b) (lv_one (!b)) (priorityR b)
  keeps : Neutral K F
  admire : Tower.mirror K 0 0 (Tower.mirror K 1 0 F)=-F
lemma Spry.test {b:Bool} {F:Buffered.Family K}(h:Spry A P K b i F): InTest K false (A.yard i.1 b) false F:= by
 have he:=Marble.assign h.marb; have ht:cameo (lv_one b) (lv_one (!b))=false:=by cases b <;> decide
 rwa [ht] at he
#print Spry.mk
include d
theorem sprightly (t:Roomy (A.yard i.1 b) (K.c m)) : ∃ F:Buffered.Family K,Spry A P K b i F ∧ F m=A.matinee P b i X Z C:=by
 let S':= A.yard i.1 b
 obtain ⟨G,u,h⟩:= Reach.extensionA (K:=K) t (A.marquee_one P b i X Z C d) (A.matinee_c P b i X Z C d) (A.matinee_1 P b i X Z C d) (fun v:Fields (K.c m)=> A.light_charge P b i X Z C K m d v.1) -- param order `matinee_1 ... d r..`
 have hv:=Marble.assign u; rw [show cameo (lv_one b) (lv_one (!b))=false from (by cases b<;> decide)] at hv; refine ⟨G,⟨u,onceNeutral hv.widen t.seats (by rw [h]; exact matinee_g A P b i X Z C d),?_⟩,h⟩
 have he(a:Axis)(h:a≠3) : Tower.reflectedBox a 0 (A.yard i.1 b)= (A.yard i.1 b):= A.yard_spin i.1 b a h; have ht:=Tower.axial K 0 0 (Tower.axial K 1 0 hv.widen); rw [he 1 (by decide),he 0 (by decide)] at ht
 apply looksLike t.seats ht (negative_test K hv)
 change reflMark 0 0 (reflMark 1 0 (G m))= -(G m); rw [h]; exact matinee_R A P b i X Z C d
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms light_charge
#print axioms shore_separated
#print axioms sprightly
