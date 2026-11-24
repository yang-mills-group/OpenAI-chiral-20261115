import Organdy.Porch
import Zephyr.Chern.Lint
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern


variable {N:Side} {a b B d w:ℝ}
local notation "Ω"=> Single N

variable {A:StemA N} {o:Seat N}

/-- Kernel band estimate in an affinely growing probe. Use *any* anchor in every
positively charged band; as in band_buds for anchored entry. -/
lemma bandPaid {S:Sa N}{C:Toll Ω}{F:SOp N}(p:Piece d S C F)
    (v:o∉ S → C=0) (u:Oily a d B w) (t:Temper o A B)
    (i j:Ω)(k:Fin 3):
    ‖wad F A i j k‖ ≤ w*rent a S * C i j := by
 by_cases e:C i j=0
 · simp [wad,(kernel_free p e u.s.ready A).bud_eq,e]
 have r:o∈S:=by
   by_contra h; rw [v h] at e; exact e rfl
 have a1:1≤B*(1+(S.card:ℝ)):=one_le_mul_of_one_le_of_one_le t.above (by simp)
 have h:∀ x∈leaks S, |A x|≤B*(1+(S.card:ℝ)):=by
   intro x g
   have z:= ((p.expo ..).triggered e).1.lim _ (mem_filter.mp g).2.left _ r
   exact (t.grow x).trans (mul_le_mul_of_nonneg_left
     (add_le_add_right (by exact_mod_cast z.le) _) (zero_le_one.trans t.above))
 refine ((kernel_jet p u.s a1 h).2 k).trans ?_
 refine mul_le_mul_of_nonneg_right ((u.q S.card).trans ?_) (p.nonn ..)
 exact mul_le_mul_of_nonneg_left (Branch.rent_up (show a/2≤a from half_le_self u.hb.le) _) u.bound.le

abbrev dropArc (A:StemA N)(X:SOp N)(t:ℝ) :=
    Matrix.trace (X (profile (petals A t)))
lemma bandDrop {S:Sa N}{C:Toll Ω}{F:SOp N}(p:Piece d S C F)
 (v:o∉ S→ C=0) (u:Oily a d B w)(t:Temper o A B):
   Bud (dropArc A F) ∧ ∀ k, ‖bud (dropArc A F) k‖ ≤ w*(rent a S*ledgerV C):=by
 have q : Bloom (dropArc A F) (∑ i:Ω,wad F A i i):=Bloom.sum _ (fun i _=>(kernel_bud p u.s.ready).bloom)
 refine ⟨q.1,fun k=>?_⟩
 simp only [q.bud_eq,Finset.sum_apply,ledgerV,mul_sum]
 refine (norm_sum_le ..).trans (sum_le_sum ?_)
 intro i _; refine (bandPaid p v u t i i k).trans ?_
 rw [mul_assoc]
 exact single_le_sum (f:=fun j=> w*(Branch.rent a S * C i j)) (fun j _ => mul_nonneg u.bound.le (mul_nonneg (rent_pos ..).le (p.nonn _ j))) (mem_univ i)

/-- The *whole trace*, no factor depending on period. -/
lemma dropSoak {X:SOp N} (h:Soak o X a b d)
 (u:Oily a d B w)(t:Temper o A B):
    Bud (dropArc A X) ∧ ∀ k, ‖bud (dropArc A X) k‖≤w*b:=by
 obtain ⟨F,C,h,l,g,r⟩:=h
 let G:Sa N → SOp N:=fun S y=>if v:y∈Openc _ d then F S ⟨y,v⟩ else 0
 have z (S:Sa N) : F S=fun j=> G S j.val:=funext fun j=>by simp [G,j.property]
 have y (S:Sa N):= bandDrop (F:=G S) (show Piece d S _ _ from (by have v:=h S; rw [z] at v; exact v)) (l S) u t
 have q:Bloom (dropArc A X) (∑ S,bud (dropArc A (G S))):=by
    apply (Bloom.sum univ (fun i _=> (y i).1.bloom)).congr
    filter_upwards [petals_open u.s.ready A] with x gx
    simp_rw [dropArc,r ⟨_,gx⟩,Matrix.trace_sum]
    exact sum_congr rfl fun i _=>congrArg Matrix.trace (congrFun (z i) ⟨_,gx⟩)
 refine ⟨q.1,fun k=>?_⟩
 simp only [q.bud_eq,Finset.sum_apply]
 refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=>(y i).2 k)).trans ?_)
 rw [←mul_sum]
 exact mul_le_mul_of_nonneg_left g u.bound.le

variable {X:SOp N} {p:BudgetPoint} {K:Scree.Loom N}
abbrev chime (K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N)(V:Pane N):=
   Matrix.trace (shine K p o X V)
lemma chimeZ (K:Scree.Loom N)(p:BudgetPoint)(x:Site N)(X:SOp N)(U:Fields N):
 Zc K p x X U= chime K p (node x) X U.1 • 1:=rfl
lemma chimes {A:StemA N} (h:Trunk o X (p.B/10) a b d)
 (f:WindowDress K p d)(ha:0≤a):
 (chime K p o X ∘ petals A) =ᶠ[𝓝 0] dropArc A X:=by
 have z:petals A 0 ∈ safeZone p o:=by
   rw [petal_idle]
   intro i _
   simpa [faceValue,travel,square] using p.threshold_pos
 have r: ∀ᶠ t in 𝓝 0,petals A t ∈safeZone p o:=
   (cont_petal A).continuousAt.eventually (ping_o.mem_nhds z)
 filter_upwards [petals_safe A f.pos,r] with v t u
 rw [comp_apply,chime,litView f (trunks_canal h ha) u (fun _ _ _=>rfl) t]

structure Lode (A:StemA N)(full:SOp N)(g:Pane N→ℂ)
 (Y:SOp N)(cap cut:ℝ):Prop where
 paid: Bud (g ∘ petals A)
 tail: Bud (dropArc A Y)
 sheer: Bloom (dropArc A full) (bud (g ∘ petals A) + bud (dropArc A Y))
 wage(n:Fin 3): ‖bud (g ∘ petals A) n‖≤cap
 leftover(n:Fin 3): ‖bud (dropArc A Y) n‖≤cut

lemma toned {P Y:SOp N} {c:ℝ} (h:Trunk o X (p.B/10) a b d)
 (v:Soak o Y a c d)
 (q:∀ z:Openc (More N) d,P z.val=X z.val+Y z.val)
 (f:WindowDress K p d)
 (u:Oily a d B w)(t:Temper o A B):
 Lode A P (chime K p o X) Y (w*b) (w*c):=by
 have e:= chimes (A:=A) h f u.hb.le
 obtain ⟨B,G⟩:= dropSoak h.pay u t
 obtain ⟨R,M⟩:= dropSoak v u t
 refine ⟨(B.bloom.congr e).1,R,?_,by rw [bud_congr e]; exact G,M⟩
 rw [bud_congr e]
 apply (B.bloom.add R.bloom).congr
 filter_upwards [petals_open f.pos A] with v hv
 rw [dropArc,q ⟨_,hv⟩, Matrix.trace_add]
