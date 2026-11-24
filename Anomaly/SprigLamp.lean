import Anomaly.PitchMark
import Zephyr.Chern.Bends
/-!
Pass the projector calculation to the masked local probe. Buds use *real*
motions of the first (physical) Pane. This is still the stencil result;
one must then see this term in the signed-law price -- not claim a vacuum
price merely from a jet at a background.
-/
set_option autoImplicit false
noncomputable section
namespace Zephyr.Chern
open YM Lattice Filter Topology CF CF.Tulip CF.Cube CF.Lat
open CF.Tenant CF.Drapes CF.Branch Metric Finset
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
open CF.Swell CF.Pastry CF.Scree CF.Skye CF.Fock CF.Sault
variable {N:Side}
local notation "T" => Single N

variable {o:Seat N} {V:Oil N} {X:SOp N} {a b d w B:ℝ}

/-- `Soak` is based at an actual rooted footprint, not support-free
row control. That pays the growth of these jets even when summing
trace entries over the entire torus. -/
theorem piece_root_buds (p : Oily a d B w) {A:StemA N} (u: Temper o A B)
    {C : Toll T} {F:Oil N} {S: Seal (Site (More N))} (f:Piece d S C F)
    (t:C≠0→ o∈S) (i j:T)(k:Fin 3) :
    ‖wad F A i j k‖ ≤ w * (rent a S*C i j) := by
  by_cases h : C i j=0
  · simp [wad,(kernel_free f h p.s.ready A).bud_eq,h]
  have l:C≠0:=fun x=>h (by rw [x]; rfl)
  have hl:= (f.expo i j).triggered h
  have hb:1≤ B:=u.above
  have H : 1≤ B*(1+(S.card:ℝ)):= one_le_mul_of_one_le_of_one_le hb (by simp)
  refine ((kernel_jet f p.s H ?_).2 k).trans ?_
  · intro x hx
    have he: separation x.1 o < S.card := hl.1.lim x.1 (mem_filter.mp hx).2.1 o (t l)
    apply le_trans (u.grow x)
    gcongr
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (f.nonn _ _)
  refine (p.q S.card).trans (mul_le_mul_of_nonneg_left ?_ p.bound.le)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (half_le_self p.hb.le) (by positivity)

/-- True trace measurement along the compact-link motion *before* mask,
for using the tail. -/
def traceJet (X:SOp N)(A:StemA N)(t:ℝ) := Matrix.trace (X (profile (petals A t)))

theorem inTrace {A:StemA N} (p: Soak o X a b d) (q:Oily a d B w)(u:Temper o A B) :
    Bud (traceJet X A) ∧ ∀ k, ‖bud (traceJet X A) k‖≤ w*b := by
  classical
  obtain ⟨F,C,H,t,v,g⟩ := p
  let G : Band N→Oil N:= fun S x=> if hx:x∈Openc _ d then F S ⟨x,hx⟩ else 0
  have hu(S) : F S= fun x=> G S x.val:=funext fun x=> by simp [G,x.property]
  have h(S):Piece d S (C S) (G S):= by have hy:= H S; rw [hu S] at hy; exact hy
  have he : Bloom (traceJet X A) (∑ S:Band N,∑ i:T,wad (G S) A i i):=by
    apply (Bloom.sum univ (u:=fun S t=> ∑ i:T,drip (G S) A i i t)
      (fun S _=> Bloom.sum _ (fun i _=> (kernel_bud (h _) q.s.ready).bloom))).congr
    filter_upwards [petals_open q.s.ready A] with x hx
    unfold traceJet; rw [show X (profile (petals A x))= _ from g ⟨_,hx⟩,Matrix.trace_sum]
    exact sum_congr rfl fun S _=> congrArg Matrix.trace (hu S ▸ rfl) -- tune
  rw [he.bud_eq]; refine ⟨he.1,?_⟩
  intro k; simp_rw [Finset.sum_apply]
  refine ((norm_sum_le ..).trans ?_).trans (mul_le_mul_of_nonneg_left v q.bound.le)
  rw [mul_sum]; apply sum_le_sum; intro S _
  refine (norm_sum_le ..).trans ?_
  unfold ledgerV; rw [mul_sum, mul_sum]; exact sum_le_sum (fun i _=> (piece_root_buds q u (h S) (fun n=> Classical.not_not.mp (mt (t S) n)) i i _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (single_le_sum (fun j _=> (h S).nonn i j) (mem_univ _)) (rent_pos _ _).le) q.bound.le))

/-- At *each* fixed height and torus, no assumption of staying in
Guard globally along the affine direction. Only the germ is used.
No smoothness across the mask boundary assumed. -/
theorem lamp_petals (A : StemA N) (b : RG.BudgetPoint) :
    ∀ᶠ t in 𝓝 0,pingS b.threshold univ (petals A t) := by
  have h: (petals A 0) ∈ {V:Pane N|pingS b.threshold univ V}:=by rw [petal_idle]; exact ping_f b univ
  exact ((cont_petal A).tendsto 0).eventually (ping_o.mem_nhds h)

theorem meter_pass (O : Site N)(A : StemA N) {b : RG.BudgetPoint} {K : Loom N} {X : SOp N}
    {r : ℕ} {e d : ℝ} (p : Roof N e d r K)(h:b.threshold≤e) : (fun t=> traceMeter b K O X (petals A t))=ᶠ[𝓝 0] traceJet X A := by
  filter_upwards [lamp_petals A b] with t ht
  let u:= petals A t; let S:=halo b.B {node O}
  unfold traceMeter pinMatrix
  have hz : u ∈ {V : Pane N|pingS b.threshold (halo b.B {node O}) V} := CF.Vow.grow_b (subset_univ _) ht
  rw [Set.indicator_of_mem hz]
  have he: ∀ i,K (u,i)=u:=by
    intro i; funext j; apply p.lamp
    have hv: pingS e univ u:=fun i H => (ht i H).trans_le h
    exact Disjoint.mono_right (subset_univ _) (show Disjoint (RG.flags e u) univ from (show Disjoint (univ: Support _) (RG.flags _ _) from ping_le hv).symm)
  change Matrix.trace (X (profile (K (u,_))))=_; rw [he]; rfl

end Zephyr.Chern
