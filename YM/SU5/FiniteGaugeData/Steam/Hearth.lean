import YM.SU5.FiniteGaugeData.Steam.Away
/-! Uniform density bound with role of face suppression retained.
    Bound field on bad events pricing with tile heat.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window.Steve
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Graph Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
variable {G:Gauge}{n:Side}{h v a k C L w:ℝ}{R:PathData G}{F:RG.Clip}{i:ℕ}
def misses (X: Config G n) (t:ℝ): Finset (Face (Per n)) := univ.filter (fun i=> t < G.chord (faceValue X i))
lemma match_miss (X: Config G n)(s:Signed)(x:Site n) : (misses (pull s x X) t).card = (misses X t).card:=by
 refine card_bij (fun i _=> Face.send s x i) ?_ (fun i _ j _ eq=> Face.injective_send s x eq) ?_ -- wrong
 · intro i p; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.trans_le (Face.send_price X i s x G.chord G.chord_inv (fun k g=>G.chord_conj g k)).le⟩
 intro i p; obtain ⟨j,rfl⟩:= (Finite.surjective_of_injective (Face.injective_send s x)) i; exact ⟨j, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp p).2.trans_le (Face.send_price X j s x G.chord G.chord_inv (fun k g=>G.chord_conj g k)).symm.le⟩, rfl⟩
-- use Or: threshold chooses ≥? strict bad thus reconstruction may want ≤. continuity etc.
lemma penalty_many (W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n)(A:ℕ)(e:0≤ v)(Z:A ≤ (misses V p.threshold).card): kinetic n p C L v (A*F.linear) ≤ R.principal F p v V := by
 let t:=p.threshold; let U:= misses V t; have hp:= F.tail_pos
 have uθ(q:Face (Per n)): 0≤ R.baseTerm F p V q:= R.base_nonneg ..
 have ht: ↑A*F.linear*t^2 ≤ ∑ x,R.baseTerm F p V x:= calc
    _ ≤ U.card • (F.linear*t^2) := by
       simp only [nsmul_eq_mul]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr Z) (by positivity)
    _ = ∑ _ ∈ U, F.linear*t^2:=by simp
    _ ≤ ∑ i∈ U,R.baseTerm F p V i:= sum_le_sum (fun i hi=> (show F.linear*t^2≤ _ from (by
        have hh:= (mem_filter.mp hi).2; unfold baseTerm; apply le_trans _ (le_add_of_nonneg_right ?_); swap; · split<;> positivity
        rw [clipped,if_neg hh.not_ge,sq,←mul_assoc]; exact mul_le_mul_of_nonneg_left hh.le (mul_nonneg hp.le p.threshold_pos.le))))
    _ ≤ _:= sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> uθ i)
 obtain ⟨A,B⟩:=Graph.oath W p V
 unfold kinetic taxY PathData.principal; exact (add_le_add (mul_le_mul_of_nonneg_left (add_le_add ht (neg_le_of_abs_le A)) e) (neg_le_of_abs_le B)).trans' (Eq.le (by ring)) -- t
lemma full_below (W:R.Bounds F a C L)(p:BudgetPoint)(V:Config G n)(i:ℕ)(e:0≤ v)(Z:i ≤ (misses V p.threshold).card): kinetic n p C L v (i*F.linear) ≤ R.inChannels F p v V:=by
 have he (s':Signed):= penalty_many W p (pull s' 0 V) i e (show _ from le_trans Z (match_miss V s' 0).symm.le)
 exact ((mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _=> he i)) (show 0≤ (Fintype.card Signed :ℝ)⁻¹ by positivity))).trans' (by simp)
open MeasureTheory Cascade Vale CF.Paige Vault Nova Emu
variable {m B Ln:Side} {u η vA κ γ s r σ x g d:ℝ}{p:ℕ} {O:Odd Ln.val}{Y:Pricing i Ln O (Thread i)}{P:Grasp Y B u}
-- separate algebra amount, eF = ln area price for unmarked gauge integral
abbrev unlit (V:GramM N)(γ L:ℝ):= taxY (More N) V.beta V.p.threshold γ L+ Fintype.card (Face (Per (More N)))/2
abbrev blow (F:Clip)(γ y:ℝ) := γ*(F.linear*y^2)/2
lemma weight_X (V:GramM N)(W:V.path.Bounds V.funds σ γ L)(e:0 < g)(b:V.beta*g^2=1)(k:g≤V.p.threshold)(x:Pane N)(r:ℕ)(z: r ≤ (misses x V.p.threshold).card): Graph.past V x ≤ Real.exp (unlit V γ L - r * blow V.funds V.beta V.p.threshold)*Real.exp (-basal V g x):=by
 rw [←Real.exp_add]; refine Real.exp_monotone ?_; have he:= per_channel W e b k x
 rw [←full_basal] at he; have hb:= full_below W V.p x r (variance_beta e b).le z; unfold kinetic at hb; unfold blow unlit; linarith only [he,hb]
lemma operator_all (V:GramM (mid m B))(S:Loom (mid m B))(R:Ledger h v η r C V)(H:Roof (mid m B) x u p S)(hu:P.roundZ≤(mid m B).val)(F:1≤h)(u:0≤r)(eA:0≤C)(x:Orbit (mid m B)): ‖Graph.beam V P S x‖ ≤ Real.exp (flagBill (mid m B) v η C) := by
 let A:=Graph.cab V P S x; exact (spentS _ _ A).trans (by rw [(sea_g hu (S x) (H.paid _) V.J.M).2, mul_one]; exact extensive_mile R x u F eA ((P.broadness _ hu _).projection _ (H.paid _)))
end YM.CF.Window.Steve
