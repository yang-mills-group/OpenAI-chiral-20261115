import YM.CF.Mir.Funds

/-! Exact sym action for scalar program. Leaves terms allocated by face, with connected weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Trip
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Phase.Part m B} {u v d : ℝ} {W : Scroll m B c}
instance trips_home : Nonempty (Trip m) := ⟨1⟩
abbrev FaceTerm (m B : Side) := Trip m × Stamp m B
abbrev tariffR (m : Side) := (Fintype.card (Trip m) : ℝ)
lemma paid_t (m : Side) : 0 < tariffR m := Nat.cast_pos.mpr Fintype.card_pos
-- t orientation new to old, onPack acts evaluating transformed arrays at new grid
-- assigned old face = adv t A

def driftK (t : FaceTerm m B) : Stamp m B := t.2.image (run B t.1)
def faceT (t : FaceTerm m B) : Index m := t.1.adv (pinpoint m B t.2)
def twistF (m B : Side) (v : Trip m) (f : Pack m B→ℂ) (x : Pack m B) := (tariffR m)⁻¹ • v.flips (f (onPack B v x))
def programK {t : Phase.Part m B} (W : Scroll m B t) (v : FaceTerm m B) := twistF m B v.1 (W.term v.2)
def cabin {t : Phase.Part m B} (W : Scroll m B t) (x : Pack m B) := ∑ v:FaceTerm m B, programK W v x
def seedK {t : Phase.Part m B} (W : Scroll m B t) (v : FaceTerm m B) := twistF m B v.1 (W.leftover v.2)
def coinK {t : Phase.Part m B} (W : Scroll m B t) (u : ℝ) (v : FaceTerm m B) := (tariffR m)⁻¹*dust W u v.2
lemma ct_flips (a : Trip m) : Continuous (flips a) := by unfold flips; split; exact continuous_id.star; exact continuous_id
variable (H : ScaleK u v W) {e : ℝ} (b : Budget B e d)
include H b
lemma programC (k) : ContinuousOn (programK W k) (payer m B e) := by
  let E := k.1
  exact (continuousOn_const (c:=(tariffR m)⁻¹)).smul ((ct_flips E).comp_continuousOn ((gainS H b _).cont.comp (E.convey _).continuousOn (fun x l=>dominated E x l)))
lemma cabin_cont : ContinuousOn (cabin W) (payer m B e) := continuousOn_finsetSum _ fun i _=> programC H b i
lemma program_face (k) {x y} (h:x∈payer m B e) (g:y∈payer m B e) (p : Sample.AgreeF (faces m (faceT k)) x.2 y.2) (q : Agrees (room m B (faceT k)) x.1 y.1) : programK W k x=programK W k y := by
  let t := k.1; let a := pinpoint m B k.2
  apply congrArg (fun u:ℂ=>(tariffR m)⁻¹ • u); apply congrArg (t.flips); refine plates H b k.2 (dominated t x h) (dominated t y g) ?_ ?_
  · intro i hx; apply p (t.adv i); rw [faceT,←location]; exact mem_image_of_mem _ hx
  apply (setN k.1 (room m B a) x.1 y.1); rw [room_run]; exact q
lemma twist_gate {x : Pack m B} (p:x∈payer m B e) (g : Geometry (CSide m B)) (k) : programK W k (Lattice.gauge g x.1,partner m B g x.2)=programK W k x := by
  unfold programK twistF; rw [pore]; apply congrArg (fun u:ℂ=>(tariffR m)⁻¹ • u); apply congrArg (k.1.flips); exact (gainS H b k.2).gaugeEq (onPack B k.1 x) (g ∘ run B k.1) (dominated k.1 x p)
-- term pairing, not only sum identity.
def pivot (t : Trip m) (k : FaceTerm m B) : FaceTerm m B := (t⁻¹*k.1,k.2)
omit H b
lemma drop_off (t : Trip m) (k : FaceTerm m B) (x : Pack m B) : programK W (pivot t k) (onPack B t x)=t.flips (programK W k x) := by
  unfold programK pivot twistF; rw [trip_comp]; simp only [←mul_assoc,mul_inv_cancel,one_mul]; rw [flips_real,← t.flip_inv_eq, flips_comp]; rw [show (t⁻¹*k.1).flips=(k.1*t⁻¹).flips by funext x; unfold flips; simp [Trip.glarex,Bool.xor_comm]]
lemma fieldHit (t : Trip m) (k : FaceTerm m B) : faceT (pivot t k) = t⁻¹.adv (faceT k) := (adv_comp ..).symm
lemma pivot_back (a : Trip m) (k : FaceTerm m B) : pivot a⁻¹ (pivot a k) = k := by simp [pivot]
def pivotM (t : Trip m) : Equiv.Perm (FaceTerm m B) := ⟨pivot t, pivot t⁻¹, pivot_back t, fun k=> by simp [pivot]⟩
lemma shakes (t : Trip m) (x) : cabin W (onPack B t x)=t.flips (cabin W x) := by rw [cabin, ←Equiv.sum_comp (pivotM t) _]; exact (sum_congr rfl fun i (_:i∈Finset.univ)=> drop_off t i x).trans (flip_sum t _ _).symm
include H b
lemma net_sum {x} (g:x∈payer m B e) : Phase.fund m B c x.1 x.2 - cabin W x=∑ k:FaceTerm m B, seedK W k x := by
  rw [sub_eq_iff_eq_add]; unfold cabin; rw [←sum_add_distrib,Fintype.sum_prod_type]
  let m' := tariffR m; have hp := paid_t m
  have hk (t : Trip m) : ∑ k:Stamp m B,(seedK W (t,k) x + programK W (t,k) x)= m'⁻¹ • Phase.fund m B c x.1 x.2 := by
    unfold seedK programK twistF; simp only [←smul_add,←flips_add,Scroll.leftover,sub_add_cancel,←smul_sum]
    rw [←flip_sum,taxed H b.1 (dominated t x g)]; have h := settledAll t b.1 x c g
    change m'⁻¹ • t.flips (Phase.fund m B c (through B t x.1) (oncue t x.2))= _; rw [h, show t.flips (t.flips (Phase.fund m B c x.1 x.2))=Phase.fund m B c x.1 x.2 from by nth_rw 1 [←flip_inv_eq]; apply flips_inv] -- tune
  simp_rw [hk]; rw [sum_const,card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ (paid_t m|>.ne'), one_smul]
omit H b in
lemma spin_grove (s:Stamp m B) (a : Trip m) (h : Branch.Grove (terr _) s) : Branch.Grove (terr _) (s.image (run B a)) := by -- shouldn't include H
  induction h with
  | single x => rw [image_singleton]; exact .single _
  | join _ g h ih => rw [image_insert]; exact .join ih (mem_image_of_mem _ g) (show separation (run B a _) (run B a _)≤1 from (span_act ..).trans_le h)
lemma life (t : FaceTerm m B) : supportsCup m B (driftK t) (seedK W t) (coinK W d t) e := by
  obtain ⟨u,w,h,g,k,y⟩ := leavings H b t.2; let a := t.1
  have he : 0 ≤ (tariffR m)⁻¹ := (inv_pos.mpr (paid_t m)).le
  have hv := a.convey B
  have ht := u.comp hv.continuousOn (fun x g=>dominated a x g)
  refine ⟨(continuousOn_const (c:=(tariffR m)⁻¹)).smul ((ct_flips a).comp_continuousOn ht),fun x e=>?_,mul_nonneg he h,fun b x e=>?_,fun p=>?_,?_⟩
  · unfold seedK twistF; rw [norm_smul,Real.norm_of_nonneg he,flips_norm]; exact mul_le_mul_of_nonneg_left (w _ (dominated a x e)) he
  · unfold seedK twistF; rw [pore]
    apply congrArg (fun u:ℂ=>(tariffR m)⁻¹ • u); apply congrArg (a.flips); exact g (b ∘ run B a) (onPack B a x) (dominated a x e)
  · exact spin_grove _ a (k (right_ne_zero_of_mul (show (tariffR m)⁻¹*dust W d t.2≠0 from p)))
  intro x hx x' hx' p q
  apply congrArg (fun u:ℂ=>(tariffR m)⁻¹ • u); apply congrArg (a.flips)
  apply y _ (dominated a x hx) _ (dominated a x' hx')
  · intro i h; apply p (a.adv i); unfold driftK; rw [←chairs_rot]; exact mem_image_of_mem _ h
  apply setN a (walls m B t.2) x.1 x'.1; rw [wall_rot]; exact q
end YM.CF.Mir
