import YM.CF.Cubes.Prism

/-! Gauge covariance, continuity of flags. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cube
open Lattice Lat SU Finset
open scoped Matrix.Norms.L2Operator MatrixOrder Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}
section
variable (U : Bkg (Domain m B)) (g : Site (Domain m B) → E)
def onF (s : ArrayF m) : ArrayF m := fun x=>scaledV (g (address m B x.1)) (s x)
lemma parcel_g (x y o) : parcel m B (gauge g U) x y o = g (address m B x)*parcel m B U x y o*(g (address m B y))⁻¹ := by
  unfold parcel; rw [travel_gauge,arrive]
lemma launch_g (z a o v) : launch m B (gauge g U) z a o (scaledV (g (address m B a)) v)=turn (g z) (launch m B U z a o v) := by
  unfold launch scaledV tax; rw [travel_gauge,arrive,turn_seq,turn_seq (g z),turn_inv_g]
lemma freight_g (z a v) : freight m B (gauge g U) z a (scaledV (g (address m B a)) v)=turn (g z) (freight m B U z a v) := by
  unfold freight; rw [turn_mul,turn_sum]; simp_rw [launch_g]
lemma paint_g (s : ArrayF m) (q) : paintV m B (gauge g U) (onF g s) q=turnX g (paintV m B U s q) := by
  funext i; unfold paintV paint turnX; rw [turn_ren,turn_sum]; congr 1; apply sum_congr rfl; intro x _; rw [onF,freight_g,turn_mul]
lemma train_g (s : ArrayF m) (x l) : train m B (gauge g U) (onF g s) x l=(train m B U s x l).map (turn (g (address m B x))) := by
  induction l generalizing x with
  | nil => rfl
  | cons r l ih =>
    rcases r with ⟨w,o⟩; rw [train,train,ih,parcel_g]
    let p := turn (g (address m B w.1))
    let t := turn (parcel m B (gauge g U) x w.1 o)
    let u := turn (parcel m B U x w.1 o); let Z := turn (g (address m B x))
    have he : turn (g (address m B x)*parcel m B U x w.1 o*(g (address m B w.1))⁻¹) ∘ p= Z ∘ u := by
      ext v : 1; change turn _ _= turn _ (turn _ v); unfold p; rw [turn_seq,turn_inv_g,turn_seq]
    change List.map _ (List.map p ( _ :: train m B U s w.1 l))=_
    rw [List.map_map,List.map_map,he]
lemma check_g (e) (s : ArrayF m) (r a) : Check m B e (gauge g U) (onF g s) r a ↔ Check m B e U s r a := by
  unfold Check; simp_rw [train_g]; unfold onF scaledV; dsimp only; simp_rw [strain_turn,turn_norm]
lemma verified_g (e) (s : ArrayF m) (r) : Verified m B e (gauge g U) (onF g s) r ↔ Verified m B e U s r := by
  unfold Verified; simp_rw [check_g]
end

section
-- express evaluation of dependent list with fixed indexing, no topology on arbitrary-length list.
abbrev FlagU (m B : Side) := Bkg (Domain m B)×ArrayF m
lemma flags_cont (m B : Side) (x : Index m) (l : List (Ramp m)) : ∃ L : List (FlagU m B → Vect), (∀ w∈L, Continuous w) ∧
    ∀ t, train m B t.1 t.2 x l = L.map (fun f=>f t) := by
  induction l generalizing x with
  | nil => exact ⟨[],by simp,fun _=>rfl⟩
  | cons r l ih =>
    rcases r with ⟨w,o⟩
    obtain ⟨L,h,H⟩ := ih w.1
    let A : FlagU m B → Vect := fun t=>(t.2 w).val
    have hA : Continuous A := continuous_subtype_val.comp ((continuous_apply w).comp continuous_snd)
    let T : FlagU m B→E := fun t=> parcel m B t.1 x w.1 o
    have hT : Continuous T := (travel_cont (K:=E) (address m B x) (march (address m B x) (address m B w.1) o)).comp continuous_fst -- tune
    refine ⟨(A::L).map (fun f t=>turn (T t) (f t)),?_,?_⟩
    · intro f hf; obtain ⟨j,g,rfl⟩ := List.mem_map.mp hf
      have hg : Continuous j := (List.mem_cons.mp g).elim (fun k=>by rw [k]; exact hA) (fun k=>h j k)
      let q := fun t => (T t,j t)
      change Continuous ((fun x:E×Vect=>turn x.1 x.2) ∘ q)
      exact turn_cont.comp (show Continuous q from hT.prodMk hg)
    intro t; rw [train,H,List.map_map]; simp [T,A]
lemma fee_cont (m B : Side) (a : Spot m) (l : List (Ramp m)) :
    Continuous (fun t:FlagU m B => ‖restrain margin (train m B t.1 t.2 a.1 l) (t.2 a).val‖) := by
  obtain ⟨L,h,H⟩ := flags_cont m B a.1 l
  simp_rw [H]; apply Continuous.norm
  exact strain_cont margin margin_pos L id h _ (continuous_subtype_val.comp ((continuous_apply a).comp continuous_snd))
lemma open_check (m B a r) : IsOpen {t:FlagU m B| Check m B margin t.1 t.2 r a} := by
  unfold Check; simp_rw [Set.setOf_forall]; apply isOpen_biInter_finset; exact fun i _=>isOpen_lt continuous_const (fee_cont m B a i)
lemma open_verified (m B r) : IsOpen {t:FlagU m B| Verified m B margin t.1 t.2 r} := by
  unfold Verified; simp_rw [Set.setOf_forall]; exact isOpen_iInter_of_finite fun a=> isOpen_iInter_of_finite fun _=>open_check ..
end
end YM.CF.Cube
