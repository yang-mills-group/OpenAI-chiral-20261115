/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Taxi.Mile
/-! Scope extension from SlotPay.(Project). Using entire *position* law (not small-field on other walk endpoints; loses the threshold gain). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Wages
open Work.G07 Lattice RG Wilson
open scoped ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side}
namespace Path
private lemma one_pick (x : Site n) (a : Step) : separation x (x+a.vec) ≤ 1 := by
  rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split
  · rw [pdist_neg]; exact pdist_step _
  exact pdist_step _

private theorem sieve_Q (x : Site n) (l : Walk) :
    price (tissue (G:=G) x l)=1 ∧ (uses (tissue (G:=G) x l)).length=l.length ∧
      ∀ i∈uses (tissue (G:=G) x l),separation x i.1 ≤ l.length := by
  induction l generalizing x with
  | nil => simp [tissue,price,uses]
  | cons a l ih =>
    obtain ⟨h,h',he⟩:=ih (x+a.vec)
    have hx : (single (G:=G) x a).size=1 ∧ (single (G:=G) x a).links = [a.used x] := by
      unfold single; split <;> exact ⟨rfl,rfl⟩
    have ha:= one_pick x a
    rw [tissue,price,h,hx.1, one_mul,uses,hx.2]
    simp only [List.singleton_append,List.length_cons,h']
    refine ⟨trivial,trivial,fun i hi => ?_⟩; rcases List.mem_cons.mp hi with rfl|hg
    · cases a with
      | mk i b =>
        cases b
        · rw [show (Step.used _ _).1=x from rfl]; simp
        apply le_trans (b:=1) _ (Nat.le_add_left ..)
        simpa [Step.vec,Step.used,sub_eq_add_neg] using ha
    exact le_trans (separation_triangle x (x+a.vec) i.1) (by have := he i hg; omega)
end Path
private lemma detour_phi (s : Slot) : (detour s).length ≤ 2*s.length := by
  simp only [detour,Slot.length,square,Lattice.reverse,List.length_append,List.length_reverse,List.length_map,List.length_cons,List.length_nil]; omega

theorem pane_R (x : Slot) (l : ℕ) (hl : x.length ≤ l)
    (o : Site n) (b : BudgetPoint) :
    LeftBound b.order (b.dirBound o) (fun _=>True) 1
       (2* slotCost G b.power b.order l) (fun U : Config G n => x.atSite U o) := by
  let f:=fun U : Config G n => x.atSite U o
  let w := Path.tissue (G:=G) o (detour x)
  have hF : f=fun U => projector G (Path.eval w U):=funext (hangs x o)
  have hE : LeftSmooth b.order f := hF.symm ▸ (Path.soft w _).postcomp _
  have hp := b.threshold_pos.le
  let C := slotCost G b.power b.order l; have hh : 1≤C := slot_ge ..
  refine ⟨hE,mul_nonneg (by norm_num) (zero_le_one.trans hh),fun a ha hD U hU => ?_⟩
  simp only [one_pow,mul_one]
  by_cases ht : a=[]
  · subst a; exact (Slot.eval_norm x _).trans (le_mul_of_one_le_right (by norm_num) hh)
  apply le_trans ?_ (show C*b.threshold ≤ 2*C from ((mul_le_of_le_one_right (zero_le_one.trans hh) b.threshold_le).trans (le_mul_of_one_le_left (zero_le_one.trans hh) (by norm_num))))
  change ‖leftDerivs f a U‖ ≤ C*b.threshold
  have ha' : leftDerivs (fun U => projector G (Path.eval w U)) a U=projector G (leftDerivs (Path.eval w) a U) :=
    congr_fun (left_linear (Path.soft w b.order) _ ha) U
  rw [hF,ha']
  apply le_trans (norm_projector G _)
  obtain ⟨h1,h2,h3⟩:=Path.sieve_Q (G:=G) o (detour x)
  let T := G.colorScale*b.threshold*(1+(2:ℝ)*l)^b.power
  let N := margin G b.power l; have hn : 1≤N := margin_ge ..
  have hg:=G.colorScale_pos
  have he : 0 ≤ T := by unfold T; positivity
  have hd := (detour_phi x).trans (Nat.mul_le_mul_left _ hl)
  have hc : T * (Path.uses w).length ≤ N*b.threshold := by
    have hw : ((Path.uses w).length : ℝ) ≤ 2*l := by
      unfold w; rw [h2]; exact_mod_cast hd
    calc
      T * (Path.uses w).length ≤ T*(2*l) := mul_le_mul_of_nonneg_left hw he
      _ ≤ (G.colorScale+1)*b.threshold*(2*((l:ℝ)+1))^b.power * (2*((l:ℝ)+1)) := by unfold T; gcongr <;> linarith
      _ = _ := by unfold N margin; rw [pow_succ,mul_pow]; ring
  have hT (i) (hi : i ∈ Path.uses w) (j : Directions G n) (hj : j∈a) : ‖G.colorMat (j i)‖ ≤ T := by
    have hx := (h3 _ hi).trans hd
    have he := hD _ hj i
    rw [G.colorMat_norm]; refine (mul_le_mul_of_nonneg_left he hg.le).trans ?_
    unfold T; rw [mul_assoc]; gcongr
    rw [separation_comm]; exact_mod_cast hx
  have hB := Path.bill w T he U a hT
  change _ ≤ C*b.threshold
  have hd : b.threshold^a.length ≤ b.threshold := by
    have hk : 1 ≤ a.length := List.length_pos_iff.mpr ht
    simpa only [pow_one] using pow_le_pow_of_le_one hp b.threshold_le hk
  calc
    _ ≤ G.colorScale⁻¹*((Path.price w*‖(1:G.Mat)‖)*(T*(Path.uses w).length)^a.length) := mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr G.colorScale_pos.le)
    _ ≤ G.colorScale⁻¹*((1*‖(1:G.Mat)‖)*(N*b.threshold)^a.length) := by
      have hx : Path.price w=1:= h1; rw [hx]; gcongr
    _ ≤ G.colorScale⁻¹*((1*‖(1:G.Mat)‖)*(N^b.order*b.threshold)) := by rw [mul_pow]; gcongr
    _ ≤ _ := by
      let L := b.order; change _ ≤ (1+G.colorScale⁻¹*‖(1:G.Mat)‖)*N^L*b.threshold
      have hN : 0 ≤ N^L*b.threshold:=mul_nonneg (pow_nonneg (zero_le_one.trans hn) L) hp
      unfold L at *; linarith
end YM.Next.Scheduling.Wages
