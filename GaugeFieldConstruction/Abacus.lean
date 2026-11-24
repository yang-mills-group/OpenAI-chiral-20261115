import GaugeFieldConstruction.Raster
import GaugeFieldConstruction.Square

/-!
# Certifier for square windows. Triangular proof (eliminate backwards).
-/
set_option autoImplicit false
namespace YM.GaugeFieldConstruction.Vouchers.Abacus
open Cauchy Wick Raster Invoice Credit Complex Window Finset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
abbrev Coin (α : Type*) := ℤ × Bill α

noncomputable def estimate (r : Coin α) : J α →ₗ[ℂ] ℂ := jet (fun i=>money (Bill.cash i r.2))
noncomputable def win (T : List (Coin α)) : Window α (Coin α) where
  hom k a := money (Bill.cash a k.2)
  fare k:=k.1
  modes:= T.toFinset
lemma sees (T : List (Coin α)) (r : Coin α) : (win T).read r=estimate r:=rfl

/-- given tail hooks, entries outside-tail excluded. use query that relates to rows. -/
def touch (t : List α) (p : Coin α) (i : α) : Bool :=
  decide (p.1>0) && !(decide (Bill.cash i p.2=0)) && (p.2.all (fun w=>List.contains (i::t) w.1))
def bells : List α → List (Coin α) → Bool
  | [],[]=>true
  | i::t, r::u=>touch t r i && !(decide (i∈t)) && !(decide (r∈u)) && bells t u
  | _,_=>false

private lemma tries (t : List α) (r : Coin α) (i : α) (p : touch t r i=true) :
    r.1>0 ∧ (win [r]).hom r i ≠ 0 ∧ ∀ j ∉ i::t, (win [r]).hom r j=0 := by
  simp only [touch,Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq,decide_eq_false_iff_not] at p
  refine ⟨p.1.1, (nonzero _).mpr p.1.2, fun j h=>?_⟩
  change money _=0; have hk := p.2
  suffices H : Bill.cash j r.2=0 by rw [H]; simp
  have e : ∀ v : Bill α, (∀ x : α×Credit, x∈v→ x.1∈i::t) → Bill.cash j v=0 := by
    intro v; induction v with
    | nil=> simp [Bill.cash]
    | cons w v ih=>
      intro he; have hy : j ≠ w.1:=by intro ht; rw [ht] at h; exact h (he _ (by simp))
      rw [Bill.cash, if_neg hy]; exact ih (fun i hi=> he i (by simp [hi]))
  apply e _ _; exact hk
lemma valid (l : List α) (s : List (Coin α)) (u : bells l s=true) : Valid l.toFinset (win s) ∧ l.Nodup ∧ s.Nodup := by
  induction l generalizing s with
  | nil=>
    cases s with
    | nil=>
      refine ⟨⟨?_,?_⟩,List.nodup_nil,List.nodup_nil⟩
      · simp [win]
      intro x h _; simpa [Area,Finsupp.supported_empty] using h
    | cons a s=> contradiction
  | cons i v ih=>
    cases s with
    | nil=> contradiction
    | cons r w=>
    simp only [bells,Bool.and_eq_true,Bool.not_eq_eq_eq_not,Bool.not_true,decide_eq_false_iff_not] at u
    obtain ⟨p,g,c⟩:=ih w u.2
    obtain ⟨q,h,H⟩:=tries v r i u.1.1.1
    let M:=win (r::w)
    -- separating: use tail rows. need all r' in w zero at i
    have hh : ∀ z : List α,∀ k : List (Coin α), bells z k=true → ∀ j∉z,∀ c∈k,Bill.cash j c.2=0 := by
      intro z; induction z with
      | nil=> intro k he; cases k <;> simp_all [bells] -- fix
      | cons a b ih'=>
        intro w hv; cases w with
        | nil=> contradiction
        | cons x y=>
        intro j hj i hi; have u:touch b x a=true ∧ bells b y=true := by
          simp only [bells, Bool.and_eq_true] at hv; exact ⟨hv.1.1.1,hv.2⟩
        cases List.mem_cons.mp hi with
        | inl he=> subst i; exact Decidable.byContradiction (fun h=>nonzero _ |>.mpr h <| (tries b x a u.1).2.2 j hj)
        | inr hy=> exact ih' y u.2 j (fun h=>hj (by simp [h])) i hy
    refine ⟨⟨?_,?_⟩,List.nodup_cons.mpr ⟨u.1.1.2,g⟩,List.nodup_cons.mpr ⟨u.1.2,c⟩⟩
    · intro k hk; change k∈List.toFinset (r::w) at hk
      rcases List.mem_cons.mp (List.mem_toFinset.mp hk) with L|L
      · subst k; change 0<(↑r.1:ℝ); exact_mod_cast q
      exact p.funds k (List.mem_toFinset.mpr L)
    intro a hv he
    let x:=∑ j∈ v.toFinset,a j • ket j
    have Hx : a=a i • ket i+x := by
      have ht: i ∉ v.toFinset:=by simpa using u.1.1.2
      have h:= decomp hv; simp only [List.toFinset_cons] at h; rw [sum_insert ht] at h; exact h.symm
    have ka : x∈ Area v.toFinset:= Submodule.sum_mem _ (fun i hi=>Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℂ 1 hi))
    have kx : x=0 := p.poses x ka (by
      intro k hk
      have ht: k∈w:=List.mem_toFinset.mp hk
      have hj:= he k (List.mem_toFinset.mpr (List.mem_cons_of_mem r ht)); rw [Hx,map_add,map_smul,Window.read,on_ket] at hj
      have hv : M.hom k i=0 := by change money _=0; rw [hh v w u.2 i u.1.1.2 k ht]; simp
      change a i • M.hom k i + jet (M.hom k) x = 0 at hj; rw [hv,smul_zero,zero_add] at hj
      exact hj)
    rw [kx,add_zero] at Hx
    have k:= he r (List.mem_toFinset.mpr (by simp))
    rw [Hx,map_smul,Window.read,on_ket] at k
    have ha: a i=0:= (mul_eq_zero.mp k).resolve_right h; rwa [ha,zero_smul] at Hx

def totv (L : List (Coin α)) (i j) := Credit.sum <| L.map fun c=> zn c.1 * silver (Bill.cash i c.2)* Bill.cash j c.2
def line (S : List α) (V : α→α→Credit) (T : List (Coin α)) (k : ℤ) (i : α) :=
  S.all fun j=> decide (totv T i j= zn k * V i j)
lemma earning (i j : α) (T : List (Coin α)) (p : T.Nodup) : money (totv T i j)=(win T).glance i j := by
  rw [totv,sum_money,List.map_map]
  unfold Window.glance win; dsimp only
  rw [List.sum_toFinset _ p]; congr 2; ext r; simp only [Function.comp_apply,Credit.times,zn_pay,Credit.cc, ofReal_intCast] -- adjust

noncomputable def vault (T : List (Coin α)) (k : ℤ) := (win T).gain (YM.Maxwell.normal/k) -- import

lemma sums (S : List α) (V : α→α→Credit) (T : List (Coin α)) (k : ℤ) (p : 0<k) (u : bells S T=true)
    (g : ∀ i∈S,line S V T k i=true) : Valid S.toFinset (vault T k) ∧
    ∀ i∈S.toFinset,∀ j∈S.toFinset,(YM.Maxwell.normal:ℂ)*money (V i j)=(vault T k).glance i j := by
  obtain ⟨h,b,c⟩:= valid S T u
  refine ⟨Window.earning h (div_pos YM.Maxwell.normal_pos (by exact_mod_cast p)), fun i hi j hj=>?_⟩
  have he : totv T i j= zn k*V i j := of_decide_eq_true (List.all_eq_true.mp (g i (List.mem_toFinset.mp hi)) j (List.mem_toFinset.mp hj))
  have hy : (k:ℂ)≠0:= Int.cast_ne_zero.mpr (Int.ne_of_gt p) -- maybe Int
  rw [vault,sum_g,← earning i j T c,he,Credit.times,zn_pay]; push_cast; field_simp
end YM.GaugeFieldConstruction.Vouchers.Abacus
