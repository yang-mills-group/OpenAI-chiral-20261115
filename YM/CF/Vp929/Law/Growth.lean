import YM.CF.Vp929.Law.Spin
import YM.CF.Vp929.Law.Stamina
import Mathlib.Tactic
set_option maxRecDepth 8000
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms March Filter
open scoped Topology Classical
namespace Delta
variable {B n k h:ℕ}(χ:Cover→ℕ){x y:Cover}
abbrev Coloring (r:Cover→ℕ)(B:ℕ) :Prop:=∀ x y,Range B x y→ r x=r y→ x=y
def cull (H:ℕ)(x:Cover): Prop:=∀ y, Range H x y → χ y < χ x → ¬ cull H y
termination_by χ x
def sep(H:ℕ)(L:Set Cover):Prop:=∀ x ∈ L,∀ y∈L, Range H x y → x=y
lemma exits(H:ℕ)(x:Cover):∃ y, Range H x y ∧ cull χ H y:=by
 by_cases t:cull χ H x; exact ⟨x,Range.refl H x,t⟩; rw [cull] at t; push Not at t; obtain ⟨y,v,t,k⟩:=t; exact ⟨y,v,k⟩
lemma firm {Q} (v:Coloring χ Q)(p:h≤Q):sep h {x|cull χ h x}:=by
 intro x a y b p'; change cull .. at a b; rcases lt_trichotomy (χ x) (χ y) with e|e|e; rw [cull] at b; exact (b x p'.symm e a).elim; exact v x y (p'.mono p) e; rw [cull] at a; exact (a y p' e b).elim
abbrev Gear {α:Type*}(r t:Cover→α)(o:Cover)(a:ℕ):Prop:=∀ i:Cover,Range a o i → r i=t i
lemma gear_near{α:Type*}{r t:Cover→α}(v: Gear r t x h)(p:Range n x y)(t₁:n+k ≤ h):Gear r t y k:=fun i e=> v _ ((p.trans e).mono t₁)
lemma flashCull (χ₀: Cover→ℕ)(H:ℕ)(o:Cover)(i:ℕ)(p: χ o < i) (t: Gear χ χ₀ o (i*H)) : cull χ H o↔ cull χ₀ H o:=by
 induction i generalizing o with
 | zero=> omega
 | succ i ih=>
    rw [cull.eq_1 χ H _,cull.eq_1 χ₀ H _]; have he:= t o (Range.refl _ _); rw [←he]; have hx(y)(p:Range H o y):χ y=χ₀ y:= t y (p.mono (by rw [Nat.add_mul]; omega)); constructor
    · intro v y tP q a; rw [←hx y tP] at q; refine v y tP q ((ih _ (by omega) (gear_near t tP ?_)).2 a); rw [Nat.add_mul]; omega
    intro v y W q U; refine v y W ((hx y W) ▸ q) ((ih _ (by omega) (gear_near t W (by rw [Nat.add_mul]; omega))).1 U)
protected lemma sympathy(s:March)(χ₁:Cover→ℕ)(t:χ=χ₁ ∘ s.slide)(H:ℕ)(x:Cover) : cull χ H x ↔ cull χ₁ H (s.slide x):=by
 have h(n:ℕ)(x:Cover)(p:χ x < n) : cull χ H x ↔ cull χ₁ H (s.slide x):=by
   induction n generalizing x with
   | zero=> omega
   | succ n ih=>
      rw [cull.eq_1 χ H _,cull.eq_1 χ₁ H _]; constructor
      · intro u y q U; obtain ⟨y,rfl⟩:=s.equi.surjective y; change Range _ _ (s.slide y) at q; have h:= s⁻¹.range q; simp only [s.left] at h; have Y:χ y < χ x:=by rw [t]; exact U
        exact mt (fun z=> (ih y (by omega)).2 z) (u y h Y)
      intro u y W v; have t':=ih y (by omega); exact mt t'.1 (u (s.slide y) (s.range W) (by rw [t] at v; exact v))
 exact h (χ x+1) x (by omega)
section Stints
-- width packing integer units

variable (V:Set Cover)
abbrev pinch :ℕ:= (box 2000).card
abbrev cluster(o:Cover)(H:Side): Set Cover:={x| x∈V ∧ Range (1000*H.val) o x}
private lemma gasB (u:ℕ)(w:2000 ≤ u)(o:Cover)(H:Side)(e:sep H.val V) : ∃ K:Finset Cover, (K:Set Cover)= cluster V o H ∧ K.card ≤ (box u).card:= by
 let X(i:Cover):Cover:= fun j=>(i j-o j)/(H.val:ℤ); let A:=cluster V o H; let K:ℤ:= H.val; have hk:0<K:=Int.natCast_pos.mpr H.property
 have h(x:Cover)(t:x∈A): X x∈box u:=by
    have v:∀ i,-(u:ℤ) ≤ X x i∧ X x i ≤ u:=by
       intro i; let a:=x i-o i; suffices -2000≤ a/K ∧ a/K≤2000 from by change -(u:ℤ)≤a/K ∧ a/K≤(u:ℤ); omega
       have p:= (show _∧ Range (1000*H.val) o x from t).2 i; have h: -1001*K ≤ a ∧ a ≤1000*K:=by unfold a K; omega
       constructor
       · apply (Int.le_ediv_iff_mul_le hk).2; linarith
       apply Int.le_of_lt_add_one; apply (Int.ediv_lt_of_lt_mul hk ?_)
       linarith
    exact box_test.mpr ⟨fun i=>(v i).1,fun i=>(v i).2⟩
 have t:Set.InjOn X A:=by
    intro x p y t he; apply e x (show x∈V∧_ from p).1 y (show y∈V∧_ from t).1; intro i; let a:=X y i; let b:=x i-o i; let c:=y i-o i; have hb:a*K≤ b ∧ b<(a+1)*K:=by
       have he:b/K=a:=congrFun he i; exact ⟨(Int.le_ediv_iff_mul_le hk).1 he.ge, (Int.ediv_lt_iff_lt_mul hk).1 (lt_of_le_of_lt he.le (by omega))⟩
    have hc:a*K ≤ c ∧ c < (a+1)*K:=by
       have he:c/K=a:=rfl; exact ⟨(Int.le_ediv_iff_mul_le hk).1 he.ge, (Int.ediv_lt_iff_lt_mul hk).1 (lt_of_le_of_lt he.le (by omega))⟩
    rw [add_mul,one_mul] at hb hc; omega
 let s:= Set.Finite.of_finite_image ((Finset.finite_toSet (box u)).subset (show X '' A ⊆ ↑(box u) from by rintro _ ⟨x,e,rfl⟩; exact h x e)) t; refine ⟨s.toFinset,s.coe_toFinset, Finset.card_le_card_of_injOn X ?_ ?_⟩; all_goals rw [s.coe_toFinset]; first|exact fun x e=>h x e|exact t
lemma gas(o:Cover)(H:Side)(e:sep H.val V) : ∃ K:Finset Cover, (K:Set Cover)= cluster V o H ∧ K.card ≤ pinch:= gasB V _ le_rfl o H e
end Stints
end Delta
end YM.CF.VolumeCape
