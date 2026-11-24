import GaugeFieldConstruction.Down
/-!
# Exact free normalizations in (97)-(99)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Calibration.RawBank
open Gap Cauchy Conj Row Phys Function Submodule U1 Flux One Stage Wide Stage.Cell One.Lamp Floor
open Matter (Slot FlavorIndex)
open Matrix
open scoped Matrix BigOperators Topology ContDiff

noncomputable abbrev YG (i):= Mint.spin (DeckG i) (gCard i)
noncomputable abbrev YF (i):= Mint.spin (DeckF i) (fCard i)
noncomputable abbrev YX (i p q):= Mint.spin (DeckX i) (xCard i p q)
lemma visitG (d Ω x): YG d Ω ((DeckG d).issue x) = (DeckG d).issue ((gCard d).beta Ω x) := Mint.click (DeckG d) (gCard d) (leavesG d) Ω x
lemma visitF (d Ω x): YF d Ω ((DeckF d).issue x)=(DeckF d).issue ((fCard d).beta Ω x) := Mint.click _ _ (leavesF d) Ω x
lemma visitX (d i j Ω x): YX d i j Ω ((DeckX d).issue x)=(DeckX d).issue ((xCard d i j).beta Ω x) := Mint.click _ _ (leavesX d i j) Ω x
lemma field_g (d x):YG d 0 x=0 := by
  obtain ⟨a,rfl⟩:=(DeckG d).supply x; rw [visitG]; suffices H : (gCard d).beta 0=0 by rw [H,LinearMap.zero_apply,map_zero]
  apply ket_ext; intro i; simp [Cell.beta,bill]
lemma field_f (d x):YF d 0 x=0 := by
  obtain ⟨a,rfl⟩:=(DeckF d).supply x; rw [visitF]; suffices H : (fCard d).beta 0=0 by rw [H,LinearMap.zero_apply,map_zero]
  apply ket_ext; intro i; simp [Cell.beta,bill]

variable (m :ℂ) (V : Bool→ℂ)
abbrev Lg := gloG (gStress m)
abbrev Lf := gloF (fStress V)
abbrev Lx := gloX (fStress V) (gStress m)

def SY (d) (Ω:Rotors) : Module.End ℂ (UV d) := LinearMap.prodMap 0 (LinearMap.prodMap
  (m • YG d Ω) (LinearMap.prodMap
    (LinearMap.pi (fun k : FlavorIndex=> V k.1 • YF d Ω ∘ₗ LinearMap.proj k))
    (LinearMap.pi (fun k : FlavorIndex => (m • YX d true false Ω + V k.1 • YX d false true Ω) ∘ₗ LinearMap.proj k))))
def packΘ (v : E4): UV four →ₗ[ℂ] UV five := (LinearMap.prodMap 0 (LinearMap.prodMap (m • LinearMap.id)
  (LinearMap.prodMap (LinearMap.pi fun i : FlavorIndex=>V i.1 • (LinearMap.proj i : Fragment (UF five) →ₗ[ℂ] UF five)) 0))) ∘ₗ (∑ i:Axis,(v i:ℂ) • deriv i)

variable {K : Dollars} {x y : E4} {χ : E4→ℝ}
lemma pinX (d : Floor) (Ω z): YX d true false Ω z + YX d false true Ω z=YX d true true Ω z := by -- binder
  obtain ⟨b,rfl⟩:=(DeckX d).supply z; rw [visitX,visitX,visitX,← map_add]; congr 1; rw [← tripleL d true true Ω,scratch]; simp [activates]
lemma noneX (d Γ z): YX d false false Γ z =0:=by
  obtain ⟨z,rfl⟩:=(DeckX d).supply z; rw [visitX,← tripleL,scratch]; simp [activates]

lemma Fcom {K : Lamp Spair Spair} {χ : E4→ℝ} {Y x y} {a b : Fragment (J Row.f)} (h : Course Y) (u : Chassis x y χ) (p:∀ i,K.Latch χ Y x y (tiap i (a i)) (tiap i (b i))) : K.Latch χ Y x y (graph_f a) (graph_f b) := by
  unfold graph_f; rw [LinearMap.sum_apply,LinearMap.sum_apply]; apply Lamp.summed K h u; intro i _; rw [LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.proj_apply]; exact p i
lemma Xcom {K : Lamp Trip Trip} {χ : E4→ℝ} {Y x y} {a b : Fragment (J Row.x)} (h : Course Y) (u : Chassis x y χ) (p:∀ i,K.Latch χ Y x y (tuap i (a i)) (tuap i (b i))) : K.Latch χ Y x y (graph_x a) (graph_x b) := by
  unfold graph_x; rw [LinearMap.sum_apply,LinearMap.sum_apply]; apply Lamp.summed K h u; intro i _; rw [LinearMap.comp_apply,LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.proj_apply]; exact p i
lemma atF (d : Floor) (b : UV d) (i) : (shells d b).2.2.1 i=(b.2.2.1 i).val:=rfl
lemma atX (d : Floor) (b : UV d) (i) : (shells d b).2.2.2 i=(b.2.2.2 i).val:=rfl
lemma SYf (d Ω b i): (SY m V d Ω b).2.2.1 i= V i.1 • (YF d Ω (b.2.2.1 i)):= rfl
lemma SYx (d Ω b i): (SY m V d Ω b).2.2.2 i=m • YX d true false Ω (b.2.2.2 i)+V i.1 • YX d false true Ω (b.2.2.2 i):= rfl

lemma stroke (d) (b : UV d) (u : Chassis x y χ) (Ω): Earn m V χ (soar Ω x) x y (dress (shells d b)) (dress (shells d (SY m V d Ω b))) := by
  let v:= SY m V d Ω b; apply produced m V (dress (shells d b)) (soarC Ω x) u (dress (shells d v)) rfl
  · rw [dressG,dressG]; change Latch (Lg m) _ _ _ _ (graph_g _) (graph_g (m • (YG _ _ b.2.1).val))
    have W w : Touch (Lg m) (soar Ω x) m (graph_g w.val) (graph_g (YG d Ω w).val):= by
      obtain ⟨i,rfl⟩:=(DeckG d).supply w; rw [visitG]; exact Go m (soarC Ω x).toCourse (soarT Ω x) d i
    rw [map_smul]; exact Lamp.rotor _ (W b.2.1) u
  · rw [dressF,dressF]; apply Fcom (soarC Ω x).toCourse u
    intro i
    have W (w : UF d) : Touch (Lf V) (soar Ω x) (V i.1) (tiap i w.val) (tiap i (YF d Ω w).val):=by
      obtain ⟨q,rfl⟩:=(DeckF d).supply w; rw [visitF]; exact Fo V (soarC Ω x).toCourse (soarT Ω x) d i q
    rw [atF,atF]; rw [show v=SY m V d Ω b from rfl,SYf]; simp only [Submodule.coe_smul_of_tower,map_smul]; exact Lamp.rotor (Lf V) (W (b.2.2.1 i)) u
  rw [dressX,dressX]; apply Xcom (soarC Ω x).toCourse u; intro i; rw [atX,atX, show v= SY m V d Ω b from rfl,SYx]
  obtain ⟨w,hw⟩:=(DeckX d).supply (b.2.2.2 i)
  have hp:= Xout m V Ω u i d w
  have he: (DeckX d).issue (scratch Ω d m (V i.1) w)=m • (YX d true false Ω (b.2.2.2 i))+ V i.1 • YX d false true Ω (b.2.2.2 i) := by rw [← hw,visitX,visitX,scratch,LinearMap.add_apply,map_add]; simp only [LinearMap.smul_apply,map_smul]
  rw [cash,cash,he,hw] at hp; exact hp

lemma amble (b : UV four) (u : Chassis x y χ) (v : E4) : Earn m V χ (dir v) x y (dress (shells _ b)) (dress (shells _ (packΘ m V v b))) := by
  have sk:= dirC v x
  let Y : UV five:= ∑ i:Axis,(v i:ℂ) • deriv i b
  let Q:=packΘ m V v b
  have he :shells _ Y=∑ i:Axis,(v i:ℂ) • P i (shells four b) := by
    unfold Y; rw [map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul]; rw [show P i _=_ from Eq.symm (LinearMap.congr_fun (scene i) b)]; rfl
  have hh :Q.2=(m • Y.2.1,(fun i=> V i.1 • Y.2.2.1 i),0) := by unfold Q packΘ; rw [LinearMap.comp_apply,LinearMap.sum_apply]; rfl
  apply produced m V _ sk u _
  · rfl
  · have h (w : UG four) : Touch (Lg m) (dir v) m (graph_g w.val) 0 := by
      rw [← map_zero graph_g, show (0:J Row.g)=(YG four 0 w).val from by rw [field_g]; rfl] -- adjusts invalid
      obtain ⟨q,rfl⟩:=(DeckG four).supply w; rw [visitG]; exact Go m sk.toCourse (dirT v) four q
    have hv: ∀ i a, (Lg m).P i a= Phys.eyes i a := fun _ _=> rfl
    rw [dressG,dressG]; change Latch (Lg m) _ _ _ _ (graph_g b.2.1.val) (graph_g Q.2.1.val)
    have hp := (Lg m).receives (h b.2.1) u
    have hw: Y.2.1.val=∑ i:Axis, (v i:ℂ) • P_g i b.2.1.val:= by
      have H:=congr_arg coG he; rw [map_sum] at H; simp_rw [map_smul] at H; exact H
    rw [hh]; change Latch _ _ _ _ _ _ (graph_g (m • Y.2.1.val)); rw [map_smul,hw,map_sum]; simp_rw [map_smul,Phys.line_g]; rw [zero_add] at hp; exact hp
  · rw [dressF,dressF]; apply Fcom sk.toCourse u
    intro i
    let g:=b.2.2.1 i
    have hw : (Y.2.2.1 i).val=∑ j:Axis,(v j:ℂ) • P_f j g.val:= by
      have H:=congr_arg (coF i) he; rw [map_sum] at H; simp_rw [map_smul] at H; exact H
    have hv : Touch (Lf V) (dir v) (V i.1) (tiap i g.val) (tiap i (YF four (0:Rotors) g).val):= by obtain ⟨q,r⟩:=(DeckF four).supply g; rw [← r,visitF]; exact Fo V sk.toCourse (dirT v) four i q
    rw [field_f,Submodule.coe_zero,map_zero] at hv
    have H: ∀ j:Axis, tiap i (P_f j g.val)=(Lf V).P j (tiap i g.val) := by
      intro j; change _ = bones j _; simp_rw [tiap,LinearMap.sum_apply,map_sum,LinearMap.smul_apply,map_smul,weave]
    have Hp:= (Lf V).receives hv u; rw [zero_add] at Hp
    have ty : ∑ j:Axis,(↑(dir v j x):ℂ) • (Lf V).P j (tiap i g.val) = tiap i (Y.2.2.1 i).val := by
      rw [hw,map_sum]; exact Finset.sum_congr rfl (fun j _=>by rw [map_smul,H]; rfl)
    have ex : ((packΘ m V v b).2.2.1 i).val=V i.1 • (Y.2.2.1 i).val := by change (Q.2.2.1 i).val=_; rw [hh]; rfl
    rw [atF,atF,ex,map_smul]; rw [ty] at Hp; dsimp only [Lf,g] at Hp; exact Hp
  have hn : b.2.2.2=0 := funext fun i=>Subtype.ext ((Submodule.mem_bot ℂ).mp (b.2.2.2 i).property)
  rw [cand _ _ hn,cand _ Q (by rw [hh])]; exact mints _
end YM.GaugeFieldConstruction.Calibration.RawBank
