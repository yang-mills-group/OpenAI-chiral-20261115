import GaugeFieldConstruction.Faces

/-!
# U1. Row coordinates and translation on shell products
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Finset Function Complex
open scoped BigOperators
namespace Cauchy
variable {α β γ η : Type*} {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Symmetry etc. can use elementary on-axis Cauchy jets. -/
def DeterminedBy {V : Type*} (f : V → J α →ₗ[ℂ] ℂ) := ∀ x, (∀ i,x ∈ LinearMap.ker (f i)) → x=0
theorem ext_jet {V : Type*} {f : V → J α →ₗ[ℂ] ℂ} (h : DeterminedBy f) {x y : J α}
    (e : ∀ i,f i x=f i y) : x=y := sub_eq_zero.mp (h _ (fun i => by
      rw [LinearMap.mem_ker,map_sub,e i,sub_self]))

/-- The tensor product here via `Finsupp`. -/
def times' : J α →ₗ[ℂ] J β →ₗ[ℂ] J (α × β) := jet fun a => jet fun b => ket (a,b)
@[simp] lemma takes (a : α) (b : β) : times' (ket a) (ket b)=ket (a,b) := by simp [times']

lemma crossing {a b : J (α × β) →ₗ[ℂ] M}
    (h : ∀ i j, a (times' (ket i) (ket j))=b (times' (ket i) (ket j))) : a=b :=
  ket_ext (fun ⟨x,y⟩ => by simpa only [takes] using h x y)

def onFirst (f : J α →ₗ[ℂ] J γ) : J (α × β) →ₗ[ℂ] J (γ × β) :=
  jet fun ⟨x,y⟩ => times' (f (ket x)) (ket y)
def onSecond (f : J β →ₗ[ℂ] J γ) : J (α × β) →ₗ[ℂ] J (α × γ) :=
  jet fun ⟨x,y⟩ => times' (ket x) (f (ket y))
def productRead (a : J α →ₗ[ℂ] ℂ) (b : J β →ₗ[ℂ] ℂ) : (J (α × β)) →ₗ[ℂ] ℂ :=
  jet fun ⟨x,y⟩ => a (ket x)* b (ket y)

-- Basic pure tensors span
lemma equalsB {f g : J α →ₗ[ℂ] J β →ₗ[ℂ] M} (h : ∀ x y, f (ket x) (ket y)=g (ket x) (ket y)) :
    f=g := ket_ext (fun i => ket_ext (h i))

@[simp] lemma first (f : J α →ₗ[ℂ] J γ) (i : J α) (j : J β) :
    onFirst f (times' i j)=times' (f i) j := by
  have h : (times' (α:=α) (β:=β)).compr₂ (onFirst f)=times' ∘ₗ f :=
    equalsB (fun x y => by change onFirst _ (times' _ _) = times' _ _; simp [onFirst])
  exact LinearMap.congr_fun (LinearMap.congr_fun h i) j
@[simp] lemma second (f : J β →ₗ[ℂ] J γ) (i : J α) (j : J β) :
    onSecond f (times' i j)=times' i (f j) := by
  have h : (times' (α:=α) (β:=β)).compr₂ (onSecond f)=
    ((times' (α:=α) (β:=γ)).flip ∘ₗ f).flip := equalsB (fun x y => by
      change onSecond _ (times' _ _) = times' _ _; simp [onSecond])
  exact LinearMap.congr_fun (LinearMap.congr_fun h i) j

lemma read_times (a : J α →ₗ[ℂ] ℂ) (b : J β →ₗ[ℂ] ℂ) (x : J α) (y : J β) :
    productRead a b (times' x y)=a x * b y := by
  have h : (times' (α:=α) (β:=β)).compr₂ (productRead a b)=(LinearMap.mul ℂ ℂ).compl₁₂ a b :=
    equalsB (fun i j => by change productRead _ _ (times' _ _) = a _ * b _; simp [productRead])
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

/-- Execute a derivative as either input in the tensor. -/
def splitD (a : Module.End ℂ (J α)) (b : Module.End ℂ (J β)) : Module.End ℂ (J (α × β)) :=
  onFirst a + onSecond b
@[simp] lemma split_legs (a : Module.End ℂ (J α)) (b : Module.End ℂ (J β)) (i : J α) (j : J β) :
    splitD a b (times' i j)=times' (a i) j+times' i (b j) := by simp [splitD]

theorem arrows (r : J α →ₗ[ℂ] ℂ) (s : J β →ₗ[ℂ] ℂ) (x y : ℂ)
    (a : Module.End ℂ (J α)) (b : Module.End ℂ (J β)) (ha : r ∘ₗ a=x • r) (hb : s ∘ₗ b=y • s) :
    productRead r s ∘ₗ splitD a b = (x+y) • productRead r s := by
  apply crossing; intro i j
  simp only [LinearMap.comp_apply, split_legs, map_add, LinearMap.smul_apply, smul_eq_mul, read_times]
  rw [← LinearMap.comp_apply r, ← LinearMap.comp_apply s,ha,hb]
  simp only [LinearMap.smul_apply, smul_eq_mul]; ring

def oneWay (s : J β →ₗ[ℂ] ℂ) : J (α × β) →ₗ[ℂ] J α := jet fun ⟨x,y⟩ => s (ket y) • ket x
def another (r : J α →ₗ[ℂ] ℂ) : J (α × β) →ₗ[ℂ] J β := jet fun ⟨x,y⟩ => r (ket x) • ket y

/-- The chart tests continue to separate without any pair cancellations. -/
theorem paid_pair {f : γ → J α →ₗ[ℂ] ℂ} {u : η → J β →ₗ[ℂ] ℂ}
    (h : DeterminedBy f) (g : DeterminedBy u) :
    DeterminedBy fun p : γ × η => productRead (f p.1) (u p.2) := by
  classical
  intro X he
  have hm (r : J α →ₗ[ℂ] ℂ) (s : J β →ₗ[ℂ] ℂ) : productRead r s=r ∘ₗ oneWay s := by
    apply ket_ext; rintro ⟨x,y⟩; rw [productRead, LinearMap.comp_apply, oneWay, on_ket,on_ket]
    rw [map_smul]; exact mul_comm ..
  have hu j : oneWay (α:=α) (u j) X=0 := h _ (fun i => by
    rw [LinearMap.mem_ker,← LinearMap.comp_apply,← hm]; exact he (i,j))
  have ha (r : J α →ₗ[ℂ] ℂ) : another r X=0 := g _ (fun i => by
    have hv : u i ∘ₗ another r=productRead r (u i) := by
      apply ket_ext; rintro ⟨x,y⟩; simp [productRead,another]
    rw [LinearMap.mem_ker,← LinearMap.comp_apply, hv,hm,LinearMap.comp_apply,hu, map_zero])
  ext1 ⟨x,y⟩
  have hf : Finsupp.lapply (R:=ℂ) y ∘ₗ another (Finsupp.lapply x)=
      (Finsupp.lapply (x,y) : J (α × β) →ₗ[ℂ] ℂ) := by
    apply ket_ext; rintro ⟨i,j⟩
    simp only [LinearMap.comp_apply, another,on_ket, map_smul]
    change ket i x * ket j y=ket _ _
    by_cases h : i=x <;> by_cases k : j=y <;> simp [ket,h,k]
  change Finsupp.lapply (R:=ℂ) (x,y) X=0
  rw [← hf, LinearMap.comp_apply, ha,map_zero]

/- Specializations to g, f, x of U1. The color or species Slot factor
is held fixed and nonzero in this test. (Determination of how many
intertwining copies is a separate argument.) -/
namespace Row
open Raw Chart
abbrev g := GIndex × GIndex
abbrev f := FIndex × FIndex
abbrev x := f × GIndex
abbrev Pol := {c : Chart // c.l≠0}
abbrev Surface := Pol × Bool

def eg (j : Surface) := (j.1.val.face j.2).read
def ef (b : Bool) (j : Pol) := (j.val.fermi b).read
def gChart (p : Surface × Surface) := productRead (eg p.1) (eg p.2)
def fChart (p : Pol × Pol) := productRead (ef false p.1) (ef true p.2)
def xChart (p : (Pol × Pol) × Surface) := productRead (fChart p.1) (eg p.2)

theorem loyalty : DeterminedBy eg := fun a h => chart_Maxwell a (fun c i p => h (⟨c,p⟩,i))
theorem skin (b : Bool) : DeterminedBy (ef b) := fun a h => chart_Weyl b a (fun c p => h ⟨c,p⟩)
theorem chart_g : DeterminedBy gChart := paid_pair loyalty loyalty
theorem chart_f : DeterminedBy fChart := paid_pair (skin false) (skin true)
theorem chart_x : DeterminedBy xChart := paid_pair chart_f loyalty

def P_g (k : Axis) := splitD (Gder k) (Gder k)
def P_f (k : Axis) := splitD (Cder false k) (Cder true k)
def P_x (k : Axis) := splitD (P_f k) (Gder k)

def L (k : Axis) := splitD (-(Cder false k)) (Cder true k)

lemma ge_charge (k : Axis) (i j : Maxwell) :
    productRead i.read j.read ∘ₗ P_g k = (i.p k+j.p k) • productRead i.read j.read :=
  arrows _ _ _ _ _ _ (i.frequency k) (j.frequency k)
lemma ph_charge (k : Axis) (i : Weyl false) (j : Weyl true) :
    productRead i.read j.read ∘ₗ P_f k = (i.p k+j.p k) • productRead i.read j.read :=
  arrows _ _ _ _ _ _ (i.frequency k) (j.frequency k)
lemma x_charge (k : Axis) (i : Weyl false) (j : Weyl true) (v : Maxwell) :
    productRead (productRead i.read j.read) v.read ∘ₗ P_x k = (i.p k+j.p k+v.p k) •
      productRead (productRead i.read j.read) v.read :=
  arrows _ _ _ _ _ _ (ph_charge _ _ _) (v.frequency k)
lemma l_charge (k : Axis) (i : Weyl false) (j : Weyl true) :
    productRead i.read j.read ∘ₗ L k = (j.p k-i.p k) • productRead i.read j.read := by
  rw [sub_eq_add_neg, add_comm]
  apply arrows; rw [LinearMap.comp_neg,i.frequency]; simp
  exact j.frequency k

theorem commuting {F : γ → J α →ₗ[ℂ] ℂ} (h : DeterminedBy F)
    {X Y : J α →ₗ[ℂ] J α} (p q : γ → ℂ) (hp : ∀ i,F i ∘ₗ X = p i • F i)
    (hq : ∀ i, F i ∘ₗ Y=q i • F i) (a : J α) : X (Y a)=Y (X a) := ext_jet h fun i => by
  rw [← LinearMap.comp_apply, hp, ← LinearMap.comp_apply (F i), hq]
  rw [LinearMap.smul_apply, LinearMap.smul_apply]
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply (F i), hq, hp]
  simp [mul_left_comm]

theorem gc (k j : Axis) (a) : P_g k (P_g j a)=P_g j (P_g k a) := 
  commuting chart_g (fun i => i.1.1.val.mom k + i.2.1.val.mom k) (fun i => i.1.1.val.mom j + i.2.1.val.mom j)
  (fun ⟨i,j⟩ => ge_charge k (face i.1.val i.2) (face j.1.val j.2))
  (fun ⟨u,v⟩ => ge_charge j (face u.1.val u.2) (face v.1.val v.2)) a

theorem fc (k j : Axis) (a) : P_f k (P_f j a)=P_f j (P_f k a) := 
  commuting chart_f (fun i => i.1.val.mom k + i.2.val.mom k) (fun i => i.1.val.mom j + i.2.val.mom j)
  (fun ⟨i,t⟩ => ph_charge k (fermi i.val false) (fermi t.val true))
  (fun ⟨i,t⟩ => ph_charge j (fermi i.val false) (fermi t.val true)) a

theorem xc (k j : Axis) (a) : P_x k (P_x j a)=P_x j (P_x k a) := 
  commuting chart_x (fun i => i.1.1.val.mom k + i.1.2.val.mom k + i.2.1.val.mom k) (fun i => i.1.1.val.mom j + i.1.2.val.mom j + i.2.1.val.mom j)
  (fun ⟨⟨i,t⟩,v⟩ => x_charge k (fermi i.val false) (fermi t.val true) (face v.1.val v.2))
  (fun ⟨⟨i,t⟩,v⟩ => x_charge j (fermi i.val false) (fermi t.val true) (face v.1.val v.2)) a

/-- Two *same color* F legs: symmetrize with both placements, no division. -/
def Bose (x y : GJet) := times' x y + times' y x

def arc (w : Wed) := F w.toBlade.val.1 w.toBlade.val.2

def B (i : Axis) := ∑ a:Spin, ∑ b:Spin, Hij i a b • times' (C a 0) (C b 0)

-- The evaluation of m labels, in the coordinate system for which the
-- theorems `chart_g, chart_f, chart_x` hold.
def evalTg (a : G4) := Bose (arc a.val.1) (arc a.val.2)
def evalG (a : G5) := Bose (arc a.1) (Gder a.2.2 (arc a.2.1))
def evalTf (a : F4) := a.2.elim (fun k => L k (B a.1)) (fun k => P_f k (B a.1))
def evalF (a : F5) : J f :=
  a.2.elim (fun t => L t.val.1 (L t.val.2 (B a.1))) <| fun z =>
    z.elim (fun t => P_f t.val.1 (P_f t.val.2 (B a.1))) (fun p => P_f p.1 (L p.2 (B a.1)))
def evalX (a : X5) := times' (B a.1) (arc a.2)

-- Check a consistency: ordinary translation of f at degree four admits
-- a common representation at the next degree. More such kinematics later.
lemma Ls (k j : Axis) (a) : L k (L j a)=L j (L k a) := 
  commuting chart_f (fun i => i.2.val.mom k - i.1.val.mom k) (fun i => i.2.val.mom j - i.1.val.mom j)
  (fun ⟨i,t⟩ => l_charge k (fermi i.val false) (fermi t.val true))
  (fun ⟨i,t⟩ => l_charge j (fermi i.val false) (fermi t.val true)) a
lemma eval_SL (i j k : Axis) : evalF (i,Sum.inr (Sum.inr (j,k)))= P_f j (evalTf (i,Sum.inl k)) := rfl
lemma eval_SS (i j k : Axis) : evalF (i,Sum.inr (Sum.inl (ordered j k)))= P_f j (evalTf (i,Sum.inr k)) := by
  unfold ordered; split
  · exact fc k j _
  rfl
lemma eval_LL (i j k : Axis) : evalF (i,Sum.inl (ordered j k))= L j (evalTf (i,Sum.inl k)) := by
  unfold ordered; split
  · exact Ls k j _
  rfl
end Row
end Cauchy
end YM.GaugeFieldConstruction
