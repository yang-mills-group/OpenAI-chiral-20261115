import GaugeFieldConstruction.Grades

/-! Actions on the free calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction
open Function Cauchy Row Record Conj LabelAction U1 Raw
open Matter (Generation FlavorIndex)
namespace Calibration
open Floor
variable {d : Floor} (s : Signed)

def rev (s : Signed) (i : FlavorIndex) : FlavorIndex :=
  if signBit s then (i.1,i.2.2,i.2.1) else i
lemma rev_one (i) : rev 1 i=i := rfl
lemma rev_rev (i) : rev s (rev s i)=i := by cases h : signBit s <;> simp [rev,h]
lemma rev_mul (p : Signed) (i) : rev (s*p) i= rev p (rev s i) := by
  cases h : signBit s <;> cases e : signBit p <;> simp [rev,signBit_mul,h,e]

section
variable {V K M : Type*} {R : Record V K} {H : Submodule ℂ (J V)} {f : Flip V} (G : Grade R f H)
variable [AddCommGroup M] [Module ℂ M]
def onFrame (s : Signed) : Module.End ℂ (Fragment ↥H) where
  toFun u i:= G.moves s (u (rev s i))
  map_add' x y:= by ext1 i; exact map_add ..
  map_smul' x y:= by ext1 i; exact (G.moves s).map_smul _ _
lemma framed1 : onFrame G 1=1 := by
  apply LinearMap.ext; intro x; ext1 i
  change G.moves 1 (x (rev _ _)) = x i; rw [rev_one,map_one]; rfl
lemma framed (s p : Signed) : onFrame G (s*p)=onFrame G s*onFrame G p := by
  apply LinearMap.ext; intro x; ext1 i; rw [Module.End.mul_apply]; simp [onFrame,rev_mul]

def hues (g : Flavor) : Module.End ℂ (Fragment M) where
  toFun x i := pay (Flavor.bit g⁻¹ i) (x (Flavor.reprice g⁻¹ i))
  map_add' a b:= by ext1 i; simp [pay_add]
  map_smul' z a:= by ext1 i; dsimp only [Pi.smul_apply, RingHom.id_apply]; cases Flavor.bit g⁻¹ i <;> simp
lemma reverses (g : Flavor) (i : FlavorIndex) : (g⁻¹).reprice (g.reprice i)=i := by rw [← Flavor.rises,inv_mul_cancel,Flavor.rise1]
lemma reverse_sign (g : Flavor) (i : FlavorIndex) : (g⁻¹).bit (g.reprice i)=g.bit i := by
  have h:= Flavor.bit_mul g⁻¹ g i; rw [inv_mul_cancel, Flavor.bit1] at h
  cases e:(g⁻¹:Flavor).bit (g.reprice i) <;> cases p:g.bit i <;> simp_all
lemma plate (u : Fragment M) (g : Flavor) (i) : hues g u (Flavor.reprice g i)=pay (Flavor.bit g i) (u i) := by
  simp [hues,reverse_sign,reverses]
lemma hues1 : hues 1=(1:Module.End ℂ (Fragment M)) := by
  apply LinearMap.ext; intro u; ext1 i; simp [hues,Flavor.bit1,Flavor.rise1]
lemma hues_mul (g p : Flavor) : hues (g*p)=(hues g : Module.End ℂ (Fragment M))*hues p := by
  apply LinearMap.ext; intro u; ext1 i
  simp only [hues,LinearMap.coe_mk,AddHom.coe_mk,Module.End.mul_apply,mul_inv_rev, Flavor.bit_mul,Flavor.rises]
  rw [pay_comp,Bool.xor_comm]

lemma crossed (q : Flavor) : (onFrame G s)*(hues (M:=↥H) q)=hues (M:=↥H) q*(onFrame G s) := by
  apply LinearMap.ext; intro u; ext1 i
  change G.moves s (pay (Flavor.bit _ _) _) = pay (Flavor.bit _ _) _
  have hu : Flavor.reprice q⁻¹ (rev s i)= rev s (Flavor.reprice q⁻¹ i) := by cases he:signBit s <;> simp [rev,he,Flavor.reprice]
  have ht : Flavor.bit q⁻¹ (rev s i)=Flavor.bit q⁻¹ i := by
    cases he:signBit s <;> simp [rev,he,Flavor.bit,Bool.xor_comm]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk, hues,onFrame]
  rw [hu,ht]
  cases Flavor.bit q⁻¹ i <;> simp
  exact map_neg (G.moves s) (u (rev s (q⁻¹.reprice i)))
end

-- maps directly, point system positions not inputs
set_option synthInstance.maxSize 5000

def spinFrame (d : Floor) : Signed →* Module.End ℂ (UV d) where
  toFun s:= LinearMap.prodMap (1:Module.End ℂ ℂ) (LinearMap.prodMap ((gauge d).moves s)
      (LinearMap.prodMap (onFrame (matter d) s) (onFrame (mixed d) s))) -- tweak arg order
  map_one':= by rw [map_one,framed1,framed1]; rfl
  map_mul' x y:=by rw [map_mul,framed,framed]; rfl

def flavors (d : Floor) : Flavor →* Module.End ℂ (UV d) where
  toFun g:= LinearMap.prodMap (1: Module.End ℂ ℂ) (LinearMap.prodMap (1:Module.End ℂ (UG d))
    (LinearMap.prodMap (hues (M:=UF d) g) (hues (M:=UX d) g)))
  map_one':= by rw [hues1,hues1]; rfl
  map_mul' i j := by rw [hues_mul,hues_mul]; rfl

section
variable {I W : Type*} {R : Record I W} {u : Flip I} {H : Submodule ℂ (J I)}
def flipT (B : Grade R u H) : H →ₛₗ[bar] H := LinearMap.restrict u (fun x hx => B.way ⟨x,hx⟩)
end

def shade (d : Floor) : UV d →ₛₗ[bar] UV d where
  toFun u := (bar u.1, flipT (gauge d) u.2.1, (fun i=>flipT (matter d) (u.2.2.1 i)),(fun i=>flipT (mixed d) (u.2.2.2 i)))
  map_add' a b := Prod.ext (map_add bar a.1 b.1) (Prod.ext (map_add ..)
    (Prod.ext (funext fun i=>map_add ..) (funext fun i=>map_add ..)))
  map_smul' a b:= Prod.ext (by change bar (a*b.1)=bar a*bar b.1; simp)
    (Prod.ext (LinearMap.map_smulₛₗ ..) (Prod.ext (funext fun i=> LinearMap.map_smulₛₗ ..) (funext fun i=> LinearMap.map_smulₛₗ ..)))

lemma clear (x : UV d) : shade d (shade d x)=x := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact star_star x.1
  · exact Subtype.ext (g2 x.2.1.val)
  · exact funext fun i=>Subtype.ext (f2 (x.2.2.1 i).val)
  exact funext fun i=> Subtype.ext (x2 (x.2.2.2 i).val)
lemma comp_s (x : UV d) : shade d (spinFrame d s x)=spinFrame d s (shade d x) := by
  refine Prod.ext rfl ?_; refine Prod.ext ?_ (Prod.ext (funext fun i=> ?_) (funext fun i=>?_))
  · exact Subtype.ext ((gauge d).star s x.2.1 (flipT (gauge d) _) rfl)
  · exact Subtype.ext ((matter d).star s (x.2.2.1 (rev s i)) (flipT (matter d) _) rfl)
  exact Subtype.ext ((mixed d).star s (x.2.2.2 (rev s i)) (flipT (mixed d) _) rfl)
lemma color_s (x : UV d) (p : Flavor) : shade d (flavors d p x)= flavors d p (shade d x) := by
  refine Prod.ext rfl ?_; refine Prod.ext rfl (Prod.ext (funext fun i=> ?_) (funext fun i=>?_))
  · change flipT _ (pay (Flavor.bit p⁻¹ i) _) = pay _ _; cases Flavor.bit p⁻¹ i <;> simp only [pay_false,pay_true]
    · rfl
    exact map_neg (flipT (matter d)) (x.2.2.1 (p⁻¹.reprice i))
  change flipT _ (pay (Flavor.bit p⁻¹ i) _) = pay _ _; cases Flavor.bit p⁻¹ i <;> simp only [pay_false,pay_true]
  · rfl
  exact map_neg (flipT (mixed d)) (x.2.2.2 (p⁻¹.reprice i))
lemma commute (d) (p : Flavor) : Commute (spinFrame d s) (flavors d p) := LinearMap.ext fun x=>
  Prod.ext rfl (Prod.ext rfl (Prod.ext (LinearMap.congr_fun (crossed s (matter d) p) x.2.2.1)
    (LinearMap.congr_fun (crossed s (mixed d) p) x.2.2.2)))
end Calibration
end YM.GaugeFieldConstruction
