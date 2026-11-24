import GaugeFieldConstruction.Turnstile

/-!
# Currency of reflection
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Mirror
open Cauchy Row Phys Function Calibration U1 LabelAction Raw Conj Finset Record Floor
open scoped BigOperators
open Matter (FlavorIndex Slot)
variable {α β γ : Type*} {R : Record α β}

lemma grade_eq {Q : Submodule ℂ (J α)} {Y : Flip α} [Fintype γ] (A : Labels γ) (B : Grade R Y Q)
    (g : Flip α) (q : γ→ J α) (hq : Q=space q) (hc : R.Reading A q)
    (h : ∀ i,Y (q i)=q i) (H : ∀ i,g (q i)=pay (A.cost mirror i) (q (A.move mirror i))) (z : Q) :
    g z.val=Y (B.moves mirror z).val := by
  subst Q
  classical
  obtain ⟨p,rfl⟩:= Carries.supplied q z
  rw [Carries.move_issue A q hc]; change g (∑ i:γ,p i • q i)=Y (∑ i:γ, (A.transport ℂ mirror p) i • q i)
  conv_rhs=> rw [← Equiv.sum_comp (A.equivMove mirror) (fun i=>(A.transport ℂ mirror p) i • q i)]
  rw [map_sum,map_sum]; apply Finset.sum_congr rfl
  intro i _
  dsimp only [Labels.equivMove, Equiv.coe_fn_mk]; rw [LinearMap.map_smulₛₗ,LinearMap.map_smulₛₗ,H i,h, Labels.transport_value]; cases A.cost mirror i <;> simp

lemma pure₁ (w : UG five) : flipG w.val=cG ((gauge five).moves mirror w).val := by
  refine grade_eq (g4Act.directSum g5Act) _ _ (Sum.elim evalTg evalG) (by rw [space_sum]; rfl) (reading_add readingTg readingG) ?_ ?_ w -- tweak
  exact Sum.rec (fun j=>g_tr j) (fun j=>g5_tr j)
  exact Sum.rec Gb Gp
lemma pure₂ (w : UF five) : flipF w.val=cF ((matter five).moves mirror w).val := by
  refine grade_eq ((f3Act.directSum f4Act).directSum f5Act) _ _ (Sum.elim (Sum.elim B evalTf) evalF) ?_ (reading_add (reading_add readingB readingTf) readingF) ?_ ?_ w
  · rw [space_sum, space_sum]; rfl
  · exact Sum.rec (Sum.rec f3_tr f4_tr) f5_tr
  exact Sum.rec (Sum.rec turnFB Fb) Fp
lemma pure₃ (w : UX five) : flipX w.val=cX ((mixed five).moves mirror w).val := grade_eq x5Act _ _ _ rfl readingX x5_tr Xp w

lemma liftGrade {Y : Flip α} {S T : Submodule ℂ (J α)} (A : Grade R Y S) (B : Grade R Y T) (h : S≤T) {g : Flip α}
    (H : ∀ i,g (i:T).val=Y (B.moves mirror i).val) (z : S) : g z.val=Y (A.moves mirror z).val := by
  rw [Carries.same A.toCarries B.toCarries mirror z ⟨_, h z.property⟩ rfl]; exact H ⟨z.val,h z.property⟩

-- Package into the uncapped Shell

def night : Shell →ₛₗ[bar] Shell where
  toFun x := (bar x.1, flipG x.2.1, (fun i=> flipF (x.2.2.1 (rev mirror i))), (fun i=> flipX (x.2.2.2 (rev mirror i))))
  map_add' a b := Prod.ext (map_add ..) (Prod.ext (map_add ..) (Prod.ext (funext fun _=>map_add ..) (funext fun _=> map_add ..)))
  map_smul' z x := Prod.ext (map_mul bar z x.1) (Prod.ext (LinearMap.map_smulₛₗ ..)
    (Prod.ext (funext fun _=>LinearMap.map_smulₛₗ ..) (funext fun _=>LinearMap.map_smulₛₗ ..)))
lemma price (i) (z : UV i) : night (shells i z)=shells i (shade i (spinFrame i mirror z)) := by
  simp only [shells, shade, spinFrame,LinearMap.prodMap_apply,night,LinearMap.coe_mk,AddHom.coe_mk, MonoidHom.coe_mk,OneHom.coe_mk]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · exact liftGrade (gauge i) (gauge five) (belowg i) pure₁ z.2.1
  apply Prod.ext
  · exact funext fun j=>liftGrade (matter i) (matter five) (belowf i) pure₂ (z.2.2.1 (rev mirror j))
  exact funext fun j=> liftGrade (mixed i) (mixed five) (belowx i) pure₃ (z.2.2.2 (rev mirror j))
lemma time_P (k : Axis) (i : Shell): night (P k i)=pay (clock k) (P k (night i)) := by
  cases g:clock k
  · apply Prod.ext
    · exact map_zero bar
    apply Prod.ext
    · change flipG _=P_g k (flipG i.2.1); have ht:=time_Pg k i.2.1; rw [g] at ht; exact ht
    refine Prod.ext (funext fun j=>?_) (funext fun j=>?_)
    · have he:=time_Pf k (i.2.2.1 (rev mirror j)); rw [g] at he; exact he
    have he:=time_Px k (i.2.2.2 (rev mirror j)); rw [g] at he; exact he
  apply Prod.ext
  · change bar 0= -0; simp
  apply Prod.ext
  · have he:=time_Pg k i.2.1; rw [g] at he; exact he
  refine Prod.ext (funext fun j=>?_) (funext fun j=>?_)
  · have he:=time_Pf k (i.2.2.1 (rev mirror j)); rw [g] at he; exact he
  have he:=time_Px k (i.2.2.2 (rev mirror j)); rw [g] at he; exact he

-- Book mirror

def slide := body slight (tr Pig)
def pairM : Flip Spair := Phys.swap _ ∘ₛₗ tr _
def torso := body pairM slide
def mask := body slide slide
def sky : Book →ₛₗ[bar] Book where
  toFun x:= (bar x.1,mask x.2.1, pairM x.2.2.1,torso x.2.2.2)
  map_add' x y := Prod.ext (map_add ..) (Prod.ext (map_add ..) (Prod.ext (map_add ..) (map_add ..)))
  map_smul' z x := Prod.ext (map_mul bar z x.1) (Prod.ext (LinearMap.map_smulₛₗ ..)
    (Prod.ext (LinearMap.map_smulₛₗ ..) (LinearMap.map_smulₛₗ ..)))
lemma cusp (i : FlavorIndex) : Matter.flip (Pi.single i (1:ℂ)) = Pi.single (rev mirror i) 1 := by
  ext1 j; rcases i with ⟨k,p,q⟩; rcases j with ⟨u,x,y⟩; simp [Pi.single_apply,Matter.flip,rev,and_comm]
lemma bar1 (i : FlavorIndex) : star ∘ Pi.single i (1:ℂ) = Pi.single i 1 := by ext1 j; simp only [Function.comp_apply,Pi.single_apply]; split_ifs <;> simp
lemma shα (i) (x y : Slot) : bar (alpha i x y)=alpha (rev mirror i) y x := by
  change star (Matter.coeffs _ _ _)=Matter.coeffs _ _ _
  have he:=Matter.conjugate_neut (Pi.single i 1); rw [bar1] at he
  have ht:=Matter.neutral_transpose (Pi.single i 1); rw [cusp] at ht
  rw [← ht]; change _ = Matter.coeffs _ x y; exact Matrix.ext_iff.mpr he x y
lemma shβ (i p) (x y : Slot) : bar (beta i p x y)= - beta (rev mirror i) p y x := by
  let u:= dye p
  change star (Matter.costing _ u x y)= -Matter.costing _ u y x
  have he:=Matter.conjugate_tint (Pi.single i 1) u; rw [bar1] at he
  have hv:=Matter.cost_transpose (Pi.single i 1) u; rw [cusp] at hv
  have hp: star (Matter.costing (Pi.single i 1) (Matter.cc_color u) x y)=Matter.costing (Pi.single i 1) u x y := Matrix.ext_iff.mpr he x y
  rw [← hp]
  rw [star_star]; exact Matrix.ext_iff.mpr hv y x
lemma shadowG (p : Pig) (z : GJet) : slide (atop p z)= atop p (slight z) := by
  change body _ (tr Pig) (times' z (ket p)) = times' _ _; rw [portal,tr_ket]
lemma shadowF (s : Spair): pairM (ket s)= ket (s.2,s.1) := by rw [pairM,LinearMap.comp_apply,tr_ket,Phys.swap,on_ket]
lemma perG (p : Pig) (z) : mask (yD p p z)= yD p p (flipG z) := by
  have H : mask ∘ₛₗ yD p p=yD p p ∘ₛₗ flipG := ksets (fun i=>by
    rw [← takes i.1 i.2,LinearMap.comp_apply,LinearMap.comp_apply,yD,straps,mask,portal,flipG,portal,straps,shadowG,shadowG])
  exact LinearMap.congr_fun H z
lemma perF (i j : Slot) (z) : pairM (sD i j z)=sD j i (flipF z) := by
  have H : pairM ∘ₛₗ sD i j=sD j i ∘ₛₗ flipF := ksets (fun ⟨a,b⟩=>by
    rw [LinearMap.comp_apply,LinearMap.comp_apply, Phys.band, shadowF,← takes a b,flipPair,tr_ket,tr_ket,takes,Phys.band])
  exact LinearMap.congr_fun H z
lemma perX (i j k z) : torso (fD i j k z)= -fD j i k (flipX z) := by
  have H : torso ∘ₛₗ fD i j k = -(fD j i k ∘ₛₗ flipX) := ksets (fun a=>by
    rw [← takes a.1 a.2,LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.comp_apply, torso, fD,straps,portal, perF, shadowG,flipXPair,map_neg,neg_neg,fD,straps])
  exact LinearMap.congr_fun H z
lemma intoG (z) : mask (graph_g z)=graph_g (flipG z) := by
  simp_rw [graph_g,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.map_smulₛₗ,map_sum,perG]; rw [map_div₀, map_ofNat, map_one]
lemma intoF (i) (z) : pairM (tiap i z)=tiap (rev mirror i) (flipF z) := by
  simp_rw [tiap,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,LinearMap.map_smulₛₗ, perF,shα]
  exact Finset.sum_comm
lemma intoX (i) (z) : torso (tuap i z)=tuap (rev mirror i) (flipX z) := by
  simp_rw [tuap,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,LinearMap.map_smulₛₗ, perX,shβ, neg_smul_neg]
  exact Finset.sum_comm

def revE : FlavorIndex ≃ FlavorIndex where
  toFun := rev mirror; invFun:=rev mirror; left_inv:=rev_rev _; right_inv:=rev_rev _
lemma total (u : Shell) : dress (night u)=sky (dress u) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change graph_g _=mask _; exact (intoG u.2.1).symm
  apply Prod.ext
  · rw [dressF]; change graph_f _= pairM (dress u).2.2.1; rw [dressF]
    unfold graph_f; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]
    conv_lhs=> rw [← Equiv.sum_comp revE]
    apply Finset.sum_congr rfl; intro i _; rw [LinearMap.comp_apply,LinearMap.comp_apply]; simp only [LinearMap.proj_apply]
    simp only [night,LinearMap.coe_mk,AddHom.coe_mk, revE,Equiv.coe_fn_mk]; rw [rev_rev,intoF]
  rw [dressX]; change graph_x _=torso (dress u).2.2.2; rw [dressX]
  unfold graph_x; rw [LinearMap.sum_apply,LinearMap.sum_apply,map_sum]
  conv_lhs=> rw [← Equiv.sum_comp revE]
  apply Finset.sum_congr rfl; intro i _; rw [LinearMap.comp_apply,LinearMap.comp_apply]; simp only [LinearMap.proj_apply]
  simp only [night,LinearMap.coe_mk,AddHom.coe_mk, revE, Equiv.coe_fn_mk]; rw [rev_rev, intoX]
end YM.GaugeFieldConstruction.Mirror
