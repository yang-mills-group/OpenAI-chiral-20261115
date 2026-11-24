import GaugeFieldConstruction.Contracts
import GaugeFieldConstruction.Keeping

/-!
# Two-contract reflection and separated prices. Derivative acts yarn curl
kernels & PH kernels. Included only separated pairs here, w/out any n>=3.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick
open Gap Cauchy Row Phys Function Calibration U1 Conj Finset
open scoped BigOperators
open Matter (FlavorIndex Slot)
variable {α β γ η : Type*}

-- Put back matching colors and Slots

def matchUp {X S : Type*} [DecidableEq S] (b : Bil X X) : Bil (X×S) (X×S) := jet fun i=> jet fun j=> if i.2=j.2 then b (ket i.1) (ket j.1) else 0
def ge := matchUp (S:=Pig) colored
def yarn (b) := matchUp (S:=Slot) (directed b)
lemma matchU {X S : Type*} [DecidableEq S] (b : Bil X X) (c d : S) (x y) : matchUp b (atop c x) (atop d y)=
    if c=d then b x y else 0 := by
  have he (u v : X): matchUp b (atop c (ket u)) (atop d (ket v)) = if c=d then b (ket u) (ket v) else 0 := by rw [heights,heights,matchUp,on_ket,on_ket]
  by_cases p:c=d
  · have ht : (matchUp b).compl₁₂ (atop c) (atop d)=b := equalsB (fun i j=> (he i j).trans (if_pos p))
    rw [if_pos p]; exact LinearMap.congr_fun (LinearMap.congr_fun ht x) y
  have ht : (matchUp b).compl₁₂ (atop c) (atop d)=0 := equalsB (fun i j=> (he i j).trans (if_neg p))
  rw [if_neg p]; exact LinearMap.congr_fun (LinearMap.congr_fun ht x) y
lemma topG (i) (p q : J Pen) : ge p (lace i q)=Gap.step i (ge p q) := by
  have H : ge.compl₁₂ LinearMap.id (lace i)=ge.compr₂ (Gap.step i) := equalsB (fun ⟨x,c⟩ ⟨y,d⟩ => by
    change ge (ket _) (lace i (ket _)) = Gap.step i (ge _ _)
    rw [← heights c x,← heights d y,ge,lace,← here,matchU,matchU]; split_ifs
    · exact gradGR ..
    simp)
  exact LinearMap.congr_fun (LinearMap.congr_fun H p) q
lemma topF (d i) (p q : J Mode) : yarn d p (stride (!d) i q)=Gap.step i (yarn d p q) := by
  have H : (yarn d).compl₁₂ LinearMap.id (stride (!d) i)=(yarn d).compr₂ (Gap.step i) := equalsB (fun ⟨x,c⟩ ⟨y,v⟩=>by
    change yarn _ (ket _) (stride _ _ (ket _)) = Gap.step i (yarn d _ _)
    rw [← heights c x,← heights v y,yarn,stride,← here,matchU,matchU]; split_ifs
    · exact gradDR ..
    simp)
  exact LinearMap.congr_fun (LinearMap.congr_fun H p) q
lemma baseG (i) (p q : J Pen) : ge (lace i p) q= -Gap.step i (ge p q) := by
  have H : ge.compl₁₂ (lace i) LinearMap.id=ge.compr₂ (-Gap.step i) := equalsB (fun ⟨x,c⟩ ⟨y,d⟩ => by
    change ge (lace i (ket _)) (ket _) = - Gap.step i (ge _ _)
    rw [← heights c x,← heights d y,ge,lace,← here,matchU,matchU]; split_ifs
    · exact gradGL ..
    simp)
  exact LinearMap.congr_fun (LinearMap.congr_fun H p) q
lemma baseF (d i) (p q : J Mode) : yarn d (stride d i p) q= - Gap.step i (yarn d p q) := by
  have H : (yarn d).compl₁₂ (stride d i) LinearMap.id=(yarn d).compr₂ (-Gap.step i) := equalsB (fun ⟨x,c⟩ ⟨y,v⟩=>by
    change yarn d (stride d i (ket (x,c))) (ket (y,v)) = -Gap.step i (yarn d _ _)
    rw [← heights c x,← heights v y,yarn,stride,← here,matchU,matchU]; split_ifs
    · exact gradDL ..
    simp)
  exact LinearMap.congr_fun (LinearMap.congr_fun H p) q

/-- For the two-point contractions all forms pay yarn gap. -/
def weave' (V : Bil α β) (Q : Bil γ η) : Bil (α×γ) (β×η) := jet fun i=> jet fun j => Gap.times (V (ket i.1) (ket j.1)) (Q (ket i.2) (ket j.2))
lemma arrive (V : Bil α β) (Q : Bil γ η) (a b c d) :
    weave' V Q (times' a c) (times' b d) = Gap.times (V a b) (Q c d) := by
  have he (x y) : weave' V Q (times' a c) (times' (ket x) (ket y)) = Gap.times (V a (ket x)) (Q c (ket y)) := by
    have h : times'.compr₂ ((weave' V Q).flip (times' (ket x) (ket y)))=Gap.times.compl₁₂ (V.flip (ket x)) (Q.flip (ket y)) := equalsB (fun i j=>by
      change weave' V Q (times' _ _) (times' _ _) = Gap.times _ _; simp only [takes,weave',on_ket]; rfl)
    exact LinearMap.congr_fun (LinearMap.congr_fun h a) c
  have H : times'.compr₂ (weave' V Q (times' a c))=Gap.times.compl₁₂ (V a) (Q c) := equalsB he
  exact LinearMap.congr_fun (LinearMap.congr_fun H b) d

/-- Reflection not part of the price. Two slots, arrangements of F. -/
def gaugeGap : Bil GaugePair GaugePair := weave' ge ge + (weave' ge ge).compl₁₂ LinearMap.id (Phys.swap Pen)
/-- First and fourth & second and third. No Wick sign. -/
def fGap : Bil Spair Spair := (weave' (yarn false) (yarn true)).compl₁₂ LinearMap.id (Phys.swap Mode)
/-- Last slot lies outside the Spin arrangement. -/
def xGap : Bil Trip Trip := weave' fGap ge

theorem gauge_contract (a b c d : J Pen) {x : E4} : eye x (gaugeGap (times' a b) (times' c d))=
    eye x (ge a c) * eye x (ge b d) + eye x (ge a d) * eye x (ge b c) := by
  change eye x (weave' _ _ (times' a b) (times' c d)+ weave' ge ge (times' a b) (Phys.swap _ (times' c d)))=_
  rw [map_add, Phys.swap_apply,arrive,arrive,Gap.tick,Gap.tick]
theorem f_pay (a b c d : J Mode) : fGap (times' a b) (times' c d)=Gap.times (yarn false a d) (yarn true b c) := by
  change weave' _ _ (times' a b) (Phys.swap _ _)=_
  rw [Phys.swap_apply, arrive]
theorem x_pay (a b : J Spair) (c d : J Pen) : xGap (times' a c) (times' b d)= Gap.times (fGap a b) (ge c d) := arrive ..

lemma surges (V : Bil α β) (Q : Bil γ η) (p : Module.End ℂ (J β)) (g : Module.End ℂ (J η)) (i : Axis)
    (h : ∀ a b, V a (p b)=Gap.step i (V a b)) (H : ∀ a b,Q a (g b)=Gap.step i (Q a b)) (a b) :
    weave' V Q a (splitD p g b)=Gap.step i (weave' V Q a b) := by
  have HT: (weave' V Q).compl₁₂ LinearMap.id (splitD p g)=(weave' V Q).compr₂ (Gap.step i) := equalsB (fun x y=>by
    change weave' V Q (ket x) (splitD p g (ket y))=Gap.step i _
    change weave' V Q _ _=Gap.step i (weave' V Q (ket x) (ket y))
    rw [← takes x.1 x.2,← takes y.1 y.2, split_legs,map_add]; simp only [arrive,h,H,Gap.keep])
  exact LinearMap.congr_fun (LinearMap.congr_fun HT a) b
lemma fades (V : Bil α β) (Q : Bil γ η) (p : Module.End ℂ (J α)) (g : Module.End ℂ (J γ)) (i : Axis)
    (h : ∀ a b, V (p a) b= -Gap.step i (V a b)) (H : ∀ a b,Q (g a) b= -Gap.step i (Q a b)) (a b) :
    weave' V Q (splitD p g a) b = -Gap.step i (weave' V Q a b) := by
  have HT : (weave' V Q).compl₁₂ (splitD p g) LinearMap.id=(weave' V Q).compr₂ (-Gap.step i) := equalsB (fun x y=>by
    change weave' V Q (splitD p g (ket x)) (ket y)= - Gap.step i (weave' V Q (ket x) (ket y))
    rw [← takes x.1 x.2,← takes y.1 y.2,split_legs,map_add]; simp only [LinearMap.add_apply,arrive,h,H,Gap.keep,map_neg,LinearMap.neg_apply,neg_add])
  exact LinearMap.congr_fun (LinearMap.congr_fun HT a) b
lemma g_R (a b) (i) : gaugeGap a (Phys.eyes i b)=Gap.step i (gaugeGap a b) := by
  have h:=surges ge ge _ _ _ (topG i) (topG i)
  change weave' _ _ a _ + weave' ge ge a (Phys.swap _ _)= Gap.step _ (weave' ge ge _ _ + _)
  rw [map_add,Phys.also,Phys.eyes,h,h]; rfl
lemma g_L (a b) (i) : gaugeGap (Phys.eyes i a) b = - Gap.step i (gaugeGap a b) := by
  have h:=fades ge ge _ _ _ (baseG i) (baseG i)
  change weave' _ _ (Phys.eyes i a) b + weave' ge ge (Phys.eyes i a) (Phys.swap _ _)= - Gap.step i (weave' ge ge _ _ + weave' ge ge _ _)
  rw [Phys.eyes,h,h,map_add,neg_add]; rfl

lemma swap_split (a : J (α×α)) (p q) : Phys.swap _ (splitD p q a)=splitD q p (Phys.swap _ a) := by
  have h : Phys.swap _ ∘ₗ splitD p q= splitD q p ∘ₗ Phys.swap _ := crossing fun i j=>by
    simp only [LinearMap.comp_apply,split_legs,map_add,Phys.swap_apply]; rw [add_comm]
  exact LinearMap.congr_fun h a
lemma f_R (a b) (i) : fGap a (bones i b)=Gap.step i (fGap a b) := by
  change weave' _ _ _ (Phys.swap _ (bones i b))=Gap.step i _
  rw [bones,swap_split]; exact surges _ _ _ _ i (topF false i) (topF true i) _ _
lemma f_L (a b) (i) : fGap (bones i a) b = - Gap.step i (fGap a b) := fades (yarn false) (yarn true) _ _ i (baseF false i) (baseF true i) a (Phys.swap _ b)
lemma x_R (a b) (i) : xGap a (back i b) = Gap.step i (xGap a b) := surges fGap ge _ _ i (fun a b=> f_R a b i) (topG i) a b
lemma x_L (a b) (i) : xGap (back i a) b = -Gap.step i (xGap a b) := fades fGap ge _ _ i (fun a b=> f_L a b i) (baseG i) a b

def oneG := cut (fun _=> (1:ℂ)) fun _ _=> contDiffAt_const
def cyc (a b : Book) := ((a.1*b.1) • oneG) + gaugeGap a.2.1 b.2.1 + fGap a.2.2.1 b.2.2.1 + xGap a.2.2.2 b.2.2.2
def pair : Book →ₗ[ℂ] Book →ₗ[ℂ] SmoothGap := LinearMap.mk₂ ℂ cyc
  (fun a b c=>by simp only [cyc,Prod.fst_add,Prod.snd_add,add_mul,add_smul,map_add,LinearMap.add_apply]; abel)
  (fun r a b=>by unfold cyc; change ((r*a.1*b.1) • _) + gaugeGap (r • a.2.1) _ + fGap (r • a.2.2.1) _ + xGap (r • a.2.2.2) _ = _; simp only [map_smul, LinearMap.smul_apply,smul_add,mul_assoc,smul_smul])
  (fun a b c=>by simp only [cyc,Prod.fst_add,Prod.snd_add,mul_add,add_smul,map_add]; abel)
  (fun r a b=>by unfold cyc; change ((a.1*(r*b.1)) • _) + gaugeGap _ (r • b.2.1) + fGap _ (r • b.2.2.1) + xGap _ (r • b.2.2.2) = _; rw [mul_left_comm]; simp only [map_smul, smul_add,smul_smul])
lemma one₀ (i) : Gap.step i oneG=0 := Gap.individuated fun t ht=>by rw [oneG,reveal _ _ _ ht]; simp [YM.Maxwell.grad, YM.Analysis.D]
lemma r_pay (i) (a b) : pair a (press i b)=Gap.step i (pair a b) := by
  change cyc a (press i b)= Gap.step i (cyc a b)
  simp only [cyc, map_add,map_smul,one₀,smul_zero, zero_add,press, LinearMap.prodMap_apply,LinearMap.zero_apply, mul_zero,zero_smul]; rw [g_R,f_R,x_R]
lemma l_pay (i) (a b) : pair (press i a) b = -Gap.step i (pair a b) := by
  change cyc (press i a) b= - Gap.step i (cyc a b)
  simp only [cyc,map_add,map_smul,one₀,smul_zero,zero_add,neg_add,press,LinearMap.prodMap_apply,LinearMap.zero_apply,zero_mul,zero_smul]; rw [g_L, f_L,x_L]

def couples : Shell →ₗ[ℂ] Shell →ₗ[ℂ] SmoothGap := pair.compl₁₂ dress dress
lemma left_leg (i) (a b) : couples (P i a) b= - Gap.step i (couples a b) := by
  change pair (dress _) _= - Gap.step i (pair _ _); rw [Phys.likes,l_pay]
lemma right_leg (i) (a b) : couples a (P i b)= Gap.step i (couples a b) := by
  change pair _ (dress _)=Gap.step i (pair _ _); rw [Phys.likes,r_pay]
end YM.GaugeFieldConstruction.Wick
