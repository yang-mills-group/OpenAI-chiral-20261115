import GaugeFieldConstruction.SpinPay
import GaugeFieldConstruction.TestsPay

/-!
# c-real form on the shell rows. Caution: anti-linear involution.
  The Spin action even of pure c is nontrivial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Cauchy.Conj
open Finset Function Complex Raw Row Matrix
open scoped BigOperators Matrix
variable {α β : Type*}
abbrev bar := starRingEnd ℂ
abbrev Flip (α : Type*) := J α →ₛₗ[bar] J α

def tr (α : Type*) : Flip α where
  __ := Finsupp.mapRange.addMonoidHom ((starRingEnd ℂ).toAddMonoidHom)
  map_smul' z a:=by ext1 i; simp [bar, mul_comm]
lemma tr_ket (a : α) : tr α (ket a)=ket a := by
  classical
  ext1 i; change bar (ket a i)=_
  simp [ket,Finsupp.single_apply]

def comb (f : α → J β) := (jet f) ∘ₛₗ tr α -- annotate
lemma onet (f : α → J β) (a) : comb f (ket a)=f a := by rw [comb,LinearMap.comp_apply,tr_ket,on_ket]
lemma ksets {u v : J α →ₛₗ[bar] J β} (h : ∀ a : α,u (ket a)=v (ket a)) : u=v := Finsupp.lhom_ext fun i c=> by
  rw [show Finsupp.single i c=c • ket i from by simp [ket],LinearMap.map_smulₛₗ,LinearMap.map_smulₛₗ,h]

def body (F : Flip α) (G : Flip β) : Flip (α×β) := comb fun j=> times' (F (ket j.1)) (G (ket j.2))
theorem portal (F : Flip α) (G : Flip β) (x : J α) (y : J β) :
    body F G (times' x y)= times' (F x) (G y) := by
  have he i y : body F G (times' (ket i) y)=times' (F (ket i)) (G y) := by
    have ht : body F G ∘ₛₗ times' (ket i)= times' (F (ket i)) ∘ₛₗ G := ksets fun j=> by
      simp only [LinearMap.comp_apply,takes,body,onet]
    exact LinearMap.congr_fun ht y
  have hv : body F G ∘ₛₗ times'.flip y= times'.flip (G y) ∘ₛₗ F := ksets (fun i=>he i y)
  exact LinearMap.congr_fun hv x

/-- spinJ in both halves (real). -/
def blockSpin (a b : Spin) : ℂ := CF.spinJ (band false a) (band false b)
def vcc : Flip FIndex := comb fun j=> ∑ a : Spin, blockSpin a j.1 • C a j.2
lemma same_band (a b : Spin) : CF.spinJ (band true a) (band true b) = blockSpin a b := by fin_cases a <;> fin_cases b <;> rfl
lemma duo {V : Type*} [AddCommGroup V] (f : Spin → V) : ∑ i:Spin,f i=f 0+f 1 := by simp
lemma trio {V : Type*} [AddCommGroup V] (f : S3 → V) : ∑ i:S3,f i=f 0+f 1+f 2 := by
  rw [Fin.sum_univ_castSucc]; simp [add_assoc]
lemma c0 (n : MI) : vcc (C 0 n)= - C 1 n := by
  rw [vcc,C,onet,duo]
  change (0:ℂ) • C 0 n + (-1:ℂ) • C 1 n = _ -- first scalar
  simp
lemma c1 (n : MI) : vcc (C 1 n)= C 0 n := by
  rw [vcc,C,onet,duo]
  change (1:ℂ) • C 0 n + (0:ℂ) • C 1 n = _; simp

lemma realistic (w : Wed) : tr GIndex (arc w)=arc w := by
  have he (g m n) : tr GIndex (G g m n)=G g m n := by
    unfold G; split_ifs
    · exact tr_ket ..
    rw [map_neg,map_add,tr_ket,tr_ket]
  suffices ∀ (i j : Axis) z,tr _ (F i j z)=F i j z from this ..
  intro i j z
  refine Fin.lastCases (i:=i) ?_ fun i' => ?_ <;> refine Fin.lastCases (i:=j) ?_ fun j'=> ?_
  all_goals simp only [F,Fin.lastCases_castSucc,Fin.lastCases_last]
  all_goals first | exact he .. | exact map_zero _ | rw [map_neg,he] | (split_ifs <;> simp [he])

lemma Gmoves (i : Axis) : tr GIndex ∘ₛₗ Gder i=Gder i ∘ₛₗ tr GIndex := by
  have he (g m n) : tr GIndex (G g m n)=G g m n := by unfold G; split_ifs; exact tr_ket ..; rw [map_neg,map_add,tr_ket,tr_ket]
  apply ksets; intro j
  simp only [LinearMap.comp_apply,tr_ket]
  refine Fin.lastCases (i:=i) ?_ fun k => ?_
  · rw [show Fin.last 3=τ from rfl,Glast,Gtime,on_ket]; dsimp only; rw [map_sub,he,he]
  rw [Gspace,Gshift,on_ket]; exact he ..

lemma Cmoves (b : Bool) (i : Axis) : vcc ∘ₛₗ Cder b i=Cder b i ∘ₛₗ vcc := by
  -- spatial shift, time differential
  apply ksets
  rintro ⟨i',n⟩
  change vcc _=Cder _ _ (vcc (C i' n))
  have hv : i'=0 ∨ i'=1 := by fin_cases i' <;> decide
  refine Fin.lastCases (i:=i) ?_ fun k => ?_
  · change vcc (Cder b τ (ket _)) = Cder b τ _
    have hc (a : Spin) (b) (n) : Cder b τ (C a n)= -∑ k : S3, ∑ c: Spin, coeffCR b k.castSucc a c • C c (bump k n) := by rw [Clast, C, Ctime,on_ket]
    change vcc (Cder b τ (C i' n))= Cder b τ (vcc (C i' n))
    rcases hv with v|v <;> subst i' <;> cases b <;>
      simp only [c0,c1,map_neg,hc, trio,duo,map_add, Chart.cast0,Chart.cast1,Chart.cast2,LinearMap.map_smulₛₗ] <;>
      simp [bar,c0,c1,coeffCR,Hij] <;> abel
  change vcc (Cder b _ (C i' n))=Cder b _ (vcc (C i' n))
  have hc (i) : Cder b k.castSucc (C i n)= C i (bump k n) := by rw [Cspace,C, Cshift,on_ket]
  rcases hv with v|v <;> rw [v,hc]
  · rw [c0,c0,map_neg,hc]
  rw [c1,c1,hc]

lemma screen (i : Axis) : body vcc vcc (B i)= B i := by
  rw [B,duo]; simp only [duo, map_add,LinearMap.map_smulₛₗ]
  simp_rw [portal,c0,c1]; fin_cases i <;> norm_num [bar,Hij] <;> abel

def cG := body (tr GIndex) (tr GIndex)
def cF := body vcc vcc
def cX := body cF (tr GIndex)
lemma g_tr (i:G4) : cG (evalTg i)=evalTg i := by simp [evalTg,cG,Bose,portal,realistic]
lemma g5_tr (i:G5) : cG (evalG i)=evalG i := by
  have he (i) (j) : tr GIndex (Gder i (arc j))= Gder i (arc j) := by
    have h := LinearMap.congr_fun (Gmoves i) (arc j); simpa only [LinearMap.comp_apply,realistic] using h
  simp [evalG,cG,Bose,portal,realistic,he]

lemma induced (u : Flip α) (v : Flip β) (X : Module.End ℂ (J α)) (Y : Module.End ℂ (J β))
    (h : u ∘ₛₗ X=X ∘ₛₗ u) (p : v ∘ₛₗ Y=Y ∘ₛₗ v) : body u v ∘ₛₗ splitD X Y=splitD X Y ∘ₛₗ body u v := by
  refine ksets (fun i => ?_)
  change body u v (splitD X Y (ket i)) = _
  rw [← takes i.1 i.2,split_legs,map_add,LinearMap.comp_apply]; repeat rw [portal]
  rw [split_legs]
  rw [show ∀ a, u (X a)=X (u a) from fun a=>LinearMap.congr_fun h a,
    show ∀ a,v (Y a)=Y (v a) from fun a=> LinearMap.congr_fun p a]
lemma G_tr (k : Axis) (a : J g) : cG (P_g k a)=P_g k (cG a) := LinearMap.congr_fun (induced _ _ _ _ (Gmoves k) (Gmoves k)) a
lemma f_tr (k : Axis) (a : J f) : cF (P_f k a)= P_f k (cF a) :=
  LinearMap.congr_fun (induced _ _ _ _ (Cmoves false k) (Cmoves true k)) a
lemma x_tr (k : Axis) (a : J x) : cX (P_x k a)=P_x k (cX a) :=
  LinearMap.congr_fun (induced cF (tr GIndex) (P_f k) (Gder k) (LinearMap.ext (f_tr k)) (Gmoves k)) a
lemma cL (k : Axis) (a : J f) : cF (L k a)=L k (cF a) := by
  have h : vcc ∘ₛₗ (-Cder false k)=(-Cder false k) ∘ₛₗ vcc := by
    apply LinearMap.ext; intro i
    simp only [LinearMap.comp_apply,LinearMap.neg_apply,map_neg]
    rw [show vcc (Cder false k i)= Cder false k (vcc i) from LinearMap.congr_fun (Cmoves false k) _]
  exact LinearMap.congr_fun (induced _ _ _ _ h (Cmoves true k)) a
lemma f3_tr (i : Axis) : cF (B i) = B i := screen i
lemma f4_tr (k : F4) : cF (evalTf k)=evalTf k := by
  rcases k with ⟨j,u|v⟩ <;> simp only [evalTf,Sum.elim_inl,Sum.elim_inr,cL,f_tr,f3_tr]
lemma f5_tr (k : F5) : cF (evalF k)=evalF k := by
  rcases k with ⟨j,u|v|⟨x,y⟩⟩ <;> simp only [evalF,Sum.elim_inl,Sum.elim_inr,cL,f_tr,f3_tr]
lemma x5_tr (k : X5) : cX (evalX k)=evalX k := by rw [evalX,cX,portal,realistic,f3_tr]
lemma bi (x : CJet) : vcc (vcc x)= -x := by
  have h : vcc ∘ₛₗ vcc= -LinearMap.id (R:=ℂ) (M:=CJet) := ket_ext (fun ⟨a,n⟩=>by
    change vcc (vcc (C a n))= - C a n
    have h : a=0 ∨ a=1 := by fin_cases a <;> decide
    rcases h with p|p <;> subst a <;> simp only [c0,c1,map_neg])
  exact LinearMap.congr_fun h x
lemma f2 (x : J f) : cF (cF x)=x := by
  have h : cF ∘ₛₗ cF= LinearMap.id (R:=ℂ) (M:=J f) := crossing fun x y => by
    rw [LinearMap.comp_apply,LinearMap.id_apply,cF,portal,portal,bi,bi]; simp
  exact LinearMap.congr_fun h x
lemma tr2 (x : J α) : tr α (tr α x) = x := by
  have h : tr α ∘ₛₗ tr α = LinearMap.id (R:=ℂ) := ket_ext fun i => by simp only [LinearMap.comp_apply, tr_ket,LinearMap.id_apply]
  exact LinearMap.congr_fun h x
lemma g2 (x : J g) : cG (cG x)=x := by
  have h : cG ∘ₛₗ cG= LinearMap.id (R:=ℂ) (M:=J g) := crossing fun x y => by
    rw [LinearMap.comp_apply,LinearMap.id_apply,cG,portal,portal,tr2,tr2]
  exact LinearMap.congr_fun h x
lemma x2 (x : J Row.x) : cX (cX x)=x := by
  have h : cX ∘ₛₗ cX= LinearMap.id (R:=ℂ) (M:=J Row.x) := crossing fun x y => by
    rw [LinearMap.comp_apply, LinearMap.id_apply,cX,portal,portal,tr2,f2]
  exact LinearMap.congr_fun h x
end YM.GaugeFieldConstruction.Cauchy.Conj
