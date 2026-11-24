import GaugeFieldConstruction.Hall
/-!
# Adjoint multiplicity on the sheet
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Matter
open CF Function Set Matrix Finset
open scoped Topology Matrix Matrix.Norms.Frobenius Kronecker BigOperators

def high := entry 0 4 (by decide)
lemma fee (i : F) : lie (tall i) high=((note i 0:ℂ)-(note i 4:ℂ)) • high := by
  apply Subtype.ext
  ext a b; by_cases e:a=0 <;> by_cases m:b=4 <;>
    simp [lie,tall,high,entry,Matrix.single_apply,e,m,Ne.symm] -- tweak
-- special pattern
abbrev Mid := Fin 3
def axis (i : Mid) : F := Fin.castAdd 1 i.succ
def up (i : Mid) : Sheet := Sum.inl (⟨(0,axis i),by
                                                     have h: ∀ i : Mid,(0:F)<axis i:=by decide
                                                     exact h i⟩:Ten)
def dn (i : Mid) : Sheet := Sum.inl (⟨(axis i,4),by
                                                     have h: ∀ i:Mid,axis i < 4:=by decide
                                                     exact h i⟩:Ten)
def e₀ : Sheet := Sum.inr 0
def e₄ : Sheet := Sum.inr 4

def band (a b : Sheet) := (a=e₄∧b=e₀) ∨ ∃ i:Mid, a=up i ∧ b=dn i
set_option synthInstance.maxSize 5000 in
lemma rota : ∀ (i j: Sheet), (∀ k, weight k i-weight k j=note k 0-note k 4) →
    (i=e₄ ∧ j=e₀) ∨ (∃ s : Mid,i=up s ∧ j=dn s) := by decide +kernel
lemma up_inj : Function.Injective up := by intro i j; fin_cases i <;> fin_cases j <;> decide
lemma dn_inj : Function.Injective dn := by intro i j; fin_cases i <;> fin_cases j <;> decide

lemma enabled (A : sl →ₗ[ℂ] U) (p : Wcov A) (x y : Sheet) (h : A high x y ≠0) : band x y := by
  apply rota
  intro k
  have hp := p (tall k) high
  rw [fee,map_smul, tilted] at hp
  have he := Matrix.ext_iff.mpr hp x y
  rw [Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal] at he
  have hr := mul_right_cancel₀ h (show ((weight k x:ℂ)-weight k y)* A high x y=
      ((note k 0:ℂ)-note k 4)* A high x y from by rw [he,sub_mul]; ring)
  exact_mod_cast hr

private lemma value : ∀ i j : Mid,i≠j → intEntry (axis i) (axis j) (up i) (up j)=1 ∧
    intEntry (axis i) (axis j) (dn i) (dn j)=1 := by decide
private lemma highcom (i j : Mid) (p : i≠j) (s : axis i≠axis j) :
    lie (entry _ _ s) high=0 := by
  apply Subtype.ext
  have h : axis i ≠4:=by fin_cases i <;> decide
  have ht : axis j≠0:=by fin_cases j <;> decide
  simp [lie,entry,high,h,ht,Ne.symm]
lemma meditate (A : sl →ₗ[ℂ] U) (p : Wcov A) (i j : Mid) :
    A high (up i) (dn i)=A high (up j) (dn j) := by
  by_cases e:i=j
  · rw [e]
  let a:=axis i; let b:=axis j
  have eq : a≠b := by
    have h:∀ i j:Mid,i≠j→axis i≠axis j:=by decide
    exact h i j e
  let E:=entry _ _ eq
  have he:=p E high
  rw [show lie E high=0 from highcom i j e eq,map_zero] at he
  have hu:=Matrix.ext_iff.mpr (sub_eq_zero.mp he.symm) (up i) (dn j)
  let V:=repX E.val
  have hv₁ : V (up i) (up j)=1 := by
    unfold V E; rw [actualEntry,(value i j e).1]; simp
  have hv₂: V (dn i) (dn j)=1 := by
    unfold V E; rw [actualEntry,(value i j e).2]; simp
  have hh : (V*A high) (up i) (dn j)=A high (up j) (dn j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (up j),hv₁,one_mul]; swap; simp
    intro x _ ht; by_cases p' : A high x (dn j)=0; rw [p',mul_zero]
    obtain h|⟨t,h,h'⟩:=enabled A p _ _ p'
    · exact nomatch h.2
    exact (ht (dn_inj h' ▸ h)).elim
  have hw : (A high*V) (up i) (dn j)=A high (up i) (dn i) := by
    rw [Matrix.mul_apply,Finset.sum_eq_single (dn i),hv₂,mul_one]; swap; simp
    intro x _ ht; by_cases p' : A high (up i) x=0; rw [p',zero_mul]
    obtain h|⟨t,h,h'⟩:=enabled A p _ _ p'
    · exact nomatch h.1
    exact (ht (up_inj h ▸ h')).elim
  exact hw.symm.trans (hu.symm.trans hh)

/-- High root alone generates sl. -/
private lemma yaw (a b c : F) (h : a≠b) (t : b≠c) (j : a≠c) :
    lie (entry _ _ h) (entry _ _ t)=entry _ _ j ∧
    lie (entry _ _ t) (entry _ _ h) = -entry _ _ j := by
  constructor <;> apply Subtype.ext <;> simp [lie,entry,j,Ne.symm]

lemma leader (A : sl→ₗ[ℂ]U) (p : Wcov A) (k : A high=0) : A=0 := by
  have v (x y : sl) (p' : A y=0) : A (lie x y)=0 := by rw [p x y,p']; simp
  have hm (i : F) (h : i≠4) : A (entry i 4 h)=0 := by
    by_cases t:i=0
    · subst i; exact k
    rw [← (yaw i 0 4 t (by decide) h).1]; exact v _ _ k
  have ht (j e : F) (h : j≠4) (s : j≠e) : A (entry j e s)=0 := by
    by_cases H:e=4
    · subst e; exact hm _ h
    rw [← neg_eq_zero,← map_neg,← (yaw j 4 e h (Ne.symm H) s).2]; exact v _ _ (hm _ h)
  have hr (i j : F) (h : i≠j) : A (entry i j h)=0 := by
    by_cases w : i=4
    · subst i
      obtain ⟨i,t,s⟩ : ∃ i:F,i≠4 ∧ i≠j:=by
        have hh:∀ j:F,∃ i:F,i≠4 ∧ i≠j:=by decide
        exact hh j
      rw [← (yaw 4 i j t.symm s h).1]; exact v _ _ (ht _ _ t s)
    exact ht _ _ w h
  have hk (i : F) (h : i≠0) :
      (lie (entry i 0 h) (entry 0 i h.symm)).val=
      Matrix.single i i 1-Matrix.single 0 0 1 := by simp [lie,entry]
  ext1 y
  let D (i j : F) := if h:i=j then if e:i=0 then (0:sl)
                                      else lie (entry i 0 e) (entry 0 i (Ne.symm e))
                     else entry i j h
  have hv (i j : F): A (D i j)=0 := by
    unfold D; split_ifs
    · simp
    · exact v _ _ (hr ..)
    exact hr ..
  have he (i j:F) : (D i j).val=Matrix.single i j 1 - (if i=j then Matrix.single 0 0 1 else (0:V)) := by
    by_cases h:i=j
    · subst i; by_cases s:j=0
      · subst j; simp [D]
      simp only [D,dif_pos rfl,dif_neg s,if_pos rfl]; exact hk _ _
    simp only [D,dif_neg h, if_neg h,sub_zero,entry]
  have hy : y=∑ i:F,∑ j:F, y.val i j • D i j := by
    apply Subtype.ext
    ext i j
    have p : ∑ i:F,y.val i i=0:=y.property
    simp only [AddSubmonoidClass.coe_finsetSum,Submodule.coe_smul,he,smul_sub,smul_ite,sum_sub_distrib,
      Matrix.sum_apply,Matrix.sub_apply,Matrix.smul_apply,smul_zero,Matrix.zero_apply,
      Matrix.single_apply]
    simp_rw [Matrix.ite_apply, Matrix.smul_apply, Matrix.single_apply,Matrix.zero_apply,ite_and]
    by_cases e : (0:F)=i ∧ (0:F)=j <;> simp_all
  change A y=0
  rw [hy,map_sum]; simp only [map_sum,map_smul,hv,smul_zero, sum_const_zero]

/-- Copy generator weighting. -/
def two (a b:ℂ) := Join.both (a • (1:Op Ten)) (b • (1:Op F))

def coat (a b:ℂ) : sl →ₗ[ℂ] U where
  toFun u := two a b*repX u.val
  map_add' _ _ := by rw [Submodule.coe_add,rep_add,mul_add]
  map_smul' _ _:= by rw [Submodule.coe_smul,rep_s]; simp
/-- Map prices are complexified but on physical colors. -/
def tint (a b:ℂ) : C →ₗ[ℝ] U where
  toFun u:=coat a b (core u)
  map_add' u v:=by rw [(hues u v 0).1,map_add]
  map_smul' r c:=by rw [(hues c c r).2,map_smul]; simp [Complex.coe_smul]
lemma tints (a b : ℂ) : action (tint a b) := by
  intro u x; change blockRep u*(two a b*repX (H x))= _
  change _=two a b*repX (H (_))*blockRep u
  rw [← mul_assoc,(pure_singular (two a b)).mpr ⟨a,b,rfl⟩ u,mul_assoc,direction,mul_assoc]
lemma risen (a b:ℂ) : extend (tint a b)=coat a b := detects (fun i=> base _ _)

private lemma contrib (a b:ℂ) :
    (∀ t:Mid,coat a b high (up t) (dn t)= -a) ∧ coat a b high e₄ e₀= -b := by
  have he : intEntry 0 4 e₄ e₀= -1 := by decide
  have ht :∀ i,intEntry 0 4 (up i) (dn i) = -1 := by decide
  have hv (i) : repX high.val (up i) (dn i)= -1 := by rw [high,actualEntry,ht]; simp
  have hy : repX high.val e₄ e₀= -1 := by rw [high,actualEntry,he]; simp
  have h₀ : two a b = diagonal (fun s => Sum.elim (fun _=>a) (fun _=>b) s) := by
    ext i j; cases i with
            | inl i' => cases j with
                | inl j => by_cases t:i'=j <;> simp [two,Join.both,t,Matrix.one_apply]
                | inr j => simp [two,Join.both]
            | inr i => cases j with
                | inl j => simp [two,Join.both]
                | inr j => by_cases t:i=j <;> simp [two,Join.both,t,Matrix.one_apply]
  constructor
  · intro t; change (two a b*_) _ _= _; rw [h₀,Matrix.diagonal_mul,hv]; simp [up]
  change (two a b*_) _ _= _; rw [h₀,Matrix.diagonal_mul,hy]; simp [e₄]

theorem tinted (V : C →ₗ[ℝ] U) : action V ↔ ∃ a b,V=tint a b := by
  constructor
  · intro h
    let W := extend V; let a := -W high (up 0) (dn 0); let b:= -W high e₄ e₀
    have H : Wcov W := earned V h
    let D := W-coat a b
    have h': Wcov (coat a b) := by rw [←risen]; exact earned _ (tints a b)
    have ht : Wcov D := fun z y=>by simp only [D, LinearMap.sub_apply,H z y,h' z y,mul_sub,sub_mul]; abel
    have hv : W=coat a b := sub_eq_zero.mp <| leader D ht <| by
      ext x y
      by_cases v : band x y
      · obtain ⟨rfl,rfl⟩|⟨t,rfl,rfl⟩:=v
        · change _-_=(0:ℂ); rw [(contrib ..).2]; simp [b]
        unfold D; rw [LinearMap.sub_apply,Matrix.sub_apply,(contrib ..).1,meditate _ H t 0]; simp [a]
      exact not_ne_iff.mp (fun u=> v (enabled _ ht _ _ u))
    refine ⟨a,b,?_⟩; ext1 i; rw [← base V,show extend V=coat a b from hv]; rfl
  rintro ⟨a,b,rfl⟩; exact tints _ _
theorem tint_faith {a b c d : ℂ} (h : tint a b=tint c d) : a=c ∧ b=d := by
  have hp : coat a b=coat c d := by rw [←risen,←risen,h]
  have hm := congr_arg (fun i : sl→ₗ[ℂ] U => i high (up 0) (dn 0)) hp
  have he := congr_arg (fun i : sl→ₗ[ℂ] U => i high e₄ e₀) hp
  simp only [(contrib ..).1,(contrib ..).2] at hm he -- likely fail
  exact ⟨neg_inj.mp hm,neg_inj.mp he⟩
end YM.GaugeFieldConstruction.Matter
