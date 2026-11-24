import GaugeFieldConstruction.Flake
/-!
# Move in those matrix entries
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Count
open Calibration Calibration.RawBank Floor Cauchy Row Record Function Set Filter Raw Stage.Wide Stage.Cell
open scoped Matrix Matrix.Norms.Frobenius BigOperators Topology
local instance gx : AddCommGroup XX:= @Submodule.addCommGroup ℂ (J Row.x) _ _ _ _

def Once := Raw.v.tensorProd (Labels.unitL Wed)
def Double := (Labels.unitL Axis).tensorProd wedAct

lemma coord_f (v p : Bool) (s : SO) (i : MX):
    rhoX five v p s ((DeckX five).issue (ket (α:=BoxX five) i))=(DeckX five).issue (PX v p |>.rotate s.val (ket i)):= Angles.bOut ..
lemma leadf (s : Signed) (h : signBit s=false) (t:X5): rhoX five false true (signMot s h) (source t)=pay (Once.cost s t) (source (Once.move s t)) := by
  rcases t with ⟨i,j⟩
  unfold source; let u:=j.toBlade.val
  rw [show rhoX _ _ _ _ _=_ from coord_f false true (signMot s h) (i,u)] -- adjust
  have he : (PX false true).rotate s.ortho (ket (i,u))=pay (s.flip i) (ket (s.perm i,u)) := by
    rw [← takes i u]; change Cell.bill (Matrix.kroneckerMap _ (UnitV.active s.ortho) ((Still W).active s.ortho)) _ = _
    rw [cran,merit s h]; rw [show (Still W).active s.ortho=1 from rfl,bills1]; rw [beacon,on_ket]; change times' (pay (s.flip i) (ket (s.perm i))) _=_; cases s.flip i <;> simp
  change (DeckX five).issue ((PX false true).rotate s.ortho (ket (i,u))) = pay ((s.flip i).xor false) _
  rw [he,Bool.xor_false]; cases p:s.flip i <;> simp only [pay_false,pay_true]
  · rfl
  exact map_neg (DeckX five).issue (ket (α:=BoxX five) (s.perm i,u))

lemma allX (s : SO) (p : XX) : rhoX five true true s p=rhoX five true false s (rhoX five false true s p) := by
  obtain ⟨x,rfl⟩:=(DeckX five).supply p
  suffices h : (xCard five true true).rotate s.val x=(xCard five true false).rotate s.val ((xCard five false true).rotate s.val x) by simp only [rhoX]; simp_rw [Angles.bOut,h]
  have he (x : J MX) : (PX true true).rotate s.val x= (PX true false).rotate s.val ((PX false true).rotate s.val x) := by
    have H : rotate (PX true true) s.val=rotate (PX true false) s.val*rotate (PX false true) s.val := crossing fun a b=>by
      rw [Module.End.mul_apply]; change bill (Matrix.kroneckerMap _ (UnitV.active s.val) (Theta.active s.val)) (times' _ _)= bill (Matrix.kroneckerMap _ (1: R4 Axis) (Theta.active s.val)) (bill (Matrix.kroneckerMap _ (UnitV.active s.val) (1:R4 W)) (times' _ _))
      rw [cran,cran,cran,bills1,bills1]
    rw [H, Module.End.mul_apply]
  exact he x
lemma leadG (s : Signed) (h : signBit s=false) (t:X5): rhoX five true false (signMot s h) (source t)=pay (Double.cost s t) (source (Double.move s t)) := by
  rcases t with ⟨k,j⟩
  let i:= s.perm.symm k
  have e :Once.move s (i,j)=(k,j):=Prod.ext (s.perm.apply_symm_apply _) rfl
  have ht:=properX s h (source (i,j)); rw [allX,beam,leadf s h, e] at ht
  change _=pay (false.xor (wedAct.cost s j)) (source (k,wedAct.move s j))
  change rhoX _ _ _ _ (pay ((s.flip i).xor false) (source (k,j)))= pay ((s.flip i).xor (wedAct.cost s j)) (source (s.perm i,wedAct.move s j)) at ht
  rw [show s.perm i=k from s.perm.apply_symm_apply _] at ht
  cases p:s.flip i <;> cases k:wedAct.cost s j <;> simp only [p,k,Bool.true_xor,Bool.false_xor,Bool.not_true,Bool.not_false,pay_true,pay_false] at *
  all_goals first | exact ht| (rw [map_neg] at ht; simpa only [neg_inj, neg_neg] using congr_arg (fun x:XX=> -x) ht)

lemma fee {P : XX→ₗ[ℂ] XX} (A : Labels X5) (s : Signed) (h : ∀ t,P (source t)=pay (A.cost s t) (source (A.move s t))) (x) (t) :
    external (A.move s t) (P x)=pay (A.cost s t) (external t x) := by
  obtain ⟨g,rfl⟩:= paid_sources x
  have he v : external (A.move s t) (P (source v))=pay (A.cost s t) (external t (source v)):= by
    rw [h]; by_cases p:v=t
    · subst v; cases A.cost s t <;> simp only [pay_true,pay_false,map_neg,window,if_true]
    cases A.cost s v <;> cases A.cost s t <;> simp only [pay_true,pay_false,map_neg,window,if_neg (Ne.symm p), if_neg (A.inj s|>.ne (Ne.symm p)),neg_zero]
  induction g using Finsupp.induction_linear with
  | zero=> simp
  | add a b p q=>simp [map_add,p,q,pay_add]
  | single i a=> rw [show Finsupp.single i a=a • ket i from by simp [ket]]; simp only [map_smul,on_ket,he]; cases A.cost s t <;> simp
lemma thick {p : Raw.VS→XX} (H : passes BH p) (t:X5) (s : Signed) i : external (Raw.x5Act.move s t) (p (vsAct.move s i))=pay ((Raw.x5Act.cost s t).xor (vsAct.cost s i)) (external t (p i)) := by
  have h:= fee x5Act s (beam s) (p i) t; rw [H] at h
  cases e: vsAct.cost s i <;> cases p:x5Act.cost s t <;> simp only [e,p,pay_false,pay_true,map_neg,Bool.true_xor,Bool.false_xor,Bool.not_true,Bool.not_false] at *
  all_goals first |exact h| simpa using congr_arg Neg.neg h
lemma rose (v: Axis→XX) (h:rotates (YX five false true) v) (p:Signed) (t:signBit p=false) i:
    rhoX five false true (signMot p t) (v i)=pay (p.flip i) (v (p.perm i)) := survives (rhoX five false true) _ (Angles.pressure _ _ (leavesX five false true) _) h p t i

-- identify axis commutant for active vector. Wedge tag now isolated.
lemma flat (x : Axis→XX) (h:rotates (YX five false true) x) (i j w) : external (i,w) (x j)=if i=j then external ((0:Axis),w) (x 0) else 0 := by
  have he s (p : signBit s=false) (a b : Axis) : external (s.perm a,w) (x (s.perm b))=pay ((s.flip a).xor (s.flip b)) (external (a,w) (x b)) := by
    have hp:= fee Once s (leadf s p) (x b) (a,w); rw [rose x h s p b] at hp
    change external (s.perm a,w) _=pay ((s.flip a).xor false) _ at hp
    cases g:s.flip a <;> cases t:s.flip b <;> simp only [g,t,pay_true,pay_false,map_neg,Bool.true_xor,Bool.false_xor,Bool.not_true,Bool.not_false] at *
    all_goals first | exact hp| simpa using congr_arg Neg.neg hp
  split_ifs with p
  · subst j; have hp := he (sw 0 i) (sw_pos ..) 0 0; simpa only [sw_apply,Bool.xor_self,pay_false] using hp
  obtain ⟨z,hz,g⟩:= third i j
  apply negate; have hp:= he (M i z) (M_pos ..) i j; rw [M_perm, M_perm, M_no _ _ _ p g,M_on _ _ (Ne.symm hz)] at hp; exact hp

/-- all-H relation forces remaining map `Sym`→`wedge` to vanish. -/
lemma skewzero (f : Wed×Raw.Sym→ℂ) (p : ∀ s w i,f (wedAct.move s w, symAct.move s i)=pay ((wedAct.cost s w).xor (symAct.cost s i)) (f (w,i))) (x): f x=0 := by
  -- verified by grouped count
  have h : ∀ w :Wed×Raw.Sym, ∃ s: Signed,decide ((wedAct.tensorProd symAct).move s w=w)=true ∧ ((wedAct.tensorProd symAct).cost s w)=true := by decide +kernel -- may expensive
  obtain ⟨s,u,v⟩:=h x
  have hv := p s x.1 x.2; change f ((wedAct.tensorProd symAct).move s x)=pay ((wedAct.tensorProd symAct).cost s x) _ at hv
  rw [of_decide_eq_true u,v] at hv; exact negate hv
lemma vanish (v:VS→XX) (p : passes BH v) (h:∀ j, rotates (YX five false true) fun i :Axis=> v (i,j)): v=0 := by
  let F (w : Wed × Raw.Sym) := external (0,w.1) (v (0,w.2))
  have he (a w i j) : external (a,w) (v (i,j))=if a=i then F (w,j) else 0 := flat _ (h j) a i w
  have hp (s: Signed) (w:Wed) (i : Raw.Sym) : F (wedAct.move s w, symAct.move s i)=pay ((wedAct.cost s w).xor (symAct.cost s i)) (F (w,i)) := by
    have ht:=thick p (0,w) s (0,i)
    change external (s.perm 0,wedAct.move s w) (v (s.perm 0,symAct.move s i))=pay (((s.flip 0).xor (wedAct.cost s w)).xor ((s.flip 0).xor (symAct.cost s i))) (F (w,i)) at ht
    rw [he,if_pos rfl] at ht; cases e:s.flip 0 <;> cases v:wedAct.cost s w <;> cases q:symAct.cost s i <;> simp only [e,v,q] at * <;> exact ht
  ext1 ⟨i,j⟩; apply paid_ext; rintro ⟨a,b⟩; rw [he,skewzero F hp]; split_ifs <;> rfl
end YM.GaugeFieldConstruction.Stage.Count
