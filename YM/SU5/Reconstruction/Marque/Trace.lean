import YM.SU5.Reconstruction.Marque.Studio
import Mathlib.Analysis.Complex.Polynomial.Basic
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Matrix Real Complex
open scoped Matrix MatrixGroups Topology Classical
noncomputable def Sugar : ℂˣ := Units.mk0 I I_ne_zero
@[simp] lemma sugar_val : (Sugar:ℂ)=I:=rfl
lemma I_inv:I⁻¹= -I:=inv_eq_of_mul_eq_one_left (by simp)
noncomputable def Basin:=Pole Sugar
lemma hush(k:ℂ)(p:k*k = -1): k=I∨ k= -I := sq_eq_sq_iff_eq_or_eq_neg.mp (by rw[pow_two,p, I_sq])
noncomputable def cents : Set Two:={1,bezel}
variable (g u:Two)
def lip := A g+D g
@[simp] lemma lip_head(t:ℂ) : lip (Head t)=2:=by simp [Head,lip]; norm_num
@[simp] lemma lip_tail(t:ℂ) : lip (Tail t)=2:=by simp [Tail,lip]; norm_num
lemma lip_comm: lip (g*u)=lip (u*g):=by simp [lip]; ring
@[simp] lemma lip_bezel: lip (bezel*g)= -(lip g):=by simp [lip,bezel,add_comm]
@[simp] lemma lip_invariant: lip (rehome u g)=lip g:=by rw [rehome,lip_comm,←mul_assoc]; simp
abbrev Blank:=lip g=0
lemma revers (h: Blank g): g⁻¹=bezel*g:= by change A g+D g=0 at h; apply tone <;> simp [bezel] <;> grind
lemma reverse2 (h: Blank g): g*g=bezel:= by nth_rw 1 [show g=bezel*g⁻¹ by rw [revers g h,←mul_assoc,bezel_sq,one_mul]]; group
@[simp] lemma basin_price:Blank Basin:=by simp [Blank,lip,Basin,Pole]
lemma topCover : ∃ h:Two,C (rehome h g)=0:=by
 by_cases e:B g=0
 · exact ⟨turn,by simp [rehome,turn,e]⟩
 -- C becomes (A*s+C)-s(B*s+D); choose root.
 obtain ⟨d,hd⟩:= IsAlgClosed.exists_pow_nat_eq ((A g-D g)^2+4*B g*C g) Nat.zero_lt_two
 let v:=(A g-D g+d)/(2*B g)
 refine ⟨Tail v,?_⟩; simp [rehome,Tail,v]; field_simp; linear_combination -hd -- tune factors
noncomputable def Wrap (g:Two) : Set Two:={g,bezel*g}
lemma lipSign (p:Blank g) {y}(h:y∈Wrap g) : Blank y:= by rcases (Set.mem_insert_iff.mp h) with h|t; exact h ▸ p; rw [Set.mem_singleton_iff] at t; simp only [Blank,t,lip_bezel,p,neg_zero]
lemma wrap_case{y} (p:y∈Wrap g):y=g∨ y=bezel*g:=p -- defeq?
@[simp] lemma wrap_bezel : Wrap (bezel*g)=Wrap g:=by unfold Wrap; rw [←mul_assoc,bezel_sq,one_mul, Set.pair_comm]
lemma wrap_acts {x:Two}(p:x∈ Wrap g) : rehome u x∈Wrap (rehome u g):= by rcases wrap_case g p with h|h; exact Or.inl (h ▸ rfl); exact Or.inr (show rehome u x=bezel * rehome u g by rw [h,rehome_mul,rehome_bezel])
-- classification of upper
lemma upper_pole (p:C g=0) (q:B g=0) : ∃ u, g=Pole u:=by
 have hx:A g*D g=1:= by simpa only [p,mul_zero,sub_zero] using det g
 have he: A g≠0:= left_ne_zero_of_mul_eq_one hx
 refine ⟨Units.mk0 _ he,tone _ _ rfl ?_ ?_ ?_⟩; exacts [q,p,(inv_eq_of_mul_eq_one_right hx).symm]
lemma drawing (p:C g=0) : (∃ h u, rehome h g=Pole u) ∨ ∃ q,g∈Wrap (Head q):= by
 have hx:A g*D g=1:= by simpa only [p,mul_zero,sub_zero] using det g
 by_cases e:A g=D g
 · right; obtain k|k:=mul_self_eq_one_iff.mp (show A g*A g=1 by nth_rw 2 [e]; exact hx)
   · exact ⟨B g,Or.inl (show g=Head (B g) from tone _ _ (by simp [Head,k]) rfl (by simp [Head,p]) (by simp [Head,←e,k]))⟩
   refine ⟨-B g, Or.inr (show g= _ from tone _ _ ?_ ?_ ?_ ?_)⟩ <;> simp [Head,bezel,p,←e,k]
 left; let h:= Head (B g/(A g-D g)); refine ⟨h,upper_pole _ ?_ ?_⟩; all_goals simp [h,Head,rehome,p];
 field_simp [e]; ring
lemma canonical : ∃ h, (∃ u, rehome h g=Pole u) ∨ (∃ q, rehome h g ∈ Wrap (Head q)):= by
 obtain ⟨x,v⟩:= topCover g; obtain ⟨t,s,b⟩|a:= drawing _ v; exacts [⟨t*x,Or.inl ⟨s,by rw [rehome_comp,b]⟩⟩,⟨x,Or.inr a⟩]
-- basin conjugator explicit
lemma blankChart(p:Blank g): ∃ h, rehome h Basin=g:= by
 obtain ⟨x,⟨t,p1⟩|⟨q,p1⟩⟩:= canonical g<;> have hp: lip (rehome x g)=0:= by rw [lip_invariant]; exact p
 · rw [p1] at hp; have ht:(t:ℂ)*(t:ℂ)=-1:= by
      simp [Pole,lip] at hp; linear_combination (t:ℂ)*hp-(mul_inv_cancel₀ (Units.ne_zero t))
   rcases hush _ ht with e|e
   · use x⁻¹; rw [← show Pole t=Basin from (by rw [Units.ext (show (t:ℂ)=(Sugar:ℂ) from e)]; rfl), ← p1,rehome_back]
   use x⁻¹ * turn; rw [rehome_comp,show rehome turn Basin=Pole t from (by apply tone <;> simp [rehome,Basin,Pole,turn,e]),← p1,rehome_back]
 rcases wrap_case _ p1 with b|b <;> simp [b, lip,Head,bezel] at hp -- issue lip simp before
lemma Head_comm (t w:ℂ) : Commute (Head t) (Head w):=by rw [commute_iff_eq]; simp_rw [Head_add]; rw [add_comm]
lemma Pole_comm (u v:ℂˣ):Commute (Pole u) (Pole v):=by rw[commute_iff_eq]; simp_rw[Pole_pow]; rw [mul_comm]
lemma sameBasin (e:rehome g Basin=Basin):∃ u,g=Pole u:= by
 have p : g*Basin=Basin*g:= mul_right_cancel (b:=g⁻¹) (by rw [mul_assoc Basin, mul_inv_cancel,mul_one]; exact e)
 have hb:= congrArg B p; have hc:=congrArg C p; simp [Basin,Pole] at hb hc
 apply upper_pole
 · by_contra e; have h:I= -I:= mul_left_cancel₀ e (by linear_combination hc); exact (neg_ne_self.mpr I_ne_zero) h.symm
 by_contra e; have h:I= -I:=mul_left_cancel₀ e (by linear_combination -hb); exact (neg_ne_self.mpr I_ne_zero) h.symm
lemma oppositeBasin (e:rehome g Basin=bezel*Basin): ∃ u,g= turn*Pole u:= by
 obtain ⟨s,p⟩:= sameBasin (turn⁻¹ * g) (by rw [rehome_comp, e,show bezel*Basin=rehome turn Basin from (by apply tone <;> simp [rehome,turn,Basin,Pole,bezel]), rehome_back]); exact ⟨s,by rw [← p]; group⟩
end YM.Marque
