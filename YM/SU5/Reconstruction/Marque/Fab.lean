import YM.SU5.Reconstruction.Marque.Trace
set_option autoImplicit false
noncomputable section
namespace YM.Marque
open Function Set Filter Matrix Real Complex
open scoped Matrix MatrixGroups Topology Classical
variable (g h:Two)(t:ℂˣ)
-- trace-reverter as first
abbrev Reverse:= Blank h ∧ Blank (g*h)
lemma signReverse (p: Reverse g h) {s:Two}(e:s∈Wrap g): Reverse s h:= by
 refine ⟨p.1,?_⟩; rcases wrap_case g e with h|h; exact h ▸ p.2; apply lipSign _ p.2; exact Or.inr (by rw [h,mul_assoc]; rfl)
lemma pairUp (p: Reverse g h): Blank (h⁻¹*g):= by simp only [Blank, revers h p.1,mul_assoc,lip_bezel,neg_eq_zero]; exact (lip_comm ..).trans p.2
lemma reverseOf (p: Blank g)(q:Blank h): Reverse (g*h) g:= ⟨p,by
 unfold Blank; rw [lip_comm (g*h),← mul_assoc,reverse2 g p]; simp [q]⟩
lemma shifted (s y:Two)(p:Reverse g s): Reverse (rehome y g) (rehome y s):= ⟨by simp only [Blank,lip_invariant, p.1],by simp only [Blank,← rehome_mul,lip_invariant,p.2]⟩
lemma findReverse : ∃ s,Reverse g s:= by
 obtain ⟨x,⟨t,e⟩|⟨q,v⟩⟩:= canonical g
 · refine ⟨rehome x⁻¹ turn,?_⟩; nth_rewrite 1 [← rehome_back x g]; apply shifted; rw [e]; simp [Reverse,Blank,lip,turn,Pole]
 refine ⟨rehome x⁻¹ Basin,?_⟩; nth_rewrite 1 [← rehome_back x g]; apply shifted; apply signReverse (Head q) Basin ?_ v; refine ⟨basin_price,?_⟩; simp [Blank,lip,Head,Basin,Pole]
variable {q:ℂ}
lemma atPoleSeries (e:(t:ℂ)≠(t:ℂ)⁻¹) (p: Reverse (Pole t) g): A g=0∧D g=0∧ B g≠0:= by
 rcases p with ⟨x,y⟩; simp [Blank,lip,Pole] at x y; have hv: A g=0:= mul_left_cancel₀ (sub_ne_zero.mpr e) (show (_-_:ℂ)*A g=(_-_)*0 by linear_combination y-(t:ℂ)⁻¹*x)
 rw [hv,zero_add] at x; refine ⟨hv,x,?_⟩; intro hd; have hy:=det g; simp [hv,x,hd] at hy
lemma sub_pole (e:(t:ℂ)≠(t:ℂ)⁻¹)(p:Reverse (Pole t) g)(q:Reverse (Pole t) h):∃ u:ℂˣ,rehome (Pole u) g=h:= by
 obtain ⟨a,b,c⟩:=atPoleSeries g t e p; obtain ⟨x,y,z⟩:=atPoleSeries h t e q; obtain ⟨t0,ht⟩:=IsAlgClosed.exists_pow_nat_eq (B h/B g) Nat.zero_lt_two; have p0:t0≠0:= fun w=> by simp only [w,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at ht; exact (div_ne_zero z c) ht.symm
 let u:= Units.mk0 _ p0; have ha:A (rehome (Pole u) g)=0:= by simp [rehome,Pole,a]
 have hb:D (rehome (Pole u) g)=0:= by simp [rehome,Pole,b] -- ; scoping
 have hx: B (rehome (Pole u) g)=B h:= by simp [rehome, Pole,u]; linear_combination ((eq_div_iff c).mp ht) -- denominator ring?
 refine ⟨u,tone _ _ (ha.trans x.symm) hx ?_ (hb.trans y.symm)⟩; have ht':= det (rehome (Pole u) g); rw [ha,hx,hb] at ht'; apply mul_left_cancel₀ z; have he:= det h; rw [x,y] at he; linear_combination he -ht'
lemma poleDead(p:(t:ℂ)=(t:ℂ)⁻¹): Pole t ∈ Wrap 1:=by
 obtain h|h:= mul_self_eq_one_iff.mp (show (t:ℂ)*(t:ℂ)=1 by nth_rw 2 [p]; simp);
 · exact Or.inl (show Pole t=1 by apply tone <;> simp [h,Pole])
 exact Or.inr (show Pole t= _ by apply tone <;> simp [h,Pole,bezel])
-- unipot
lemma atHeadSeries (p:Reverse (Head q) g)(e:q≠0): C g=0∧ D g= -A g ∧ (A g=I∨ A g= -I):= by
 rcases p with ⟨x,y⟩; simp [Blank,lip,Head] at x y; have hv: C g=0:= mul_left_cancel₀ e (show q*C g=q*0 by linear_combination y-x); have ha:D g= -A g:= by grind
 refine ⟨hv,ha,hush _ ?_⟩; have h:=det g; rw [hv,ha] at h; linear_combination -h
lemma sub_tuber {r:Two}(p: Reverse r g)(x:Reverse r h)(w:r∈Wrap (Head q))(e:q≠0):∃ i:ℂ,h∈Wrap (rehome (Head i) g):=by
 have v: Head q∈ Wrap r:= by rcases wrap_case _ w with w|w; exact Or.inl w.symm; rw [w,wrap_bezel]; exact Or.inl rfl
 -- normalize equal/opposite
 have other (g h:Two)(k:A g=A h)(p: Reverse r g)(x:Reverse r h):∃ i,rehome (Head i) g=h:= by
    obtain ⟨a,b,c⟩:= atHeadSeries g (signReverse r g p v) e; obtain ⟨d,f,z⟩:= atHeadSeries h (signReverse r h x v) e
    have hn:A h≠0:= z.elim (fun h=>h ▸ I_ne_zero) (fun h=>h ▸ neg_ne_zero.mpr I_ne_zero)
    refine ⟨(B g-B h)/(2*A h),tone _ _ ?_ ?_ ?_ ?_⟩ <;> simp [Head,rehome,b,a,d,f,k]; field_simp; ring
 obtain h0|h0 : A g=A h ∨ A g= -A h:= by
    have ht:= (atHeadSeries h (signReverse r h x v) e).2.2; have hp:= (atHeadSeries g (signReverse r g p v) e).2.2; grind
 · obtain ⟨i,r₁⟩:= other _ _ h0 p x; exact ⟨i,Or.inl r₁.symm⟩
 obtain ⟨i,r₁⟩:=other g (bezel*h) (by simp [h0,bezel]) p ⟨by simp only [Blank,lip_bezel,x.1,neg_zero],by unfold Blank; rw [←mul_assoc,←bezel_stays r, mul_assoc,lip_bezel,x.2,neg_zero]⟩
 use i; rw [r₁,wrap_bezel]; exact Or.inl rfl
-- product with head after colour
lemma goodHead(t:ℂ)(p:C g≠0∨ A g=D g):∃ s, Reverse g s∧Reverse (Head t) s:=by
 let J(t:ℂ):= pin I t 0 (-I) (by simp)
 have h(i:ℂ): Reverse (Head t) (J i):= by simp [Reverse,J,Blank,Head,lip];
 rcases p with p|p
 · refine ⟨J ((D g-A g)*I/C g),⟨(h _).1,?_⟩,h _⟩; simp [Blank,J,lip]; field_simp; ring -- simp
 refine ⟨J 0, ⟨(h _).1,?_⟩,h _⟩; simp [Blank,J,lip,p]
-- improve bad
lemma chooseHead (t:ℂ)(b:C g=0)(q:A g≠D g): ∃ w:Two, rehome w (Head t)= Head t ∧ C (rehome w g)=0∧ B (rehome w g)≠0∧B (rehome w g*Head t)≠0:=by
 have hw:D g - A g≠0:= sub_ne_zero.mpr q.symm
 let p(s:ℂ):=rehome (Head s) g; have hi (s:ℂ): B (p s)=B g+s*(D g-A g):= by simp [rehome,p,Head,b]; ring
 obtain ⟨w,hk⟩:= ((Set.finite_singleton (-(B g+A g*t)/(D g-A g))).insert (-(B g)/(D g-A g))).exists_notMem -- tune
 simp at hk; refine ⟨Head w,by unfold rehome; rw [(Head_comm _ _).eq];group,by simp [rehome,Head,b], ?_,?_⟩
 · rw [show B _=B (p w) from rfl,hi]; intro u; apply hk.1; apply (eq_div_iff hw).mpr; linear_combination u
 rw [B_mul, show B (rehome _ _)= B (p w) from rfl,hi]; intro u; apply hk.2; apply (eq_div_iff hw).mpr; simp [Head,rehome,b] at u; linear_combination u
lemma multiply_help(p:C g=0) : C ((Tail 1)*g)≠0:=by simp[p,Tail]; apply left_ne_zero_of_mul_eq_one (b:=D g); simpa [p] using det g
end YM.Marque
