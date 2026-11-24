import YM.CF.Buffered.Audition
/-! Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad.Melody
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open Lead (cash)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{F K T D U:Op (Single N)} {d:Candle}
def noteL (A:Melody B R)(V:Pane N)(b:Bool)(L:Op (Single N)) := (if b then A.first.lasting V L*A.last.lasting V L else A.first.lasting V L)- compare b • 1 -- tune
lemma dressed (U':Fields N)(p:Clad F K T D U)(b:Bool)(A:Melody B R): Dress (laneP K T U) (A.goal b U') (noteL A U'.1 b (laneP K T U)):=by unfold goal noteL; split; exact ((A.first.dress_m _ p).mul (A.last.dress_m _ p)).sub ((Dress.one _).l _); exact (A.first.dress_m _ p).sub ((Dress.one _).l _)
lemma gol_v (U':Fields N)(A:Melody B R)(b:Bool) : noteL A U'.1 b 0=A.goal b U':=by unfold noteL goal; rw [Lead.lasting_z, Lead.lasting_z]; cases b <;> rfl
lemma vocal₁ (V:Clad F (tickA N) T D K)(A: Lead R) : let u:= laneP (tickA N) T K; A.lasting (Kea.tax d) u (Tset N) (Tset N)=cash A.wave *∑ i∈five,A.note A u d i i :=by
 intro u; rw [Lead.open_mic,Matrix.smul_apply, Matrix.sum_apply]; simp_rw [show ∀ i:Slot,A.vocal d u i (Tset N) (Tset N)=_ from fun i=> A.solo_mic d V i]; rfl
lemma vocal₂ (V:Clad F (tickA N) T D K)(A W: Lead R)(t: W.wave=A.wave) : let u:= laneP (tickA N) T K; (A.lasting (Kea.tax d) u* W.lasting (Kea.tax d) u) (Tset N) (Tset N)=cash A.wave^2 *(∑ i∈five,∑ j∈five,(A.note A u d i i*W.note W u d j j-A.note W u d i j* W.note A u d j i)) :=by
 intro u; rw [Lead.open_mic,Lead.open_mic,t,Matrix.smul_mul,Matrix.mul_smul,smul_smul,sum_mul]; simp_rw [mul_sum,Matrix.smul_apply,Matrix.sum_apply,show ∀ i j:Slot,(A.vocal d u i*W.vocal d u j) (Tset N) (Tset N)=_ from fun i j=> A.reserve d W V i j]; rw [sq]; simp_rw [smul_eq_mul,mul_sum]; rfl
private lemma five_card : five.card=5:= (colors_card _).trans rfl

section surge
open YM.Stationary (Gaia)
variable {S:ℕ→ℕ}{Y:ℕ→Side}{j:ℕ}{ι:Fin 2}
variable {M:ℕ→ Jill.Male}{d₀:ℕ→ Candle}{F:∀ i,Slide (Y i) (d₀ i)} {L:∀ i,Stag (Y i)→ Peb}
variable (h:Yard Y (fun i=>(S i:ℝ))){b c:Bool} {r C:ℝ}
include h in
private lemma units_const : Tendsto (fun i:ℕ=> (((S i:ℕ):ℤ):ℝ)/(S i:ℝ)) atTop (𝓝 1) := tendsto_const_nhds.congr (fun i=>by have hp:0<(S i:ℝ):=h.pos i; rw [Int.cast_natCast,div_self hp.ne'])
include h in
private lemma gap_exact : Tendsto (fun i:ℕ=> (gap B (S i):ℝ)/(S i:ℝ)) atTop (𝓝 3) := by
 let v (i:ℕ):ℝ:=gap B (S i); let x(i:ℕ):ℝ:=S i; let n:ℕ:=2*B.val; have hp:n>0:=by unfold n; exact Nat.mul_pos (by norm_num) B.property
 have hn : (n:ℝ)=2*(B.val:ℝ):=by unfold n; push_cast; rfl
 have he(i:ℕ): 0≤(S i%(2*B.val):ℕ):= Nat.zero_le _
 have ht(i:ℕ): -2*(n:ℝ) ≤ v i-3*x i ∧ v i-3*x i≤3:=by
    let b (i:ℕ):ℕ:=S i%n
    have he: x i=(↑(b i):ℝ)+(n:ℝ)*↑(S i/n):=by unfold x b; exact_mod_cast (Nat.mod_add_div (S i) n).symm
    have hz:(b i:ℝ)<(n:ℝ):=by exact_mod_cast Nat.mod_lt (S i) hp
    have hg:0≤(b i:ℝ):=by positivity
    change _ ≤ (((4*(B.val:ℤ)*(S i/n:ℕ)+S i+3:ℤ):ℝ))-3*x i ∧ (((4*(B.val:ℤ)*(S i/n:ℕ)+S i+3:ℤ):ℝ))-3*x i≤3 -- need cast syntax
    push_cast; try rw [← Int.natCast_div,Int.cast_natCast]; unfold x at *; rw [hn] at he hz ⊢; constructor <;> linarith
 change Tendsto (fun i:ℕ=> v i /x i) _ _
 rw [tendsto_iff_norm_sub_tendsto_zero]; apply squeeze_zero (fun _=>norm_nonneg _) _ (h.thinner (2*n+3)); intro i; have he: 0<x i:=h.pos i
 change ‖v i / x i-_‖≤(2*n+3)/x i; rw [Real.norm_eq_abs, show v i/x i-3=(v i-3*x i)/x i from by field_simp, abs_div,abs_of_nonneg he.le,div_le_div_iff_of_pos_right he]
 rw [abs_le]; have hg:= ht i; constructor <;> nlinarith [show 0≤ (n:ℝ) from by positivity,hg.2,hg.1]
private lemma sailed (f:Bool)(v:ℕ→ℤ){x:ℝ}(p: Tendsto (fun i=>(v i:ℝ)/(S i:ℝ)) atTop (𝓝 x)): Tendsto (fun i:ℕ=> riseX (S i) (direction (sail f (v i)))) atTop (𝓝 (corner (phaseF f*x))) := by
 have ht(i:ℕ)(K:ℤ) : riseX (S i) (direction (sail f K)) = corner (phaseF f * ((K:ℝ)/ (S i:ℝ))) := by
   ext a; by_cases t:a=3; all_goals cases f <;> simp [phaseF,sail,corner,riseX,direction,t,moor, neg_div]
 simp_rw [ht]; apply (show Continuous corner from ?_).continuousAt.tendsto.comp (p.const_mul _)
 refine (PiLp.continuous_toLp 2 _).comp (f:=fun (x:ℝ) => Pi.single (M:=fun _:Axis => ℝ) 3 x) (continuous_pi ?_); intro i; by_cases g:i=(3:Axis)
 · subst i; simp only [Pi.single_eq_same]; exact continuous_id
 simp [g]; exact continuous_const
variable (H:1 ≤ j) (e:0 < r)(g:0<C)(f:∀ i x, FormU ((F i).u x) j (M i) r C (trackF (F i) (L i) x))
include H e g h f
lemma note_t (A W:∀ i, Lead (S i))(p q:Slot)(x:ℝ)(l:x≠0)(ha:∀ i,(A i).slot=ι)(hw:∀ i,(W i).slot=ι) (v:Tendsto (fun i=>riseX (S i) ((A i).death-(W i).birth)) atTop (𝓝 (corner x))) : Tendsto (fun i=>(A i).note (W i) (Dofu (Y i) (L i)) (d₀ i) p q) atTop (𝓝 (if p=q then Window.kernel x else 0)):=by
 let a:Wing:= ⟨dnSpin ι,p,1⟩; let b:Wing:=⟨upSpin ι,q,1⟩
 have ht(i:ℕ): ((A i).endTag p).2=a:=by unfold Lead.endTag; rw [ha] -- tune
 have hv(i:ℕ): ((W i).startTag q).2=b:=by unfold Lead.startTag; rw [hw]
 have hi:=Emu.tally F M L (fun _=>0) h e g (fun x=>Eventually.of_forall (fun i=> f i x)) a b _ _ (corner x) (Or.inl (fun P=> l (by simpa [corner] using P))) v H (fun _=>1)
 rw [show Emu.frank a b (corner x)=(if p=q then Window.kernel x else 0) from (by change (if p=q then pencil (corner x) (dnSpin ι) (upSpin ι) else 0)=_; rw [pencil_time]; simp)] at hi
 refine hi.congr fun i=>?_ ; rw [Lead.note_hop,ht,hv]
omit H e g h f in
private lemma qgap_1 (b c:Bool): Window.kernel (phaseF b)=phaseF b*P20 ∧ Window.kernel (phaseF b-(phaseF c)*3)*Window.kernel (phaseF b+(phaseF c)*3)= -(P20*P20/512):=by
 rw [P20_value]; cases b <;> cases c <;> norm_num [phaseF,Window.kernel,one_div] <;> ring_nf
lemma progression (Q:∀ i,Melody B (S i)) (q:∀ i,(Q i).face=c)(u:∀ i,(Q i).first.wave=b)(l:∀ i,(Q i).first.slot=ι) {D T Z:∀ i, Op (Single (Y i))} (v:∀ i,Clad (Dofu (Y i) (field (F i) j (M i))) (tickA (Y i)) (T i) (D i) (Z i))(W:∀ i,Dofu (Y i) (L i)=laneP (tickA _) (T i) (Z i)) (w:Bool) : Tendsto (fun i:ℕ=> (Q i).noteL (Kea.tax (d₀ i)) w (Dofu _ (L i)) (Tset _) (Tset _)) atTop (𝓝 0):=by
 let P (i:ℕ):=(Q i).first; let R(i:ℕ):=(Q i).last; let A:=phaseF b; let X(i:ℕ):=Dofu (Y i) (L i); let Y' (i:ℕ):=Tset (Y i)
 let d:=phaseF c*3
 have hl(i): (R i).slot=ι:= (Q i).slot_s.trans (l i)
 have hu(i): (R i).wave=b:= (Q i).wave_s.trans (u i)
 have hx:A≠0:=by cases b <;> simp [A, phaseF]
 have hz:A-d≠0:=by cases b <;> cases c<;> norm_num [A,d,phaseF]
 have ha:A+d≠0:=by cases b <;> cases c<;> norm_num [A,d,phaseF]
 have hA : Tendsto (fun i:ℕ=>riseX (S i) (direction (sail b (S i)))) atTop (𝓝 (corner A)):=by simpa only [mul_one,A] using sailed b (fun i=>S i) (units_const h)
 have hσ(i:ℕ): (R i).wave=(P i).wave:= (Q i).wave_s
 have hb(i:ℕ): (P i).death-(P i).birth=direction (sail b (S i)):= sub_eq_iff_eq_add'.2 ((P i).aligns.trans (by rw [show (P i).wave=b from u i]))
 have hr(i:ℕ): (R i).death-(R i).birth=direction (sail b (S i)):= sub_eq_iff_eq_add'.2 ((R i).aligns.trans (by rw [hu]))
 have he:Tendsto (fun i:ℕ=> riseX (S i) ((R i).birth-(P i).birth)) atTop (𝓝 (corner d)):=by simp_rw [show ∀ i:ℕ,(R i).birth-(P i).birth=direction (sail c (gap B (S i))) from fun i=>sub_eq_iff_eq_add'.2 ((Q i).aligned.trans (by rw [q i]))]; exact sailed c _ (gap_exact h)
 have hk:Fintype.card (Fin 3)=3:=by simp
 let m:=Lead.cash b
 have h₀(p:Slot): Tendsto (fun i=>(P i).note (P i) (X i) (d₀ i) p p) atTop (𝓝 (Window.kernel A)):= by apply Eq.mp _ ( note_t h H e g f P P p p A hx l l (by simp_rw [hb]; exact hA)); rw [if_pos rfl]
 let F'(i:ℕ):= P i; let V₀:=Window.kernel A
 cases w
 · have ht:Tendsto (fun i=> Lead.cash b * ∑ p∈five,(P i).note (P i) (X i) (d₀ i) p p-P20) atTop (𝓝 (m*∑ _p∈five,V₀-P20)):= ((tendsto_finsetSum _ fun i _=> h₀ i).const_mul m).sub_const _
   rw [sum_const,five_card,nsmul_eq_mul,show V₀= _ from (qgap_1 b c).1] at ht -- V₀
   have hg:m*((5:ℕ) • ((phaseF b:ℂ)*P20))-P20=0:=by cases b <;> norm_num [phaseF, m,Lead.cash] <;> ring
   convert ht using 1
   · funext i; unfold noteL compare; simp only [Bool.false_eq_true,ite_false,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.sub_apply,smul_eq_mul,mul_one]; unfold P X; rw [W,vocal₁ (v i),u]
   simp only [nsmul_eq_mul] at hg; rw [hg]

 let Zdn(p q:Slot):= if p=q then Window.kernel (A-d) else 0
 let Zup(p q:Slot):= if p=q then Window.kernel (A+d) else 0
 have hh:= Tendsto.sub hA he; have h₁(p q':Slot):= note_t h H e g f P R p q' (A-d) hz l hl (by
   rw [← corner_sub]; refine hh.congr fun i=>?_ ;  rw [←hb i,face_z]; exact congrArg _ (by abel))
 have h₂ (p q':Slot): Tendsto (fun i=>(R i).note (P i) (X i) (d₀ i) p q') atTop (𝓝 (Zup p q')):= note_t h H e g f R P p q' _ ha hl l (by

    have hg: Tendsto (fun i:ℕ=> riseX (S i) ((P i).birth-(R i).birth)) atTop (𝓝 (corner (-d))):=by
       rw [show corner (-d)=-corner d from PiLp.single_neg ..]
       refine he.neg.congr fun i=>?_ ;  ext a; simp [riseX, moor]; ring

    rw [←sub_neg_eq_add,←corner_sub]; refine (hA.sub hg).congr fun i=>?_ ;  rw [←hr i,face_z]; exact congrArg _ (by abel))
 let fA(i:ℕ)(p q:Slot) := (P i).note (P i) (X i) (d₀ i) p p*(R i).note (R i) (X i) (d₀ i) q q-(P i).note (R i) (X i) (d₀ i) p q*(R i).note (P i) (X i) (d₀ i) q p
 let G(p q : Slot):=V₀*V₀-Zdn p q * Zup q p
 have h₃(p:Slot): Tendsto (fun i=>(R i).note (R i) (X i) (d₀ i) p p) atTop (𝓝 V₀):= by apply Eq.mp _ ( note_t h H e g f R R p p A hx hl hl (by simp_rw [hr]; exact hA)); rw [if_pos rfl]
 have ht : Tendsto (fun i=> m^2*(∑ p∈five,∑ q∈five,fA i p q)-(compared:ℂ)) atTop (𝓝 (m^2*(∑ p∈five,∑ q∈five,G p q)-(compared:ℂ))) := ((tendsto_finsetSum _ fun p _=>tendsto_finsetSum _ (fun q _=> show Tendsto (fun i=>fA i p q) atTop (𝓝 (G p q)) from (((h₀ p).mul (h₃ q)).sub ((h₁ p q).mul (h₂ q p))))).const_mul (m^2)).sub_const _ -- tune parens
 have hp(p q:Slot): G p q= P20*P20+ if p=q then P20*P20/512 else 0:= by
    have hh: V₀*V₀=P20*P20:=by rw [show V₀= _ from (qgap_1 b c).1]; cases b <;> simp [phaseF]
    unfold G Zdn Zup; rw [hh]; by_cases h:p=q; · rw [if_pos h,if_pos h.symm, show Window.kernel (A-d)* Window.kernel (A+d)=_ from (qgap_1 b c).2]; simp [h]
    simp [h]
 have hg: m^2*(∑ p∈five,∑ q∈five,G p q)-(compared:ℂ)=0:=by
    have ht: (compared:ℂ)= P20*P20*(1+1/(5*512)):=by unfold compared; push_cast; simp [P20_value]; left; ring
    have he: m^2=1/25:=by cases b<;> norm_num [m,Lead.cash,phaseF]
    rw [ht,he]
    simp_rw [hp,sum_add_distrib]; simp [five_card]; ring
 rw [hg] at ht; refine ht.congr fun i=>?_ ; unfold noteL compare
 simp only [ite_true,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.sub_apply,smul_eq_mul,mul_one]
 unfold fA P R X; rw [W,vocal₂ (v i) _ _ (Q i).wave_s,u]
end surge
end YM.CF.Buffered.Ballad.Melody
#print axioms YM.CF.Buffered.Ballad.Melody.progression
