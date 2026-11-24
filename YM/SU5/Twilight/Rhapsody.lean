import YM.SU5.Celeste.Brooch
/-! Adaptation of Fluxion,Audition,Duet. Testing ALL clans, same enrollment.
 This port allows FIXED transverse or arbitrary offset in relative leg, even with position/rotation slack. As in Brooch:
 Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open Lead (cash)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{F K T D U:Op (Single N)} {d:Candle}

open Py.Rate.LocalLimit.Papal (Weaver)
open Lead (Clan)
open Melody (groundBid note_t vocalB₁ vocalB₂)
private abbrev dimZ(x:Clan):ℕ:= Window.dimf x
structure Promenade (B:Side) (R:ℕ) (shift:Cover) where
 first: Lead R
 last: Lead R
 slot_s : last.slot=first.slot
 wave_s : last.wave=first.wave
 face : Bool
 aligned : last.birth= first.birth+(direction (sail face (gap B R))+shift) -- don't conflate with actual shift when tending arity 
variable {J:Cover}
namespace Promenade
def groundLead (A:Promenade B R J)(X:Clan)(b:Bool): Weaver:= (if b then A.first.groundWord X*A.last.groundWord X else A.first.groundWord X)-groundBid X b • (1:Weaver)
variable (σ:Clan)
def noteClan (A:Promenade B R J)(V:Pane N)(b:Bool)(L:Op (Single N)) := (if b then A.first.cladMark σ V L*A.last.cladMark σ V L else A.first.cladMark σ V L)- groundBid σ b • 1 -- tune
lemma dressed_clan (U':Fields N)(p:Clad F K T D U)(b:Bool)(A:Promenade B R J): Dress (laneP K T U) (A.groundLead σ b N U') (noteClan σ A U'.1 b (laneP K T U)):=by unfold groundLead noteClan; split; exact ((A.first.dress_clan σ _ p).mul (A.last.dress_clan σ _ p)).sub ((Dress.one _).l _); exact (A.first.dress_clan σ _ p).sub ((Dress.one _).l _)
section surge
open YM.Stationary (Gaia)
variable {S:ℕ→ℕ}{Y:ℕ→Side}{j:ℕ}{ι:Fin 2}
variable {M:ℕ→ Jill.Male}{d₀:ℕ→ Candle}{F:∀ i,Slide (Y i) (d₀ i)} {L:∀ i,Stag (Y i)→ Peb}
variable (h:Yard Y (fun i=>(S i:ℝ))){b c:Bool} {r C:ℝ}
include h in
private lemma units_const1 : Tendsto (fun i:ℕ=> (((S i:ℕ):ℤ):ℝ)/(S i:ℝ)) atTop (𝓝 1) := tendsto_const_nhds.congr (fun i=>by have hp:0<(S i:ℝ):=h.pos i; rw [Int.cast_natCast,div_self hp.ne'])
include h in
private lemma gap_exact1 : Tendsto (fun i:ℕ=> (gap B (S i):ℝ)/(S i:ℝ)) atTop (𝓝 3) := by
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
private lemma sailed1 (f:Bool)(v:ℕ→ℤ){x:ℝ}(p: Tendsto (fun i=>(v i:ℝ)/(S i:ℝ)) atTop (𝓝 x)): Tendsto (fun i:ℕ=> riseX (S i) (direction (sail f (v i)))) atTop (𝓝 (corner (phaseF f*x))) := by
 have ht(i:ℕ)(K:ℤ) : riseX (S i) (direction (sail f K)) = corner (phaseF f * ((K:ℝ)/ (S i:ℝ))) := by
   ext a; by_cases t:a=3; all_goals cases f <;> simp [phaseF,sail,corner,riseX,direction,t,moor, neg_div]
 simp_rw [ht]; apply (show Continuous corner from ?_).continuousAt.tendsto.comp (p.const_mul _)
 refine (PiLp.continuous_toLp 2 _).comp (f:=fun (x:ℝ) => Pi.single (M:=fun _:Axis => ℝ) 3 x) (continuous_pi ?_); intro i; by_cases g:i=(3:Axis)
 · subst i; simp only [Pi.single_eq_same]; exact continuous_id
 simp [g]; exact continuous_const
variable (H:1 ≤ j) (e:0 < r)(g:0<C)(f:∀ i x, FormU ((F i).u x) j (M i) r C (trackF (F i) (L i) x))
private lemma qgap_2 (b c:Bool): Window.kernel (phaseF b)=phaseF b*P20 ∧ Window.kernel (phaseF b-(phaseF c)*3)*Window.kernel (phaseF b+(phaseF c)*3)= -(P20*P20/512):=by
 rw [P20_value]; cases b <;> cases c <;> norm_num [phaseF,Window.kernel,one_div] <;> ring_nf
include h H e g f
lemma development (Q:∀ i,Promenade B (S i) J) (q:∀ i,(Q i).face=c)(u:∀ i,(Q i).first.wave=b)(l:∀ i,(Q i).first.slot=ι) {D T Z:∀ i, Op (Single (Y i))} (v:∀ i,Clad (Dofu (Y i) (field (F i) j (M i))) (tickA (Y i)) (T i) (D i) (Z i))(W:∀ i,Dofu (Y i) (L i)=laneP (tickA _) (T i) (Z i)) (w:Bool) : Tendsto (fun i:ℕ=> (Q i).noteClan σ (Kea.tax (d₀ i)) w (Dofu _ (L i)) (Tset _) (Tset _)) atTop (𝓝 0):=by
 let P (i:ℕ):=(Q i).first; let R(i:ℕ):=(Q i).last; let A:=phaseF b; let X(i:ℕ):=Dofu (Y i) (L i); let Y' (i:ℕ):=Tset (Y i)
 let d:=phaseF c*3
 have hl(i): (R i).slot=ι:= (Q i).slot_s.trans (l i)
 have hu(i): (R i).wave=b:= (Q i).wave_s.trans (u i)
 have hx:A≠0:=by cases b <;> simp [A, phaseF]
 have hz:A-d≠0:=by cases b <;> cases c<;> norm_num [A,d,phaseF]
 have ha:A+d≠0:=by cases b <;> cases c<;> norm_num [A,d,phaseF]
 have hA : Tendsto (fun i:ℕ=>riseX (S i) (direction (sail b (S i)))) atTop (𝓝 (corner A)):=by simpa only [mul_one,A] using sailed1 b (fun i=>S i) (units_const1 h)
 have hσ(i:ℕ): (R i).wave=(P i).wave:= (Q i).wave_s
 have hb(i:ℕ): (P i).death-(P i).birth=direction (sail b (S i)):= sub_eq_iff_eq_add'.2 ((P i).aligns.trans (by rw [show (P i).wave=b from u i]))
 have hr(i:ℕ): (R i).death-(R i).birth=direction (sail b (S i)):= sub_eq_iff_eq_add'.2 ((R i).aligns.trans (by rw [hu]))

 have rise:J=J:=rfl
 have hC : Tendsto (fun i=> riseX (S i) J) atTop (𝓝 0):= by
    have he: Tendsto (fun i a=> ((J a):ℝ)/(S i:ℝ)) atTop (𝓝 (fun _=>0)):=tendsto_pi_nhds.mpr (fun a=>h.thinner ((J a):ℝ))
    exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp he
 have he:Tendsto (fun i:ℕ=> riseX (S i) ((R i).birth-(P i).birth)) atTop (𝓝 (corner d)):=by
   simp_rw [show ∀ i:ℕ,(R i).birth-(P i).birth=direction (sail c (gap B (S i)))+J from fun i=>sub_eq_iff_eq_add'.2 ((Q i).aligned.trans (by rw [q i]))]
   have hp:Tendsto (fun i:ℕ=> riseX (S i) (direction (sail c (gap B (S i))))) atTop (𝓝 (corner d)):= sailed1 c _ (gap_exact1 h)
   have hv:= hp.add hC
   rw [add_zero] at hv
   refine hv.congr fun i=>?_; rw [show ∀ x y:Cover, riseX (S i) (x+y) = riseX (S i) x+riseX (S i) y from ?_ ]; intro x y; ext a; simp [riseX,moor,add_div]

 have hk:Fintype.card (Fin 3)=3:=by simp
 let m:=Lead.cash b
 have h₀(p:Slot): Tendsto (fun i=>(P i).note (P i) (X i) (d₀ i) p p) atTop (𝓝 (Window.kernel A)):= by apply Eq.mp _ ( note_t h H e g f P P p p A hx l l (by simp_rw [hb]; exact hA)); rw [if_pos rfl]
 let F'(i:ℕ):= P i; let V₀:=Window.kernel A
 cases w
 · have ht:Tendsto (fun i=> Lead.cash b * ∑ p∈(colors σ),(P i).note (P i) (X i) (d₀ i) p p-(purePrice σ:ℂ)) atTop (𝓝 (m*∑ _p∈(colors σ),V₀-(purePrice σ:ℂ))):= ((tendsto_finsetSum _ fun i _=> h₀ i).const_mul m).sub_const _
   rw [sum_const,colors_card,nsmul_eq_mul,show V₀= _ from (qgap_2 b c).1] at ht
   have hg:m*((Window.dimf σ:ℂ)*((phaseF b:ℂ)*P20))-(purePrice σ:ℂ)=0:=by rw [price_as]; cases b <;> simp [m,Lead.cash,phaseF,dimZ] <;> ring
   convert ht using 1
   · funext i; unfold noteClan groundBid; simp only [Bool.false_eq_true,ite_false,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.sub_apply,smul_eq_mul,mul_one]; unfold P X; rw [W,vocalB₁ σ (v i),u]
   rw [hg]

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
 have ht : Tendsto (fun i=> m^2*(∑ p∈(colors σ),∑ q∈(colors σ),fA i p q)-(brill σ:ℂ)) atTop (𝓝 (m^2*(∑ p∈(colors σ),∑ q∈(colors σ),G p q)-(brill σ:ℂ))) := ((tendsto_finsetSum _ fun p _=>tendsto_finsetSum _ (fun q _=> show Tendsto (fun i=>fA i p q) atTop (𝓝 (G p q)) from (((h₀ p).mul (h₃ q)).sub ((h₁ p q).mul (h₂ q p))))).const_mul (m^2)).sub_const _ -- tune parens
 have hp(p q:Slot): G p q= P20*P20+ if p=q then P20*P20/512 else 0:= by
    have hh: V₀*V₀=P20*P20:=by rw [show V₀= _ from (qgap_2 b c).1]; cases b <;> simp [phaseF]
    unfold G Zdn Zup; rw [hh]; by_cases h:p=q; · rw [if_pos h,if_pos h.symm, show Window.kernel (A-d)* Window.kernel (A+d)=_ from (qgap_2 b c).2]; simp [h]
    simp [h]
 have hg: m^2*(∑ p∈(colors σ),∑ q∈(colors σ),G p q)-(brill σ:ℂ)=0:=by
    have he: m^2=1/25:=by cases b<;> norm_num [m,Lead.cash,phaseF]; -- tune
    have hw(p:Slot)(e:p∈(colors σ)): (∑ q∈(colors σ),G p q)=(dimZ σ:ℂ)* (P20*P20)+P20*P20/512:=by simp_rw [hp,sum_add_distrib]; rw [sum_const,nsmul_eq_mul,colors_card,sum_ite_eq,if_pos e]
    rw [he,brill_as,price_as,sum_congr rfl hw,sum_const,nsmul_eq_mul,colors_card]; unfold dimZ; ring -- ring
 rw [hg] at ht; refine ht.congr fun i=>?_ ; unfold noteClan groundBid
 simp only [ite_true,Matrix.smul_apply,Matrix.one_apply_eq,Matrix.sub_apply,smul_eq_mul,mul_one]
 unfold fA P R X; rw [W,vocalB₂ σ (v i) _ _ (Q i).wave_s,u]

end surge
end Promenade
section Era
variable (σ:Clan) {B : Side} {R j:ℕ} {r C:ℝ}
abbrev LedgerZ (N:Side) (j:ℕ)(v C e:ℝ)(w: Bool)(A:Promenade B R J) := ∀ {d:Candle} (F:Slide N d) (V:Stag N→ Peb) (M:Jill.Male), (∀ i,FormU (F.u i) j M v C (trackF F V i))→∀ T D K:Op (Single N), Clad (Dofu N (field F j M)) (tickA N) T D K → Dofu N V=laneP (tickA N) T K →
   ‖A.noteClan σ (Kea.tax d) w (Dofu N V) (Tset N) (Tset N)‖≤e
private lemma sold_eraZ (e:ℝ)(w b c:Bool)(l:Fin 2)(t:0<e)(p:1≤j)(u:0<r)(v:0<C) :
 ∀ᶠ R:ℕ in atTop, ∀ᶠ N:Side in atTop, Even N.val → ∀ (A:Promenade B R J), A.first.slot=l→ A.face=b→ A.first.wave=c→ LedgerZ σ N j r C e w A := by
 let P(R:ℕ)(N:Side) := Even N.val → ∀ A:Promenade B R J,A.first.slot=l→ A.face=b→ A.first.wave=c→ LedgerZ σ N j r C e w A
 change ∀ᶠ R:ℕ in atTop, ∀ᶠ N:Side in atTop,P R N
 by_contra k
 obtain ⟨S,h,H⟩ : ∃ S:ℕ→ℕ, (∀ i,i<S i)∧∀ i,∃ᶠ N:Side in atTop,¬P (S i) N := by
   have hp(i:ℕ) : ∃ R:ℕ,i<R∧∃ᶠ N:Side in atTop,¬P R N := by
      obtain ⟨R,x,u⟩:= (not_eventually.mp k|>.and_eventually (eventually_gt_atTop i)).exists
      exact ⟨R,u,not_eventually.mp x⟩
   choose S h g using hp; exact ⟨S,h,g⟩
 let y(i:ℕ):ℝ:=S i
 have hy(i:ℕ):0<y i:=by unfold y; exact_mod_cast show 0<S i from Nat.zero_le _|>.trans_lt (h i)
 have hx(i:ℕ):∃ N:Side,y i* Ember.pinch N ≤ (1/2:ℝ)^i∧¬P (S i) N := by
   obtain ⟨k,X⟩:= Glaze.pick_depth ((1/2)^i/y i) (by have he:=hy i; positivity)
   obtain ⟨T,v,g⟩:= ((H i).and_eventually (eventually_ge_atTop (⟨k+1,by omega⟩:Side))).exists
   exact ⟨T,(mul_comm (y i) _).le.trans ((le_div_iff₀ (hy i)).1 (X (by change k+1 ≤ T.val at g; omega))),v⟩
 choose Y f F using hx
 unfold P LedgerZ at F; push Not at F
 choose u' A ha hb hw d Q V M L T D K p' z Z using F
 have he:Yard Y (fun i=>(S i:ℝ)):=by
   refine ⟨hy,?_,?_,u'⟩
   · exact tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun v=> (h v).le) tendsto_id)
   apply squeeze_zero (fun i=>mul_nonneg (hy i).le (Ember.pinch_pos _).le) f (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num))
 have hr:= Promenade.development σ he p u v L A hb hw ha p' z w; rw [tendsto_zero_iff_norm_tendsto_zero] at hr; obtain ⟨i,k⟩:= (hr.eventually (gt_mem_nhds t)).exists; exact not_lt_of_ge (Z i).le k
lemma Promenade.atClan (p:1≤j)(u:0<r)(v:0<C)(e:ℝ)(t:0<e) : ∀ᶠ R:ℕ in atTop,∀ᶠ N:Side in atTop,Even N.val→∀ A:Promenade B R J,∀ w:Bool, LedgerZ σ N j r C e w A := by
 have he:= eventually_all.mpr (fun w:Bool=>eventually_all.mpr (fun b:Bool=>eventually_all.mpr (fun c:Bool=> eventually_all.mpr (fun l:Fin 2=> sold_eraZ σ (B:=B) (J:=J) e w b c l t p u v))))
 filter_upwards [he] with R he
 filter_upwards [eventually_all.mpr (fun w=>eventually_all.mpr (fun b=>eventually_all.mpr (fun c=> eventually_all.mpr (fun l=> he w b c l))))] with N he using fun i A w=> he w A.face A.first.wave A.first.slot i A rfl rfl rfl

end Era
open YM.CF.Lamour YM.CF.Velvet YM.CF.Lamour.Bridge.Celeste
namespace Promenade
lemma heldFlag {B:Side}{j:ℕ}(h:1≤j){M:Jill.Male}(v:Pad j N)(W:Clan)(b:Bool)(A:Promenade B R J)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x) : A.noteClan W 1 b (lake N j M) (Tset N) (Tset N)=alleyR (mateK N) x (A.groundLead W b N (1,1)):=by
 have he:= (pitch M h v.1).1; let Φ:=lake N j M; let P:=mateK N; let u:= Tset N; let y:= A.groundLead W b N (1,1); let g:= A.noteClan W 1 b Φ
 have hh:Dress (laneP (tickA N) 1 (Dofu N (lakeK N j M))) y g:=by unfold g Φ; rw [(pitch M h v.1).2]; exact dressed_clan W (1,1) he b A
 rw [coasting v M] at p; have ht:= hh.emit he p (tickB N); rw [skyGlow,quant_one,act_one,mul_one, mateV_emit] at ht; change g u u= (inner ℂ P x)⁻¹ * (inner ℂ P (acts y x)); change (inner ℂ P (acts y x))=inner ℂ P x * g u u at ht; rw [ht, inv_mul_cancel_left₀]; let hc:=shines he x _ p (tickB N); rw [skyGlow,quant_one,act_one] at hc; exact hc
lemma eraFlag {j:ℕ}(B:Side)(h:1 ≤j){x:ℝ}(p:0<x): ∀ᶠ R:ℕ in atTop,∀ (A:Promenade B R J)(σ:Clan)(b:Bool), Clarity (A.groundLead σ b) j x:=by
 obtain ⟨z,v,L⟩:=lake_formal h; have he:= Filter.eventually_all.mpr (fun x':Clan=> atClan x' (B:=B) (J:=J) h v (show (0:ℝ)<1 by norm_num) x p)
 filter_upwards [he] with R u A σ b; filter_upwards [u σ,ownsHalo h] with N e v t M y Y; rw [← heldFlag h (v t).1 σ b A y Y,← show Kea.tax emptyC=(1:Pane N) from clear_canvas]; obtain ⟨a,C⟩:=pitch M h t; exact e t A b (too N) (lakeP N j M) M (L N t _) 1 1 (Dofu N (lakeK N j M)) a C
end Promenade
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Promenade.eraFlag
