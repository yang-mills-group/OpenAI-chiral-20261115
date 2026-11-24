import ForceSatin.PulseTune
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Classical
local notation "π" => Real.pi
open YM.Stationary (Gaia exileE cartWeight cart_weight_pos orbit_at)
open Spring Spring.SunPay MeasureTheory Lyra
variable {F:Momentum→ℂ}{T:Gaia→ℂ}{N: Side}
section diff
def muJet (l:List Cover)(f:Cover→ℂ):Cover→ℂ:=l.foldr (fun i z t=>z (t+i)-z t) f
lemma muJet_cons (l:List Cover)(i:Cover)(z:Cover→ℂ) (x:Cover): muJet (i::l) z x=muJet l z (x+i)-muJet l z x:=rfl
@[simp] lemma muJet_nil(f):muJet [] f=f:=rfl
lemma muJet_sub(l:List Cover)(f g:Cover→ℂ): muJet l (f-g)=muJet l f - muJet l g:=by induction l with| nil=> rfl| cons i l ih=> ext1 x; simp_rw [Pi.sub_apply,muJet_cons,ih,Pi.sub_apply]; abel
lemma muJet_mul(l:List Cover)(f:Cover→ℂ)(z:ℂ): muJet l (z • f)= z • muJet l f:=by induction l with| nil=>rfl|cons i l ih=>ext1 x; rw [muJet_cons,ih]; simp [muJet_cons,mul_sub]
lemma muJet_go(l:List Cover){α:Type*}{g:Filter α}{F:α→Cover→ℂ}{f:Cover→ℂ}(h:∀ x:Cover,Tendsto (fun i=> F i x) g (𝓝 (f x))) (x:Cover): Tendsto (fun i=> muJet l (F i) x) g (𝓝 (muJet l f x)):=by induction l generalizing x with| nil=>exact h x|cons y l ih=> exact (ih _).sub (ih _)
lemma mu_shift (i:Cover)(s:Offset N)(F:Site N→ℂ):skyPrice s (fun j=> threadV i (tmap (glen s j))*F j)=muJet [i] (skyPrice s F):=by
 ext1 j; rw [muJet_cons]; unfold skyPrice; rw [muJet_nil,←mul_sub]; congr 1; unfold chants; rw [← sum_sub_distrib]; apply sum_congr rfl; intro z _; unfold charK threadV; rw [mode_shift]; ring
lemma mu_coin(l:List Cover)(s:Offset N)(F:Site N→ℂ):skyPrice s (fun j=> condense l (tmap (glen s j))*F j)=muJet l (skyPrice s F):=by
 induction l with
 | nil=> simp [condense]
 | cons i l ih=> simp_rw [condense,List.map_cons,List.prod_cons,mul_assoc]; erw [mu_shift i s (fun j=> condense l (tmap (glen s j))*F j),ih]; rfl
lemma skySub(s:Offset N)(F G:Site N→ℂ):skyPrice s (F-G)=skyPrice s F-skyPrice s G:=by ext i; simp only [skyPrice, chants, Pi.sub_apply,mul_sub,sum_sub_distrib]
end diff
abbrev winX(z:Cover):=‖scape z‖
lemma scape_add (x y:Cover): scape (x+y)=scape x+scape y:=by ext i; change ((↑(x i+y i):ℝ))=_+_; push_cast; rfl
abbrev Teen(z:Cover):=1+winX z
lemma teen_low (z:Cover) : 0 < Teen z:=by unfold Teen winX; positivity
structure Hurried (k:ℕ)(f:Cover→ℂ):Prop where
 gift :∃ C:ℝ,0≤C ∧ ∀ x:Cover,(Teen x)^k *‖f x‖ ≤ C
namespace Hurried
variable {k:ℕ}{f:Cover→ℂ}(h:Hurried k f)
lemma loft(k:ℕ){f:Gaia→ℂ}(h:Swift f):Hurried k (f ∘ scape):=by
 obtain ⟨C,c,p⟩:= h.fast k; refine ⟨2^k*C+(Teen 0)^k *‖f (scape 0)‖,by have h:= teen_low 0; positivity,fun x=>?_⟩; by_cases e:x=0; · subst x; apply le_add_of_nonneg_left; positivity
 have hp:1≤ ‖scape x‖:= norm_r _ e; refine le_trans ?_ (le_add_of_nonneg_right (show 0≤ (Teen 0)^k*‖f (scape 0)‖ from (by unfold Teen winX; positivity))); change (1+‖scape x‖)^k * ‖f (scape x)‖ ≤_; apply le_trans _ (mul_le_mul_of_nonneg_left (p (scape x) hp) (by positivity)); rw [← mul_assoc, ← mul_pow]; gcongr; linarith
include h
lemma scurry(i: Cover):Hurried k (fun x=>f (x+i)):=by
 obtain ⟨C,c,p⟩:= h.gift; have ht:= teen_low i; refine ⟨Teen i ^k*C,by positivity,fun x=>?_⟩; apply le_trans _ (mul_le_mul_of_nonneg_left (p (x+i)) (by positivity)); rw [←mul_assoc,←mul_pow]; gcongr
 unfold Teen winX; rw [scape_add]; have he:=norm_sub_le (scape x + scape i) (scape i); rw [add_sub_cancel_right] at he; nlinarith [mul_nonneg (norm_nonneg (scape i)) (norm_nonneg (scape x+scape i))]
lemma inter {g:Cover→ℂ}(u:Hurried k g):Hurried k (f-g):=by
 obtain ⟨C,c,p⟩:=h.gift; obtain ⟨A,a,v⟩:=u.gift; refine ⟨C+A,by positivity,fun x=>?_⟩; refine (mul_le_mul_of_nonneg_left (norm_sub_le ..) (pow_nonneg (teen_low x).le _)).trans ?_; rw [mul_add]; exact add_le_add (p x) (v x)
lemma leaves(l:List Cover):Hurried k (muJet l f):=by induction l with| nil=>exact h| cons i l ih=> exact (ih.scurry i).inter ih
lemma hot : ∃ C:ℝ,0≤C ∧ ∀ x:Cover,x≠0 → ‖f x‖ ≤ C/rally x^k:=by
 obtain ⟨C,c,p⟩:=h.gift; refine ⟨C,c,fun x a=>?_⟩; have hx:= planePeak a; rw [le_div_iff₀ (by positivity : 0< rally x^k),mul_comm]; apply le_trans _ (p x); have hv:rally x ≤ Teen x:= (orbit_at (shaftX x)).trans (show winX x≤ Teen x from le_add_of_nonneg_left zero_le_one); gcongr
end Hurried
section
variable {ι:Type*}{X:Lyra ι}{U:ι→Momentum→ℂ}{m:ℕ}(H:Singer X m U F)(V:SunPay F T)
include H V
abbrev warble (_:Singer X m U F) (i:ι)(z:Cover):= skyPrice (X.S i) (fun j=> U i (tmap (X.steps i j))) z
theorem timely (l:List Cover): ∃ C:ℝ,0<C∧∀ f:ℕ→ι,(∀ i,Juno (X.S (f i))) → Tendsto (fun i=>(X.N (f i)).val) atTop atTop → ∀ z:Cover, z≠0 → ∀ᶠ i in atTop, ‖muJet l (warble H (f i)) z-muJet l (T ∘ scape) z‖ ≤ C/rally z^(4+m+l.length):=by
 let G:= gorge (low F) ∘ scape; let F'(i:ι)(t:Site (X.N i)):=mango F (X.steps i t); let k:=4+(m+l.length)
 obtain ⟨B,b,Q⟩:= (Hurried.loft k (V.melt)|>.leaves l).hot; obtain ⟨C,u,P⟩:= X.perchLines (Bouquet H l) -- tune args 
 refine ⟨B+C+1,by positivity,fun f h p z e=>?_⟩; let Y(i:ℕ):= muJet l (skyPrice (X.S (f i)) (F' (f i))) z; have he:Tendsto Y atTop (𝓝 (muJet l G z)):= muJet_go (F:=fun i=>skyPrice (X.S (f i)) (F' (f i))) l (leaning V _ _ h p) z; let t:=rally z^k; have ht:0<t:= pow_pos (planePeak e) _
 have hw: ‖muJet l G z-muJet l (T ∘ scape) z‖ ≤ B/t:=by
    have hx:= Q z e; change ‖muJet l (G-T ∘ scape) z‖ ≤_ at hx; rw [muJet_sub] at hx; exact hx
 filter_upwards [Metric.tendsto_nhds.mp he (1/t) (by positivity),P z e _ p] with i r w
 have hs:= w (f i) rfl; let U0:=X.S (f i); let T0:=warble H (f i); let y:=T ∘ scape; let o:=T0 z; let G₁(j:Site (X.N (f i))):= tmap (X.steps (f i) j); let d:=U (f i) ∘ G₁; let D:=d-F' (f i)
 have hp :‖muJet l T0 z-Y i‖ ≤ C/t:=by
    let f':= fun (x:Momentum)=> condense l x*F x; have hv:X.mistC (fun i z=>condense l z*U i z) f' (f i)=fun j=> condense l (G₁ j)* D j:=funext fun j=>by unfold mistC D F' f' mango; simp only [Pi.sub_apply]; change condense l (G₁ j)* d j-_ = _; ring -- tune
    change ‖skyPrice _ (X.mistC _ f' (f i)) _‖ ≤_ at hs; rw [hv, show skyPrice U0 (fun j=> condense l (G₁ j)*D j)= _ from mu_coin l U0 D,skySub U0, muJet_sub] at hs; exact hs
 have hr:‖Y i-muJet l G z‖ ≤ 1/t:= (dist_eq_norm (Y i) (muJet l G z)) ▸ r.le;
 rw [_root_.add_assoc 4, add_div,add_div]; exact (norm_sub_le_norm_sub_add_norm_sub (muJet l T0 z) (Y i) (muJet l y z)).trans (by linarith only [hp, hr,hw,norm_sub_le_norm_sub_add_norm_sub (Y i) (muJet l G z) (muJet l y z)]) -- tune add_assoc first rw
end
#print axioms timely
end YM.Regis.Circuit.SpringDay
