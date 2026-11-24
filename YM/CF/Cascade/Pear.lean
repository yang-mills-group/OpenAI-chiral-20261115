import YM.CF.Cascade.Barns
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
local notation "dη"=>Aroma.port
local notation "μN"=> Ember.pinch
def bookie(n:Side)(u:CoreX)(X:Aim n)(M:Male)(j:ℕ)(I:Pride n) (p:Momentum):= (syl (copper n u (assets j M X.den I ∘represent)) (hike p) (hike p)).re
def base_u(n:Side):= date n*μN n^2
lemma base_p(n:Side):0<base_u n:=by unfold base_u; exact mul_pos (date_pos _) (pow_pos (pinch_pos _) _)
lemma corK {B L:Side}{ho:Odd L.val}{Y:Pricing j L ho (Vault.Thread j)}{e:ℝ}{P:Grasp Y B e} (M:Male)(i:Air n)(W:Dress n)(Q:Ample W)(I:Pride n)(h:P.roundZ≤ n.val)(v:Stamped j L ho Y)(p:0<e)(t:1≤j)(S:ContDiffAt ℝ ω (spar j M ∘represent (n:=More n)) 0)(u:CoreX): copper n u (assets j M W I ∘ represent) i i=palmH (ArcJ u j M W) i +2*(trim 2 (pigment I∘represent) (pour n u i)).re:=by
 let V:=Complex.ofRealCLM; let F:=gala M j W∘ represent; have he:ContDiffAt ℝ (↑(2:ℕ)) F 0:=(gala_h h p t v _ _ Q S).of_le le_top; let U:= (V ∘ F); let T:=pigment I ∘ represent; have hF:ContDiffAt ℝ (↑(2:ℕ)) U 0:=V.contDiff.contDiffAt.comp 0 he; have hh:ContDiffAt ℝ (↑(2:ℕ)) T 0:=(tuck I).of_le le_top
 rw [copperP (p:= (worthW v p t h _ _ _ Q S).2.of_le le_top),palmC M i h p t v u W Q S]; rw [show assets j M W I∘ represent=U+T from rfl,trim_addI hF hh,Pi.add_apply,Complex.add_re]; rw [show trim 2 U= V ∘ trim 2 F from trim_up V F he]; rw [mul_add]; rfl
lemma math_p (j:ℕ)(p:1≤j)(u:CoreX)(w:‖u‖=1)(x C y D a B:ℝ)(s:0<x)(b:0<C)(f:0<y)(k:0<D)(v:0<a)(d:0<B):∃ i:ℕ,∃ K:ℝ, 0<K ∧∀ {L:Side}{ho:Odd L.val}{η:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{G:Side}{P: Grasp Y G η}{N:Side},Stamped j L ho Y→0<η→ P.roundZ≤N.val→ i ≤ N.val→ ∀ (U:Aim N)(M:Male)(I:Pride N),U.toll x y C D → Lac I a B→ Even N.val→
     |bookie N u U M j I (dη N)/base_u N- 60/(12*Real.pi^2)*Real.log N.val|≤ K ∧∀ q:Momentum, physical q→ |bookie N u U M j I q|≤ K*N.val * date N:=by
 obtain ⟨Q',W,H,hW,i,P⟩:=holdJ 2 p u w x C y D s b f k
 obtain ⟨V,hV,F⟩:= Bird _ _ H hW; let l:= Q'/8; have hp:0<l:=by unfold l; positivity
 obtain ⟨j',T⟩:=hol_proj j p; obtain ⟨r,R,X⟩:= infrared (ting u) (tingP _) j p l V hp hV; obtain ⟨K,hk,m,M⟩:=kroner hp hV j p
 let A:=momentPrice 4 a * B; have hA:0<A:=mul_pos (momentPrice_pos 4 v) d; let D':=K+128*A; have hD:0<D':=by positivity
 let Y:=|r|+A+2*D'; refine ⟨i+j'+m+R+3,Y,by positivity,fun {L ho η Y G P' N} t e b q U M' I h c p'=>?_⟩
 let J:=ArcJ u j M' U.den; have hu := den_r h; have ha:= Grace u e p t M' b _ hu (T _ (by omega) _); obtain ⟨S,Q⟩:= P N (by omega) M' U h; have ht: Aroma.bill J l≤ V:= (F S (J:=J) rfl).1; have hx:b2 (Met J) l≤ V:=(F Q (J:=Met J) (funext fun i=>plume ..)).2
 let S:= copper N u (assets j M' U.den I ∘ represent); have hQ(i): S i i=palmH J i+ 2*(trim 2 (pigment I ∘ represent) (pour N u i)).re:= corK M' _ _ hu _ b t e p (T _ (by omega) M') _
 let Gx:= grove N; let W':= waveL N; let L':= dη N -- tune
 let Cv (x p):=(trim 2 (pigment I ∘ represent) (pour N u (groan (n:=N) x (hike p)))).re
 let n:ℝ:= Fintype.card (Site N); let z:= μN N; have hz:0<z:= pinch_pos _; have hn:0<n:=by unfold n; positivity
 have ha': date N=16*n:=by simp only [date,n,site_card, More, PNat.mul_coe, Nat.cast_pow]; push_cast; ring -- tune
 let d:= date N
 have hR :∀ x:ℂ,‖Complex.reCLM x‖≤‖x‖:=fun i=> Complex.abs_re_le_norm _; have hI :∀ x:ℂ,‖Complex.imCLM x‖≤‖x‖:=fun i=> Complex.abs_im_le_norm _
 constructor
 · let V':=d*z^2; have he:0<V':=base_p N; let p': Tide N L':=tide_pos 0 -- name clashes notation
   obtain ⟨u',u''⟩:= nearCapR _ p'; have hh : bookie N u U M' j I L'= Aroma.room J L'+2*(Cv Complex.reCLM L'+Cv Complex.imCLM L'):=by change S (Gx _) (Gx _) + S (W' _) (W' _)= _; rw [hQ,hQ]; unfold Gx W'; unfold Aroma.room Cv; rw [←u',←u'']; ring -- order
   have hy(x:ℂ→L[ℝ]ℝ)(g:∀ i,‖x i‖≤‖i‖): |Cv x L'|≤V'/4*A:=by
      have h:=loud L' p'.phys (n:=N) g; let f:= groan (n:=N) x (hike L')
      apply (Complex.abs_re_le_norm _).trans; apply (bulk z I c v (pour N u f) (glance _ _ w h) (partSound _ (fun x t=>milder (by simp [More]; omega) g x t) u w hz.le) le_rfl).trans_eq; unfold V' A d; rw [ha']; unfold n; ring
   have hv:= X _ _ J (by omega) ‹Even N.val› ha ht hx; simp only [tingV u w, show (60:ℂ).re=60 by norm_num] at hv
   change |bookie N u U M' j I L' /V'- _|≤ _; rw [hh, add_div,add_sub_right_comm]; apply (abs_add_le ..).trans
   have hC:=hy Complex.reCLM hR; have hp:=hy Complex.imCLM hI
   have hJ: |2*(Cv Complex.reCLM L'+ Cv Complex.imCLM L')/V'|≤ A:=by
      rw [abs_div,abs_of_pos he,abs_mul,abs_of_pos (by norm_num:(2:ℝ)>0),div_le_iff₀ he]; exact (mul_le_mul_of_nonneg_left ((abs_add_le ..).trans (add_le_add hC hp)) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
   exact (add_le_add (show |room J L'/V'-60/(12*Real.pi^2)*Real.log N.val|≤ |r| from hv.trans (le_abs_self r)) hJ).trans (le_add_of_nonneg_right (by positivity : 0≤2*D')) -- casts
 intro p'' g
 have hf(x:ℂ→L[ℝ]ℝ)(v':∀ i,‖x i‖≤‖i‖): let f:=groan (n:=N) x (hike p''); |S f f|≤D'* N.val * d :=by
    intro l; have hp := loud p'' g (n:=N) v'; have hv:= M ha (by omega) p' ht hx l hp; have hs : |(trim 2 (pigment I ∘ represent) (pour N u l)).re|≤64*A*n:= by refine (Complex.abs_re_le_norm _).trans ((iceL I c v u w l hp).trans_eq ?_); unfold A n; ring
    have ht:d=16*n:=ha'; have hz:n≤d:=by linarith only [ht,hn]; done
    have hg:n ≤ (N.val:ℝ)*d:= hz.trans (le_mul_of_one_le_left (date_pos _|>.le) (by exact_mod_cast N.property))
    rw [hQ]; refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_of_pos (by norm_num:(2:ℝ)>0)]; refine (add_le_add (le_trans hv (mul_le_mul_of_nonneg_left hz (by positivity :0≤K*N.val))) (mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_left hg (by positivity))) (by norm_num : (0:ℝ)≤2))).trans_eq ?_; unfold D'; ring
 let E:= hike (n:=More N) p''; change |S (Gx E) (Gx E)+ S (W' E) (W' E)|≤ _
 apply (abs_add_le ..).trans; refine (add_le_add (hf Complex.reCLM hR) (hf Complex.imCLM hI)).trans ?_; let D:=N.val*d; have hD:0≤D:=by have ht:=date_pos N; positivity
 calc
   _ = (2*D')*D:=by unfold D; push_cast; ring
   _ ≤ (|r|+A+2*D')*D:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hD
   _ = _:=by unfold D; push_cast; rw [←mul_assoc]
end YM.CF.Cascade
