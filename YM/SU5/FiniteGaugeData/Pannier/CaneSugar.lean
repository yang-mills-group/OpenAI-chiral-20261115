import YM.SU5.FiniteGaugeData.Pannier.Parka
import YM.Next.RANK.Swath
/-! # Carry the stencil through the paid mirrors. Same b even as thermal evidence on opposite spin.
When referring to Ward 'mirror orientation' this use is algebra; no statement of limiting Euclidean covariance. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open Window (mem_Tset pinLift)
open RG Next.Rank.Thirst
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{R ε:ℝ}
section
variable {ι:Type*}[LinearOrder ι][Fintype ι][Nonempty ι]
variable {s S D F:Finset ι}{x y:Ket ι}{P Q: Op ι}{T:UNI ι} {b:Bool}
lemma act_field (x:Ket ι)(h:twist T P= Q): acts T.val (acts P x)= acts Q (acts T.val x) :=by rw [←h,←act_mul,←act_mul,twist_product]
lemma trim_field (h:twist T P= Q)(p:trim P x): trim Q (acts T.val x):=by rw [trim, ←act_field x h,p]
lemma trim_return (h:twist T P= Q)(p:trim Q (acts T.val x)): trim P x:=by
 have ht:twist (star T) Q=P:=h ▸ twist_inv T P
 have hp:=trim_field ht p; change trim P (acts (star T.val) (acts T.val x)) at hp; rwa [act_unit] at hp
lemma paddingT (h:twist T (cutM s)=cutM S)(p:twist T P=Q) : twist T (Fock.padded s P)= Fock.padded S Q:=by
 unfold Fock.padded; rw [map_add,map_sub,map_one,map_mul,map_mul,h,p]
private lemma winUnit {a b: Op ι}(g:twist T a=b)(p:IsUnit a) : twist T (a⁻¹)=b⁻¹:=by
 symm; apply Matrix.inv_eq_right_inv; rw [← g, ←map_mul, (live p).1, map_one]
lemma sparkOn (h:twist T P=Q)(p:twist T (cutM s) =cutM S)(t:twist T (cutM D)=cutM F)(g:IsUnit (Fock.padded s P))(x:Ket ι) :
    acts T.val (sparkUp P s D x)=sparkUp Q S F (acts T.val x):=by unfold sparkUp warmth; rw [act_field _ t,act_field _ h,act_field _ (winUnit (paddingT p h) g)]
lemma handAgainst (T:UNI ι)(P:Op ι)(b:Bool): twist T (hand b P) = hand b (twist T P):=by cases b; rfl; change twist _ (1-P)=1-_; rw [map_sub,map_one]
lemma handTogether (h:twist T P= 1-Q)(b:Bool): twist T (hand b P)=hand (!b) Q:= by rw [handAgainst,h]; cases b; rfl; change (1-(1-Q))=Q; abel
lemma fields_r (h:twist T (cutM S)=1-cutM S)(x y:Ket ι): theta T (handy b S x y)=handy (!b) S (acts T.val x) (acts T.val y):=by
 unfold handy together; rw [theta_add,theta_one,theta_mul]; congr 1
 unfold cardH; rw [←act_field y (handTogether h b)]; cases b
 · change theta T (remove x)*theta T (create _)=_ ; rw [theta_upV,theta_downV]; change ((Complex.I) • create _) * ((-Complex.I) • remove _) = create _ * remove _; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,smul_smul]; simp
 change theta T (create x)*theta T (remove _)=_; rw [theta_upV,theta_downV]; change ((-Complex.I) • remove _) * ((Complex.I) • create _) = remove _ * create _; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul]; simp
end
variable {M:Tulip.Male}{n:Side}{U:Pane n}{b:Bool}
lemma flatAcross (j:ℕ)(p:1≤j):∃ N:ℕ,∀ n:Side,N≤n.val→∀ M:Tulip.Male,∀ (i:Axis)(s:ℤ)(b:Bool), twist (carR i s n) (sp b j M (1:Pane n))= sp (!b) j M (1:Pane n):=by
 obtain ⟨e,h,N,u⟩:= Scroll.radiance j p; refine ⟨N,fun n k M i s b=>?_⟩
 unfold sp; apply handTogether; let U:Pane n:=1
 have he:stir (N:=n) inert (plane i s) U=U:=by
    change fling i s n U=U; rw [fling_eq]; unfold Lattice.pull; funext i; unfold Lattice.Step.read; split; exact inv_one; rfl
 have ht:= funde_f (plane i s) inert (pinLift i) (mirrorX i) U j p M e (u n k) (guard0 h.le); rw [he] at ht; exact ht
lemma flatTset(i:Axis)(s:ℤ): twist (carR i s n) (cutM (Tset n))=1-cutM (Tset n):= tickR (plane i s) inert (pinLift i) (mirrorX i) n
abbrev hyphen (i:Axis)(s:ℤ) (X:Finset (Seat n)):= X.image ((plane i s).anon n)
lemma coal (i:Axis)(s:ℤ)(S:Finset (Seat n))(x:Seat n):((plane i s).anon n x)∈ S ↔ x ∈ hyphen i s S:=by
 constructor; exact fun h=>mem_image.mpr ⟨_,h,fling_there ..⟩; rintro h; obtain ⟨_,p,rfl⟩:=mem_image.mp h; rwa [fling_there]
lemma coal_halo (i:Axis)(s:ℤ)(S:Finset (Seat n))(w:ℕ) : hyphen i s (Lattice.halo w S)=Lattice.halo w (hyphen i s S):= swath_iffHalo ..
lemma coal_flags(i:Axis)(s:ℤ)(t:ℝ)(U:Pane n): hyphen i s (flags t (fling i s n U))= flags t U:= by rw [fling_eq]; exact s_flags (G:=SU.group) ..
lemma Sparse.reflect {w:ℕ}{S:Finset (Seat n)} (p:Sparse w S)(i:Axis)(s:ℤ): Sparse w (hyphen i s S):=by
 intro x hx y hy t; obtain ⟨x,h,rfl⟩:=mem_image.mp hx; obtain ⟨y,v,rfl⟩:=mem_image.mp hy; exact (p x h y v (fun g=> t (g ▸ rfl))).trans_eq (s_sep (Signed.mirror i) (wrap (More n) (2 • (s • step i))) x y).symm
private lemma leaksF (S:Finset (Seat n))(x:Seat n)(i:Axis): (x,i)∈ leaks S ↔ x∈ S ∧ x+step i∈ S:=by simp [leaks]
lemma riotPort (S:Finset (Seat n))(U V:Pane n): Rightful S U V ε↔∀ i∈ leaks S, ‖brand (U i)-brand (V i)‖≤ ε:=by
 constructor
 · intro p i h; let W:=profile U i-profile V i; have hl:= (norm_le_pi_norm W true).trans (p _ h); exact hl -- defeq?
 intro p i h; apply (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (p i h))).2; intro k; cases k; · simp only [Pi.sub_apply,profile,Bool.false_eq_true,ite_false, ←star_sub,norm_star]; exact p i h
 exact p i h
lemma Rightful.land{i₀:Axis}{s₀:ℤ}{S:Finset (Seat n)}{U:Pane n}(p:Rightful (hyphen i₀ s₀ S) U 1 ε): Rightful S (fling i₀ s₀ n U) 1 ε:= by
 apply (riotPort ..).2; rintro ⟨x,i⟩ h
 rw [fling_eq]; obtain ⟨hu,hg⟩:= (leaksF ..).1 h; let s:=Signed.mirror i₀
 let d:=(posDir i).rotate s; let B:=(plane i₀ s₀).anon n; let y:=B x; let S':=hyphen i₀ s₀ S
 have hp:y∈ S':= mem_image_of_mem B hu
 have hv:y+d.vec∈ S':= by
    rw [show y+d.vec=B (x+step i) from ?_]; exact mem_image_of_mem B hg
    unfold y d B Shape.anon; rw [Step.vec_rotate,Step.vec_pos]; unfold affine; change (s.act x+_)+s.act (step i)=s.act (_ + _)+_; rw [Signed.act_add]; abel -- Lean needs namespaces
 change ‖brand (d.read U y)-brand 1‖ ≤ _; generalize e:d=E at *
 obtain ⟨i,b⟩:=E; cases b; · exact (riotPort ..).1 p (y,i) ((leaksF ..).2 ⟨hp,hv⟩)
 change ‖brand (U (y-step i,i))⁻¹ - brand 1‖≤ _; rw [brand_inv, ← inv_one (G:=SU.E), brand_inv,← star_sub,norm_star]; exact (riotPort ..).1 p (y-step i,i) ((leaksF ..).2 ⟨show y-step i∈ S' from (by simpa [sub_eq_add_neg,Step.vec] using hv), by rw [sub_add_cancel]; exact hp⟩)

lemma gauge_frost (S:Finset (Seat n))(g:Seat n→SU.E): twist (tradew n g) (Vo S)=Vo S:=by
 apply Mir.twist_comm; unfold Vo cutM; ext ⟨i,s⟩ ⟨k,l⟩; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul, tradew, modes_at,jump_apply,Equiv.refl_apply]; by_cases h:i=k; subst k; simp only [↓reduceIte]; rw [mul_comm]; simp [h]
lemma gauge_frostT(g:Seat n→SU.E): twist (tradew n g) (cutM (Tset n))=cutM (Tset n):=by
 apply Mir.twist_comm; unfold cutM; ext ⟨⟨i,a⟩,s⟩ ⟨⟨k,b⟩,l⟩; simp only [Matrix.mul_diagonal,Matrix.diagonal_mul, tradew, mem_Tset,jump_apply,Equiv.refl_apply]; by_cases h:(i,a)=(k,b); rw [Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; simp only [↓reduceIte]; rw [mul_comm]; simp only [if_neg h,zero_mul,mul_zero] -- fragile
lemma pickAgree (S:Finset (Seat n))(f g:Seat n→SU.E)(h:∀ x∈ S,f x=g x):
    (tradew n g).val * Vo S=(tradew n f).val * Vo S:=by
 ext ⟨i,u⟩ ⟨k,l⟩; unfold Vo cutM; simp only [Matrix.mul_diagonal,modes_at,tradew,jump_apply,Equiv.refl_apply]; by_cases he:i=k
 · subst i; simp only [↓reduceIte]; split
   next p=>rw [h _ p]
   next _=> simp
 simp only [if_neg he,zero_mul]
lemma agreePick (S:Finset (Seat n))(f g:Seat n→SU.E)(h:∀ x∈ S,f x=g x){x:Ket (Single n)}(w:withinM (modesIn n S) x):acts (tradew n g).val x=acts (tradew n f).val x:=by nth_rw 1 [←w]; rw [←act_mul,pickAgree S _ _ h,act_mul,w]
lemma despin (a:Axis)(s:ℤ)(g:Seat n→SU.E)(x:Ket (Single n)):
    acts (tradew n (g ∘ (plane a s).anon n)).val (acts (carR a s n).val x)=acts (carR a s n).val (acts (tradew n g).val x):=by
 have hp : carR a s n*tradew n g=tradew n (g ∘ (plane a s).anon n)*carR a s n:= Nacre.envoy (plane a s) (pinLift a) g; rw [←act_mul,←act_mul]; let hp':=(carR a s n); change acts (tradew n (g ∘ (plane a s).anon n)*hp').val _=acts (hp'*tradew n g).val _; exact congrArg (fun U:UNI _=>acts U.val x) hp.symm
lemma coverSense {S:Finset (Seat n)}{t:Seat n→SU.E}{x:Ket (Single n)}:withinM (modesIn n S) (acts (tradew n t).val x)↔ withinM (modesIn n S) x:=⟨trim_return (gauge_frost ..),trim_field (gauge_frost ..)⟩
lemma sense {t:Seat n→SU.E}{x:Ket (Single n)}: trim (hand b (cutM (Tset n))) (acts (tradew n t).val x) ↔ trim (hand b (cutM (Tset n))) x :=by
 have hp:twist (tradew n t) (hand b (cutM (Tset n)))=hand b (cutM (Tset n)):=by rw [handAgainst,gauge_frostT t]
 exact ⟨trim_return hp,trim_field hp⟩
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.flatAcross
#print axioms YM.CF.Pannier.Chancel.Rightful.land
