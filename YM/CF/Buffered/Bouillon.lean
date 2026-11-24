import YM.CF.Buffered.Payings
import YM.CF.Buffered.Ranged
import YM.CF.Gall.Act
/-! Contraction with extra, arbitrary basis letters on the right. At tile scales,
local truncation tolerances pay powers (not just additive volume-independent errors).
Difference conditions packaged for use in the toron furniture estimate.
`G (Dofu ...) x` MARK x after Wick substitution: certify via Dress. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Cache
open Function Filter Metric Fock Finset Flare Kea Gall Spire Scroll Peaks Fir Jill Dial Lat Lattice Emu Onyx SU Phase Tulip Rush Cube Vault Paige Laurent
open Glaze
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Type*} [Fintype n] [LinearOrder n]
variable {m:Type*}
variable {L:Op n}{x y:FC n}
def Dress (L:Op n) (x y:FC n):= x*quant (1+L)=quant (1+L)*y
lemma Dress.zero (L:Op n): Dress L 0 0:=by simp [Dress]
lemma Dress.one (L:Op n): Dress L 1 1:=by simp [Dress]
lemma Dress.l (p:Dress L x y)(v:ℂ):Dress L (v • x) (v • y):=by unfold Dress; rw [Matrix.smul_mul,Matrix.mul_smul,p]
lemma Dress.mul {u v:FC n}(p:Dress L x y) (q:Dress L u v) :Dress L (x*u) (y*v):=by unfold Dress; rw [mul_assoc,q,←mul_assoc,p,mul_assoc]
lemma Dress.add {u v:FC n}(p:Dress L x y) (q:Dress L u v) :Dress L (x+u) (y+v):=by unfold Dress; rw [mul_add,add_mul,p,q]
lemma Dress.sub {u v:FC n}(p:Dress L x y) (q:Dress L u v) :Dress L (x-u) (y-v):=by unfold Dress; rw [mul_sub,sub_mul,p,q]
lemma Dress.sum {U V:m→FC n}(s:Finset m)(p:∀ i∈s,Dress L (U i) (V i)): Dress L (∑ i∈s,U i) (∑ i∈s,V i):=by unfold Dress; rw [mul_sum,sum_mul]; exact sum_congr rfl p
lemma Dress.cruise (A B:m→ FC n) (g:∀ i,Dress L (A i) (B i)) (l:List m): Dress L (rollC A l) (rollC B l) := by induction l with| nil=>exact Dress.one _| cons i l ih=>exact (g i).mul ih
lemma depart {P Q T D K:Op n} (v: Clad P Q T D K)(t:Reader0 n): Dress (laneP Q T K) (ton t) (iceT (laneP Q T K) t):= mixC v t -- namespace
open Thera
lemma Dress.emit {P Q T D K:Op n}{p q:Wave n}(u:Clad P Q T D K)(hp:Sea P p)(hq:Sea Q q)(v:Dress (laneP Q T K) x y) : inner ℂ q (acts (x*quant T) p)=skyGlow q T p * inner ℂ q (acts y q):=by
 let B:=quant (1+laneP Q T K); let f:=skyGlow q T p; have he:acts (quant T) p=f • acts B q:= by rw [broomstick u p q hp hq,tallied _ u.reef]
 rw [act_mul,he,map_smul,inner_smul_right,←act_mul, v,act_mul, ivory u q hq]
variable {N:Side}{j d₀:ℕ}{d:Candle}{u Y D Z t r:ℝ}
private lemma mateV_basis (N:Side) : ∃ c:ℂ,‖c‖=1∧mateK N=c • basisKet (Tset N):= by
 let b:=Tset N; let v:=mateK N; let t:=basisKet b; let c:= inner ℂ t v; have hs:Sea (cutM b) v:= (touchP N) ▸ tickB N
 have hx:v=c • t:=by nth_rw 1 [←hs.1]; rw [cutLine, cut_oneAct]; unfold t c; rw [basis_inner]
 refine ⟨c,?_,hx⟩; have ht:= hs.2; rw [hx,norm_smul] at ht; simpa [t,basisKet] using ht
lemma mateV_emit (A:FC (Single N)) : inner ℂ (mateK N) (acts A (mateK N))=A (Tset N) (Tset N):=by
 obtain ⟨c,h,v⟩:=mateV_basis N; rw [v,map_smul,inner_smul_right,inner_smul_left]; change c*(star c * _)= _; rw [←mul_assoc,show c*star c=1 from ?_,one_mul,basis_inner,basis_act]; exact (mul_comm ..).trans (scale_unit_self h) -- tune

abbrev Ice (P:Op n) (x:WordX n):= iceT P (artW x)
lemma skim_roll (L:Op n) {e:ℝ}(b:0≤e)(p:Billow e L)(X:List (WordX n)): ‖rollC (Ice L) X‖≤ (e+1)^X.length:=by
 induction X with
 | nil=> simp [rollC]
 | cons i X ih=> rw [rollC,List.map_cons,List.prod_cons]; refine (norm_mul_le ..).trans ((mul_le_mul (Gall.bill_p p i) ih (norm_nonneg _) (by linarith)).trans_eq (pow_succ' ..).symm)
lemma float_roll [Fintype m][DecidableEq m](S:n→m)(P:Op n)(X:List (WordX n)) :ChangeBill S X.length (rollC (Ice P) X) := by induction X with| nil=>exact change_one S 0| cons i X ih=>simpa only [List.length_cons,rollC,List.map_cons,List.prod_cons,Ice,add_comm 1] using (change_ice S P (artW i)).mul ih
variable [Fintype m][DecidableEq m]
-- coupons paid at each toron. later structure closeness suffices for production.
lemma royalty {N:Side} (U:Single N→m){q:Wave (Single N)}{P T D' K:Op (Single N)} (u': Clad P (tickA N) T D' K)(hq:Sea P q) (x y z:m→FC (Single N)) (p:0 ≤ u) (b:1 ≤ Y)(g: ∀ i, Dress (laneP (tickA N) T K) (x i) (y i+z i)) (e:∀ i,Sector (variety U i) false (y i))(v: ∀ i,ChangeBill U d₀ (z i))(f:Pot (Tset N) y z u Y d₀)(t:0 ≤ Z)(c:Billow Z (laneP (tickA N) T K))
 (l : List m)(a:l.Nodup) (w: List (WordX (Single N))) : ‖inner ℂ (mateK N) (acts ((rollC x l * rollC Gall.pack w)*quant T) q)‖ ≤ ‖skyGlow (mateK N) T q‖*( (4*u)^l.length*(Y*(Z+1))^w.length) := by
 let T':=laneP (tickA N) T K; let B:=rollC (Ice T') w
 have ht:= (Dress.cruise x (fun i=> y i+z i) g l).mul (Dress.cruise Gall.pack (Ice T') (fun i=>depart u' (artW i)) w)
 rw [ht.emit u' hq (tickB N),norm_mul,mateV_emit]; refine mul_le_mul_of_nonneg_left ((royalties e p b l a f v (float_roll U T' w) (skim_roll T' t c w)).trans_eq ?_) (norm_nonneg _)
 rw [mul_assoc,mul_pow Y]

lemma waive (H:1≤j)(p:0<r) : ∃ Z G C:ℝ,0<Z∧0<G∧0<C∧∀ (N:Side) (m:Type*) [Fintype m][DecidableEq m],Even N.val→ r * Ember.pinch N^2≤1/8 →∀ (U: Single N→m) (d:Candle)(F:Slide N d)(M:Jill.Male)(x:Wave (Single N)),Sea (Dofu N (field F j M)) x→∀ (D:m→ FC (Single N))(u a:ℝ)(k:ℕ), 0 ≤ u → 1 ≤ a → (∀ (T D' K:Op (Single N)),Clad (Dofu N (field F j M)) (tickA N) T D' K →∀ V:Stag N→Peb, Dofu N V=laneP (tickA N) T K →(∀ i:Slot,FormU (F.u i) j M r C (trackF F V i))→∃ y z:m→ FC (Single N),(∀ i,Dress (Dofu N V) (D i) (y i+z i)) ∧ (∀ i,Sector (variety U i) false (y i))∧ (∀ i,ChangeBill U k (z i))∧ Pot (Tset N) y z u a k) →∀ l:List m,l.Nodup → Yep (a*(Z+1)) (acts (star (rollC D l)) (mateK N)) x (G*iceK j F M r*(4*u)^l.length) := by
 obtain ⟨l,h⟩:=risky_card j H r p; let w:= l*4+1; let C:ℝ:=(w+1:ℝ)*heave r; have hx:= heave_p r; have hc:heave r ≤ C:= le_mul_of_one_le_left hx.le (by simp)
 obtain ⟨c,hb,R⟩:=rod j C hc p; obtain ⟨B,u,U⟩:=octant j H p hc; obtain ⟨v,hv,X⟩:=bead_bound w
 let V':= c^2*Real.pi; have hp:0<V':=by unfold V'; positivity
 obtain ⟨V'',hV,X'⟩:= Gall.fame H p hp
 refine ⟨V'',v*B,V',hV,mul_pos hv (zero_lt_one.trans_le u),hp,?_⟩
 intro N m _ _ w' l' E b s M i k D v₀ a₀ k₀ p₀ q₀ K L hy₀ y; let T:=risky s j M r; let Y:= (4*v₀)^L.length*costs (a₀*(V''+1)) y; have hy:0≤Y:=by unfold Y Gall.costs; have h:=zero_lt_one.trans_le q₀; positivity
 let z:=iceK j s M r; let D':=rollC D L; let M':=mateK N; have hz:0<z:=ice_p _ _ _ p
 rw [act_inner,←act_mul, Flare.wage _ i (heave r* Ember.pinch N) T w (by unfold T w; have h:= h N w' b s M; omega)]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun j' => |bead w (-1) j'| * (B*z*Y)) ?_).trans ?_)
 · intro i' hi; let t:=(i'+1:ℝ)*heave r; have ht:t∈ Set.Icc (heave r) C:=by refine ⟨le_mul_of_one_le_left hx.le (by simp),mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ (mem_range.mp hi).le) hx.le⟩
   let F:=portT s M j r t; let W:= Flare.mateV T (t* Ember.pinch N); rw [norm_mul,Complex.norm_real, Real.norm_eq_abs,show openW T (_ *(heave r* Ember.pinch N))=F from (by unfold F portT; rw [←mul_assoc])]; refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
   obtain ⟨D₀,v,e,Z',W'⟩:=R N w' l' b s M t ht; have hg:= torn s w' j M D₀ F W v; let V:= tilt F D₀; have hs:Dofu N V=_:=tall_s F D₀; have hT:= attire v w' p hb e W'; obtain ⟨A, Z, l,d₀,d₁,X⟩:=K _ _ _ hg V hs hT; rw [hs] at l; have hL: Billow V'' (laneP (tickA N) (Dofu N F) (Dofu N D₀)):= hs ▸ (fun i=> X' V s w' hT i);
   refine le_trans (royalty E hg k D A Z p₀ q₀ l d₀ d₁ X hV.le hL L hy₀ y) ?_
   exact mul_le_mul_of_nonneg_right (U _ w' l' b s M t ht.1 ht.2 i k) hy
 rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (X _ (by norm_num)) (mul_nonneg (mul_nonneg (zero_le_one.trans u) hz.le) hy)).trans_eq (by unfold z Y; ring)
#print axioms waive
end YM.CF.Buffered.Cache
