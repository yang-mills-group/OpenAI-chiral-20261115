import YM.CF.Tap.Gamin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open NormedSpace Matrix Tenant Branch
open Proa
variable {N:Side}
abbrev ActX{N:Side}:=Chin N → CrownX (N:=N)
def pivot{N:Side}(P:ActX (N:=N))(Z:CrownX (N:=N))(x:Chin N):CrownX (N:=N):= (1-P x)*Z*P x
abbrev cuter (Z:CrownX (N:=N)):ActX (N:=N):= fun _=> exp Z-1
def blush(P:ActX (N:=N))(Z:CrownX (N:=N))(x:Chin N): CrownX (N:=N):= charmE (P x) (exp Z)-charmE (tickA N) (exp Z)
def rub(P:ActX (N:=N))(Z:CrownX (N:=N))(x:Chin N): CrownX (N:=N):=trick (P x) Z (exp Z)
def rouge(P:ActX (N:=N))(Z:CrownX (N:=N)):ActX (N:=N):= pivot P Z+ rub P Z
def seize(S T U:ActX (N:=N))(v:Bool)(x:Chin N):CrownX (N:=N):= if v then U x + pale S x*(1+ U x) else T x- S x*(1+ T x)
def velvet(P:ActX (N:=N))(Z:CrownX (N:=N))(v:Bool):= seize (rouge P Z) (cuter Z) (cuter (-Z)) v
def pol(P:ActX (N:=N))(Z:CrownX (N:=N))(p q:Bool) (x) := Proa.sprig p (P x) * velvet P Z q x * Proa.sprig q (P x)
lemma punct (P:ActX (N:=N))(Z:CrownX (N:=N))(v:Bkg (More N))(q:Bool)(h: IsStarProjection (P (profile v)))(k:‖cern (P (profile v)) (exp Z)‖<1)(hp:star Z=Z) : let x:=profile v; let B:=P x; let F:= exp Z; let D:= exp (-Z); let S:= Bop B F
 star D * F=1 ∧ rouge P Z x=S ∧ pol P Z q q x=elbow B S F D q ∧ pol P Z (!q) q x= localTax B S F D q:=by
 letI : NormedAlgebra ℚ (Op (Single N)):= NormedAlgebra.restrictScalars ℚ ℂ (Op (Single N)); intro x B F D S
 have hh : star D * F=1:=by unfold D F; rw [star_exp,star_neg,hp,mul_eq_one_comm]; exact wind_inv _ -- tune
 have he:rouge P Z x=S:= (knot_p B Z F D h hh k).symm
 have hz : velvet P Z q x=liftJet q S F D-1:=by
    unfold velvet seize pale; rw [show ice x=x from ?_,he]; swap; exact ice_pr v -- tune
    unfold liftJet cuter; cases q; swap
    · change D-1+ star S * (1+(D-1))=star (1+S)*D-1; rw [add_sub_cancel,star_add,add_mul,star_one,one_mul]; abel
    change F-1-S*(1+(F-1))=(1-S)*F-1; rw [add_sub_cancel,sub_mul,one_mul]; abel
 let Q:=Proa.sprig q B; let T:=Proa.sprig (!q) B; have hg: IsStarProjection Q:=by unfold Q Proa.sprig; cases q; exact h.one_sub; exact h
 have hx:T=1-Q:=by unfold T Q Proa.sprig; cases q <;> simp
 rw [pol,pol,hz]; change _∧ _∧ Q* _ * Q= Q* _ * Q-Q∧ T* _ * Q=T* _ *Q; refine ⟨hh,he,?_,?_⟩
 · rw [mul_sub,sub_mul,mul_one,hg.isIdempotentElem.eq]
 rw [mul_sub,sub_mul,mul_one,hx]; have hw:(1-Q)*Q=0:=by rw [sub_mul,one_mul,hg.isIdempotentElem.eq,sub_self]
 rw [hw, sub_zero]
lemma treasury(j:ℕ)(hp:1≤j):∃ a R e δ:ℝ,0<a∧0<R∧0<e∧0<δ∧ ∃ m:ℕ,∀ N:Side,m≤N.val→∀ y:Op Slot,Mind y→ ‖y‖≤δ→∀ M:Male, let Z:= -(plankP N y); let P:= funde j M N;
 Solo a (R*‖y‖^2) (rub P Z) e ∧ Solo a (R*‖y‖) (rouge P Z) e ∧ Solo a (R*‖y‖) (blush P Z) e ∧ (∀ v u, Solo a (R*‖y‖) (pol P Z v u) e) ∧ Commute (tickA N) (exp Z) ∧ star Z=Z ∧ ∀ x∈Openc (More N) e, ‖cern (P x) (exp Z)‖ <1 ∧ ‖cern (tickA N) (exp Z)‖<1:=by
 obtain ⟨a,r,e,u,v,w,m,H⟩:= funde_s j hp
 let D:=Aop-(1/2:ℂ) • 1; let C:=max r (max (wingRent D a) (wingRent Aop a)); have hx:0<C:= v.trans_le (le_max_left ..)
 obtain ⟨δ,R,hδ,hR,L⟩:=starsE C hx a u.le
 let T:=Real.exp a+C; have hT:0<T:=add_pos (Real.exp_pos _) hx
 let η:=min δ 1; let d:=4*T*C*C+R; let y:=R+2*d*(Real.exp a+R); let S:=4*T*T*y
 have hy:0<y:=by unfold y d; positivity
 have hD:0<d:=by unfold d; positivity
 have hS:0<S:=by unfold S; positivity
 refine ⟨a,d+2*R+S,e,η,u,by positivity,w,lt_min hδ one_pos,m,?_⟩
 intro n hg A p q M Z P; let t:=‖A‖; have hv: Solo a C P e:=(H M n hg).books (le_max_left ..)
 have ht:Solo a (C*t) (fun _:Chin n=> -Z) e:=by
    rw [show -Z=plankP n A by simp [Z]]; exact (plateV n a e D A p.firm).books (by apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact (le_max_left ..).trans (le_max_right ..))
 have he:Solo a (C*t) (fun _:Chin n=>Z) e:=by simpa using ht.minus
 have hk:t≤δ:=q.trans (min_le_left ..); have hi:t≤1:=q.trans (min_le_right ..)
 have hu := L n e t (norm_nonneg _) hk Z P he hv; have hy':= (L n e t (norm_nonneg _) hk (-Z) P ht hv).2.2.1
 have hf :=L n e t (norm_nonneg _) hk Z (fun _=> tickA n) he ((soil_tick a e).books ((le_max_right ..).trans (le_max_right ..)))
 have ht0 : Solo a (Real.exp a) (fun _:Chin n=>1) e:= Crown.ident ..; have ht1:= ht0.sub hv; have ht:0≤t:=norm_nonneg _
 have hw:Solo a (d*t) (rouge P Z) e:=by unfold rouge pivot; apply ((((ht1.product he u.le).product hv u.le)).plus hu.2.1).books; change 2*(2*(T*(C*t))*C)+R*t^2≤_; unfold d; rw [add_mul (4*T*C*C)]; apply add_le_add; apply le_of_eq; ring; exact mul_le_mul_of_nonneg_left (by nlinarith) hR.le
 have h:star Z=Z:=by unfold Z; rw [star_neg,plank_h p.adj]
 have hq:Commute (tickA n) (exp Z):=by letI : NormedAlgebra ℚ (Op (Single n)):= NormedAlgebra.restrictScalars ℚ ℂ (Op (Single n)); exact (Commute.exp_right (y:=Z) ((plank_tick A).neg_right))
 refine ⟨hu.2.1.books (by gcongr; unfold d; nlinarith), hw.books (by gcongr; linarith),(hu.1.sub hf.1).books (show _≤_* t by rw [show R*t+R*t=2*R*t by ring]; gcongr; linarith),fun v u'=>?_,hq,h,fun x hx=>⟨hu.2.2.2 x hx,hf.2.2.2 x hx⟩⟩
 have hj : Solo a (y*t) (velvet P Z u') e:=by
    have he:R*t≤R:=mul_le_of_le_one_right hR.le hi
    have hg: R*t+ 2*(d*t*(Real.exp a+ R*t))≤ y*t:=by calc
      _ ≤ R*t+ 2*(d*t*(Real.exp a+R)):=by gcongr
      _ =_:=by unfold y; ring
    unfold velvet seize; cases u'
    · exact ((hu.2.2.1.sub (hw.product (ht0.plus hu.2.2.1) u.le)).books hg)
    exact (hy'.plus ((solo_opp hw).product (ht0.plus hy') u.le)).books hg
 have hb(v:Bool): Solo a T (fun x=>Proa.sprig v (P x)) e:=by cases v; exact ht1; exact hv.books (by unfold T; have:=Real.exp_pos a; linarith)
 apply (((hb v).product hj u.le).product (hb u') u.le).books; calc
   _ =S*t:=by unfold S; ring
   _ ≤_:=by gcongr; linarith
end YM.CF.Tap
