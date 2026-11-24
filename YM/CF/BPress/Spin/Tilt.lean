import YM.CF.BPress.Spin.Trans
import YM.CF.BPress.Spin.Energy
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Lattice SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Paint Eye Nacre Laic Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra

-- use shear argument separate, B purchases pay Aim and shelf.
section au
variable {I : Type}[Fintype I][LinearOrder I][Nonempty I] {A T K : Op I} {e η v :ℝ}
def scraw (A T:Op I)(u:ℝ):= A+u • T
def tilt (A T:Op I)(u:ℝ):= Trans.beam A (scraw A T u)
abbrev zom (T:Op I)(u:ℝ):= 1+u • T
lemma switch_s (h:TagG A T)(u:ℝ): scraw A T u=zom T u*A:=by unfold scraw zom; rw [add_mul,Algebra.smul_mul_assoc,h.2,one_mul]
lemma tempo (p:IsStarProjection A)(h:TagG A T)(u:ℝ): Trans.gram A (scraw A T u)= 1+star (u • T)*(u • T) :=by
 have he:A*(u • T)=0:=by rw [Algebra.mul_smul_comm,h.1,smul_zero]
 have hv:= congrArg star he; rw [star_mul,p.isSelfAdjoint,star_zero] at hv
 unfold Trans.gram scraw; rw [star_add,p.isSelfAdjoint, add_mul,mul_add,mul_add,p.isIdempotentElem.eq,he,hv]; abel
lemma tiltR (p:IsStarProjection A)(h:TagG A T)(u:ℝ): Trans.Ready 1 A (scraw A T u):=by
 refine ⟨p,?_,one_pos,?_ ⟩; rw [switch_s h,mul_assoc,p.isIdempotentElem.eq]; rw [tempo p h, one_smul]; exact le_add_of_nonneg_right (star_mul_self_nonneg ..)
lemma zeroT (p:IsStarProjection A)(T:Op I):tilt A T 0=A:= by rw [tilt,scraw,zero_smul,add_zero]; exact (Trans.Ready.atSelf p).2
lemma tiltT (u:ℝ)(p:IsStarProjection A):tilt A 0 u=A:= by rw [tilt,scraw,smul_zero,add_zero]; exact (Trans.Ready.atSelf p).2
lemma rotate_tilt(p:IsStarProjection A)(h:TagG A T)(u:ℝ)(V:UNI I): tilt (twist V A) (twist V T) u=twist V (tilt A T u):=by rw [tilt, show scraw (twist V A) (twist V T) u= twist V (scraw A T u) by simp [scraw], (tiltR p h u).shine]; rfl

lemma tilt_near(p:IsStarProjection A)(h:TagG A T){ε:ℝ}(t:ε≤1)(u:‖T‖≤ε)(s:‖v‖≤1): ‖tilt A T v-A‖≤ 4*ε:=by
 let E:=v • T; let B:=scraw A T v; let D:= (Trans.gram A B)⁻¹; let f:= tiltR p h v; have hd : ‖D‖≤1:=by simpa only [inv_one] using f.boundG
 have hv:0≤ε:= (norm_nonneg _).trans u
 have ha : ‖E‖≤ε:=by unfold E; rw [norm_smul]; exact ((mul_le_of_le_one_left (norm_nonneg _) s)).trans u
 have hx := IsStarProjection.norm_le _ p
 have he : ‖D-1‖≤ε:= by
    have hg : D*(1+star E*E)=1:=by rw [←tempo p h v]; exact (live f.live_G).2
    rw [mul_add,mul_one] at hg
    rw [show D-1= -(D*(star E*E)) from by rw [←hg]; abel, norm_neg]
    apply ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) hd)).trans; apply (norm_mul_le ..).trans; rw [norm_star]; exact (mul_le_of_le_one_left (norm_nonneg _) (ha.trans t)).trans ha
 have ho: ‖star B‖≤2:=by rw [norm_star]; apply ((norm_add_le ..).trans (add_le_add hx (ha.trans t))).trans_eq; norm_num
 have hk:star B-A=star E:=by unfold B scraw; rw [star_add,p.isSelfAdjoint,add_sub_cancel_left]
 have hi:‖A*D‖≤1:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans hd)
 rw [show tilt A T v-A= E*D*star B+ A*D*(star B-A)+A*(D-1)*A from (by
    change B*(D*_) -_= _; rw [←mul_assoc]; nth_rw 1 [show B=A+E from rfl]; rw [add_mul,add_mul,mul_sub,mul_sub A,mul_one,sub_mul,p.isIdempotentElem.eq]; abel)]
 have h₁:‖E*D*star B‖≤ε*2:= (norm_mul_le ..).trans (mul_le_mul ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hd).trans ha)) ho (norm_nonneg _) hv)
 have h₂: ‖A *(D-1)* A‖ ≤ ε:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hx).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hx).trans he)))
 have h₃: ‖A*D*(star B-A)‖≤ε:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hi).trans (by rwa [hk,norm_star]))
 exact ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h₁ h₃)) h₂)).trans_eq (by ring)
lemma wash_approx {B:Op I}(t:‖A-B‖≤ v)(p:‖K‖≤1): ‖wash A K-wash B K‖≤2*v :=by rw [show wash A K-wash B K=wash (A-B) K from by unfold wash; rw [cc_sub,mul_sub,sub_mul]; abel,wash,two_mul]; exact (norm_sub_le ..).trans (add_le_add ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) p).trans t)) ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) p).trans (by rwa [norm_cc]))))
end au
section purchase
variable {M:Jill.Male} {P Q W:Pledge}{η d k:ℝ}
def Ts {N:Side} (F:Aim N)(x:Op (Single N))(U:Bkg (More N)):= Kennel.capT x (F.den U)
def priceS(P Q W:Pledge):=((unary.plus P).times (aimPrice Q W)).times P
lemma CostS (M:Jill.Male){N:Side}{j:ℕ}(p:Shelf N d j P) (R:Aim N)(h:R.toll Q.rate W.rate Q.price W.price) : Form.Comes (AtW N d) (priceS P Q W) (fun x=>Ts R (spar j M x.val) x.val):=by
 let F:= AtW N d; have hu : Form.Comes F (aimPrice Q W) (R.den ∘ Subtype.val):=Form.pulls (aim_cost R h) Subtype.val continuous_subtype_val (fun _ _ _=> le_rfl)
 have hx:=p.entries M; exact Costs.mul (Costs.mul (Costs.sub Costs.one hx) hu) hx

def linePrice (P W:Pledge):Pledge:= P.plus ((unary.scales 1).times W)
-- on any path; tune needn't control u when a separate tune for constant path, `u` inside eval otherwise.
lemma buy_tilt (P W:Pledge)(p:0≤k) : ∃ U:Pledge, ∀ {I Y D:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]
 {b:Stage Y I D Empty}{A T:Raw D I}{v:D→ℝ}, Capacity b k→ Trans.Tune b v 1→Costs P b A→ Costs W b T→(∀ x,IsStarProjection (A x))→(∀ x,TagG (A x) (T x))→
 Costs U b (fun x=>tilt (A x) (T x) (v x)) :=by
 obtain ⟨U,h⟩:= Trans.value _ (C:=k) (show 0<(1:ℝ) by norm_num) p P (linePrice P W) -- tune
 refine ⟨U,?_⟩; intro I Y D _ _ _ _ _ _ b A T v J t L K hA hT
 have hx := h J (fun x=> tiltR (hA x) (hT x) (v x)) L (Costs.plus L (Trans.conducts t K))
 exact hx.2.2.2
-- eq:B-shear and Lspeed.
theorem purchase_speed (j:ℕ)(g:1≤j)(W Q:Pledge)(h:0<η) (u:0<k) : ∃(d₀ r:ℝ)(v:ℕ)(P:Pledge), 0<d₀∧0<r∧∀N:Side,v≤ N.val→∀ d:ℝ,0<d→d≤d₀→
 Shelf N d j P ∧ ∀ x:OpenW N d, ∀ M:Jill.Male, ∀ R:Aim N,R.toll W.rate Q.rate W.price Q.price→ let A:=spar j M x.val; let T:=Ts R A x.val
 ‖T‖≤ k ∧ ∀ U:Paint (More N), MatPlan U→ Bend U x.val r→∀t:ℝ, ‖t‖≤1→ ‖wash (tilt A T t) (coupling U)‖≤η :=by
 let a:=η/2; have ha:0<a:=half_pos h; let e:=min k (min 1 (a/8)); have he:0<e:=lt_min u (lt_min one_pos (by positivity)); obtain ⟨d₁,N,P,p,H⟩:=symbolHere j g; obtain ⟨d,N',w,K⟩:=invest W Q he; obtain ⟨r,M,v,L⟩:= Crystal.rawSpeed P ha j g
 refine ⟨min r (min d d₁),r,N+N'+M,P,lt_min v (lt_min w p),v,?_⟩; intro N₀ z Y Yh co; have hX:= co.trans (min_le_right ..); let J:= H N₀ (by omega) Y (hX.trans (min_le_right d d₁)); refine ⟨J,?_⟩; intro x M R ht A T
 have hA:=J.proj M x; have hp:= IsStarProjection.norm_le _ hA; have hQ:= IsStarProjection.norm_le _ hA.one_sub; have he' : ‖T‖≤e:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) hQ).trans (K (N:=N₀) (by omega) R ht _ (x.property.shrink (hX.trans (min_le_left d d₁)))))))
 refine ⟨he'.trans (min_le_left ..),fun U v Hv t T'=>?_⟩
 have hg : ‖wash A (coupling U)‖≤a:= L N₀ (by omega) Y Yh (co.trans (min_le_left ..)) J _ x.property M U v Hv
 apply (norm_le_norm_sub_add _ (wash A (coupling U))).trans; apply le_trans (add_le_add (wash_approx (tilt_near hA (tag_g (R.den x.val) hA) (le_trans (min_le_right k _) (min_le_left ..)) he' T') ((CStarRing.norm_of_mem_unitary (Paint.unit U v)).le)) hg) _; have hx : e≤ a/8:=(min_le_right ..).trans (min_le_right ..); unfold a at *; linarith
end purchase
end YM.CF.BPress.Spin
