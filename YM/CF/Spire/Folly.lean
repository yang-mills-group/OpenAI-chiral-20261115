import YM.CF.Spire.Thick
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Scroll Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Phase.Sample Broc Branch Jet MeasureTheory Acorn
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {n Y D:Type}[LinearOrder n][Fintype n][Fintype Y][DecidableEq Y][TopologicalSpace D]
lemma narV(X:Master D Y)(O:n→Y)(S: Seal Y)(A:D→FC n)(a w h K:ℝ)(p:w≤a)(g:0≤h)(l:Carries X O S a h A K):Carries X O S w h A K:=by
 obtain ⟨I,c,T,hx,H,f⟩:=l; refine ⟨I,c,T,hx,le_trans (sum_le_sum fun i _=>?_ ) H,f⟩; unfold Acorn.bill; gcongr; exact (hx i).1.pos; exact rent_up p _
variable {L A m B:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ} {P: Grasp Y B e}(K:Pearl P)(H:Stamped j L ho Y)(p:0<e)(q:1≤j)
include H K p q
lemma endeavor(R:Repair j)(n:ℕ)(c:ℝ)(k:1≤c)(t:e≤R.d)(s:P.baseline≤R.d):∃ a v:ℝ,0<a ∧ 0<v∧∀ m:Side,R.n≤ (CSide m B).val→ P.roundZ≤(CSide m B).val→∀ M:Tulip.Male,∀ S:Broc.Table m B,Grove (terr _) S→∀ z:ℝ,1≤z→ ∃ A:Castle m B e S→ FC (Iota (idrat (CSide m B))), (∀ x,acts (A x) (graft (m:=m) (idrat (CSide m B)) P (x.val false) M) = graft (m:=m) (idrat (CSide m B)) P (x.val true) M) ∧ Carries (landX n c S e) (tempo (idrat (CSide m B)) 1).home S a z A (Real.exp (v*S.card*z^2)):=by
 obtain ⟨a,v,ha,hv,Q⟩:=compareX P n c k R t s
 obtain ⟨d,w,hd,x,Y⟩:=cycle K H p q n c k
 let α:= min a d; have hα:0<α:=lt_min ha hd
 let L:= v+Acorn.worth n*(1+2*w); have he: 1≤Acorn.worth n:= one_w _
 have hl:0<L:=by unfold L; positivity
 refine ⟨α,L,hα,hl,fun m u r M S l z g=>?_⟩
 let X:=landX n c S e; let O:=(tempo (idrat (CSide m B)) 1).home; let U(i:Bool)(x:Castle m B e S): CapX m B e:=⟨x.val i,x.property.1 _⟩; let W:= newX (soar m B e) (aether n c e m B) n
 have hT(i:Bool): Cop W X (U i):=⟨rfl,rfl,((continuous_apply _).comp continuous_subtype_val).subtype_mk _,fun S x y t=> t _,fun E _ _ _ V h f t x p=>t x p _⟩ -- tune
 let F(i:CapX m B e):= candle m B (P.cost m M) i.val; let T:=fun i=> F (U false i)-F (U true i)
 have hx :S.Nonempty:= by cases l<;> simp
 obtain ⟨A,h,H⟩:=Q m u r M S l z g
 have hp:0≤z:=zero_le_one.trans g
 have hu:Wallet W α w F:= flash_d ((Y _ r M).reserve (min_le_right ..) le_rfl)
 have hy:Carries X O S α z (fun i=>Complex.exp (T i) • 1) (Real.exp (Acorn.worth n*(S.card*(2*w)))):=by
    have hx': Cash X S α T (S.card*(2*w)):= Wallet.tech (Z:=X) l hx (hT true) (hT false) ?_ hα.le hu
    · exact (hx'.embark hα.le hx l).silent (A:=Complex.exp) (f:=T)
    intro R h x; change Agrees (↑R) (x.val true) (x.val false)
    have he:R⊆Sᶜ:= Disjoint.le_compl_left h -- tune
    exact fun i q p=> (x.property.2 i (he q) (he p)).symm
 let Gx (x):FC (Iota (idrat (CSide m B))):=(Complex.exp (T x) • 1)*A x
 have hx':Carries X O S α z Gx _ :=hy.product (narV _ _ _ _ _ α _ _ (min_le_left ..) hp H) hx hα.le hp
 refine ⟨Gx,fun x=>?_,hx'.more ?_⟩
 · unfold Gx; rw [graft_v,graft_v, act_mul,map_smul, act_smul]; change _= _ • neat P m M (x.val true); rw [show acts _ (adjust (m:=m) P _ _ _)=_ from h x]; rw [act_one,smul_smul,←Complex.exp_add]; congr 2; unfold T F U; dsimp only; abel
 change Acorn.worth n * Real.exp _ * _ ≤ _
 let t:=Acorn.worth n
 have hp:1≤(S.card:ℝ):=by exact_mod_cast Finset.card_pos.mpr hx
 calc
   _ ≤ Real.exp t * Real.exp _ * Real.exp (v*S.card*z^2):= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by change t≤Real.exp t; linarith [Real.add_one_le_exp t]) (Real.exp_pos _).le) (Real.exp_pos _).le -- tune
   _ ≤ _:=by
        rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_le_exp.mpr; unfold L; change _ + _*_*_ ≤ (v+t*_) * _ * _; change 1≤ t at he; have hh:1≤z^2:=one_le_pow₀ g; have hy:0≤ t*(2*w)*S.card:=by positivity
             -- cut
        rw [show Acorn.worth n=t from rfl]
        nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤t by linarith),mul_le_mul_of_nonneg_left hh (show 0 ≤ t*S.card by positivity),mul_le_mul_of_nonneg_left hh hy]
end YM.CF.Spire
