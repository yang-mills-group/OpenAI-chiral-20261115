import YM.CF.Kea.Fleet
import YM.CF.Kea.Shift
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
lemma risen(b:ℝ→ℝ)(c:Continuous b)(h:∀ x,b x≠0): 0<b 0*b 1:=by
 rcases lt_or_gt_of_ne (h 0) with t|t <;> rcases lt_or_gt_of_ne (h 1) with g|g; exact mul_pos_of_neg_of_neg t g
 · obtain ⟨x,_,H⟩:=intermediate_value_Icc zero_le_one c.continuousOn (show (0:ℝ)∈_ from Set.mem_Icc.mpr ⟨t.le,g.le⟩); exact False.elim (h _ H)
 · obtain ⟨x,_,H⟩:=intermediate_value_Icc' zero_le_one c.continuousOn (show (0:ℝ)∈_ from Set.mem_Icc.mpr ⟨g.le,t.le⟩); exact False.elim (h _ H)
 exact mul_pos t g
variable {N:Side}{b:Candle→ℝ}
lemma strife(c:Continuous b)(h:∀ d a,(∀ i,BallG N d i a≠-1)→b d≠0)(d:Candle)(a:Axis)(X:Finset Axis)(f:a∉X)(g:∀ i,BallG N d i a≠-1):0<b (lease X d 0)*b d:=by
 let U:=lease X d; let F:= b ∘ U; have hp:=risen F (c.comp (lease_c ..)) (fun x=>h _ a (fun i=>?_)); swap
 · have he:BallG N (U x) i a=BallG N d i a:=by unfold BallG rise; simp [pulse, U,lease,f]; -- scope
   exact he.symm ▸ g i
 simp only [F, U,Function.comp_apply,lease_u] at hp; exact hp
lemma shine(c:Continuous b)(h:∀ d a,(∀ i,BallG N d i a≠-1)→b d≠0)(d:Candle)(hd:b d≠0): 0 < b emptyC*b d:=by
 let a:Axis:=0; let X:=univ.erase a; let G(x:ℝ):=lease ({a}:Finset Axis) d x; let Y(x:ℝ):= b (G x)*b d; have hp:Continuous Y:= (c.comp (lease_c ..)).mul continuous_const
 have he:0<Y 1:=by unfold Y G; rw [lease_u]; exact mul_self_pos.mpr hd
 obtain ⟨r,p,W⟩:=Metric.mem_nhds_iff.mp (hp.continuousAt.eventually (lt_mem_nhds he)); obtain ⟨t,u,T,f⟩:=popC (N:=N) ({a}: Finset Axis) d (1-r) (by linarith) a (mem_singleton_self _)
 have hv:0<b (G t)*b d:= W (show t ∈ ball (1:ℝ) r from mem_ball.mpr (by rw [Real.dist_eq]; exact abs_lt.mpr ⟨by linarith,by linarith⟩))
 let x:= G t; let z:=lease X x 0; have ht:0<b z*b x:= strife c h x a X (by unfold X; simp) f
 have hj' : (1:Axis)≠a:=by decide
 have hh: z 1=skyV:=by apply Subtype.ext; unfold z lease; simp [snapC,X,hj',skyV]
 have ha:0<b (lease {a} z 0)* b z:=strife c h z 1 _ (by simpa) (toll_e N 1 _ hh); have hz:lease {a} z 0=emptyC:=by funext i; apply Subtype.ext; by_cases l:i=a <;>simp [l,z,X,snapC,skyV,lease,emptyC]
 rw [hz] at ha; let v:=b (G t); let l:=b z; rcases mul_pos_iff.mp hv with ⟨hx,H⟩|⟨hx,H⟩
 · have hx:0<b x:=hx; have hk:0< b z:=by rcases mul_pos_iff.mp ht with h|h <;> linarith [h.1,h.2]; -- tune
   exact mul_pos (by rcases mul_pos_iff.mp ha with h|h <;> linarith [h.1,h.2]) H
 have hx:b x<0:=hx; have hk:b z<0:=by rcases mul_pos_iff.mp ht with h|h <;> linarith [h.1,h.2]
 exact mul_pos_of_neg_of_neg (by rcases mul_pos_iff.mp ha with h|h <;> linarith [h.1,h.2]) H

variable {L B m:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}{P:Grasp Y B e}
variable (A:Pearl P)(S:Stamped j L ho Y)(t:P.roundZ ≤ (CSide m B).val)(p:1≤j)
def Pad(j:ℕ)(N:Side): Prop:=Even N.val ∧ ∀ (d:Candle) (S:Slide N d) (M:Jill.Male), funde j M N (profile (tax d))=Dofu N (field S j M)
lemma gave(j:ℕ)(p:1≤j):∃ v:ℕ,∀ N:Side,Even N.val →v ≤ N.val→Pad j N:=by obtain ⟨v,H⟩:=azur j p; exact ⟨v,fun _ t h=> ⟨t,fun _ S=>H S t h⟩⟩
variable (k:0<e)(W:Jill.Male)(h:Pad j (CSide m B))
def angel(m:Side)(P:Grasp Y B e)(M:Jill.Male):ℝ:= ‖AMP m P emptyC M‖
include k t h
lemma rich(d:Candle)(F:Slide (CSide m B) d): ‖AMP m P d W‖=∏ i:Stag (CSide m B),disk j W (angle F i):= by have he:=sea_g (P:=P) t _ (tax_guard d _ _ k.le) W; unfold AMP; apply apex F h.1 j W; change Sea (funde j W _ _) _ at he; rw [h.2 _ _ _] at he; exact he
include A S p
lemma bend(d:Candle)(hp:∃ a, ∀ i,BallG (CSide m B) d i a ≠-1): AMP m P d W≠0:=by
 obtain ⟨a,u⟩:=hp; apply norm_pos_iff.mp; let N:= CSide m B; let F:= skim N d; rw [rich t k W h d F]; obtain ⟨c,C,g,hz,H⟩:= zip p; refine prod_pos fun i _=>?_
 have hx:0< ‖angle F i‖:= norm_pos_iff.mpr (fun v=> height_d d a u F i (congrFun v a))
 exact (mul_pos g (by positivity)).trans_le ((H W _ (up_p F h.1 i)).1)
lemma angel_p:0< angel m P W:=norm_pos_iff.mpr (bend A S t p k W h emptyC ⟨0,toll_e _ 0 _ rfl⟩) -- check args order
lemma cerule(d:Candle):star (AMP m P emptyC W)* AMP m P d W= (angel m P W:ℂ) * (‖AMP m P d W‖:ℂ):=by
 let F d:=AMP m P d W; let f(d):=(F d).re; have he(d):F d=(f d:ℂ):= by
   apply Complex.ext; rfl; have ht:=absol A S t p d W k; have hh:=congr_arg Complex.im ht; change -(F d).im=(F d).im at hh; rw [Complex.ofReal_im]; linarith
 change star (F emptyC)*F d=(‖F emptyC‖:ℂ)*(‖F d‖:ℂ); rw [he d,he emptyC]; simp only [Complex.star_def,Complex.conj_ofReal,Complex.norm_real, ←Complex.ofReal_mul]
 by_cases h': f d=0; · simp [h']
 have hv: Continuous f:= Complex.continuous_re.comp (vol_c A S t p W k) -- tune
 have hp:= shine (N:=CSide m B) hv (fun i a l H=>bend A S t p k W h i ⟨a,l⟩ (by change F i=_; rw [he,H]; rfl)) d h'; norm_cast; rw [←norm_mul,Real.norm_of_nonneg hp.le]
end YM.CF.Kea
