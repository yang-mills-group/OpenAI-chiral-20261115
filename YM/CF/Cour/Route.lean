import YM.CF.Cour.Frame
import YM.CF.Cour.Lake
import YM.CF.Pec.Frond
import YM.CF.Skye.Hark
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {B L:Side}{n k:ℕ}{e t x u C A:ℝ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable{m X:Side}{T:Roam m X B}{F: Forest T.ratio}{G: Ratio (CSide m B) (CSide X B)}
variable{α Y:Type}[Fintype α][DecidableEq Y][Fintype Y]
lemma echo_sum {S:Finset Y}{f:Y→Positions α→ℂ}(p:∀ i∈S,ContDiffAt ℝ (↑k) (f i) 0)(v:Fin k→α): Push.Uniform.entry (fun x=>∑ i∈S,f i x) 0 v=∑ i∈S, Push.Uniform.entry (f i) 0 v:=by
 unfold Push.Uniform.entry; rw [iteratedFDeriv_fun_sum_apply p, _root_.sum_apply] -- tune
variable {r:Side}{L': Finset (Seal (Site r))}{h₁: α→Site r}{v: Set (Positions α)}{l:ℕ}
lemma geist {w: Seal (Site r)→ℝ}{f: Seal (Site r)→ Positions α→ℂ}{b d:ℝ} (hv:v∈𝓝 0)(p:∀ i∈L',Jet.Allows k (f i) 0 (w i)) (h:∀ i∈L',w i≠0→ i.Nonempty ∧∀ x∈i,Requests v (f i) h₁ x (i.card+l))(hx:0<b)(hg:∀ s,hitE b w s≤d) (hp:n≤k)(hn:0<n)(y: Fin n→α)(ht:∀ i,0≤ w i)(j:ℕ)(hk:∀ i∈L',j≤ i.card):
 let t:= b/2; let A:=Real.exp (-t*j)*Real.exp (t*l)
 ‖Push.Uniform.entry (fun x=>∑ i∈L',f i x) 0 y‖ ≤ d*A*Push.Uniform.countCost t:=by
 intro t A; let z:= h₁ (y ⟨0,hn⟩); let K:=Push.Uniform.Decay t z; have ha:0<t:=half_pos hx; have hA:0 ≤ A:=by unfold A; positivity
 have he(o:Site r)(S:Seal (Site r))(hS:j≤S.card)(hp: separation o z ≤ S.card+l):1≤rent b S * (K o*A):=by
    unfold A K Decay Branch.rent; simp only [← Real.exp_add]; apply Real.one_le_exp
    rw [separation_comm _ o]; push_cast at *; have hQ:(separation o z:ℝ) ≤ (S.card:ℝ)+l:=by exact_mod_cast hp
    have hz:(j:ℝ)≤(S.card:ℝ):=by exact_mod_cast hS
    unfold t; linarith only [mul_le_mul_of_nonneg_left hQ hx.le,mul_le_mul_of_nonneg_left hz hx.le]
 let M(S:Seal (Site r))(o):= if o∈S then (rent b S*w S) *A * K o else 0
 rw [echo_sum (fun i hi=> ((p i hi).order hp).smooth)]; apply (norm_sum_le ..).trans
 have hM(S o):0≤ M S o:=by unfold M; split; exact mul_nonneg (mul_nonneg (mul_nonneg (rent_pos ..|>.le) (ht _)) hA) (Push.Uniform.decay_pos ..|>.le); rfl
 let R(S):= ‖Push.Uniform.entry (f S) 0 y‖; apply (sum_le_sum (s:=L') (f:=R) (g:=fun S=>∑ o,M S o) fun S hS=> ?_).trans
 · rw [sum_comm, mul_assoc]; change _ ≤ d*(A*_)
   have hh x:∑ i∈L',M i x≤ d*A*K x:=by
      apply (sum_le_sum_of_subset_of_nonneg (subset_univ L') fun i _ _=>hM i x).trans; apply le_trans ?_ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hg x) hA) (Push.Uniform.decay_pos ..|>.le)); unfold hitE hit0 M; rw [sum_filter, sum_mul,sum_mul]; refine sum_le_sum (fun i _=> ?_); split_ifs <;> (first|exact le_rfl|simp)
   refine (sum_le_sum fun x _=> hh x).trans ?_; rw [← Finset.mul_sum]; have hh:0 ≤ d:=(show 0 ≤ hitE b w z from sum_nonneg fun i _=> mul_nonneg (rent_pos ..|>.le) (ht i)).trans (hg z); exact (mul_le_mul_of_nonneg_left (Push.Uniform.decay_count ha z) (mul_nonneg hh hA)).trans (le_of_eq (mul_assoc ..)) -- tune
 by_cases hi: w S=0; exact ((Push.Uniform.entry_bound y).trans ((p S hS).norm_le n hp)).trans (hi.symm ▸ (sum_nonneg fun x _=>hM _ x))
 obtain ⟨hx,u⟩:= h S hS hi; obtain ⟨o,hx⟩:=hx; by_cases hu:separation o z ≤ S.card+l; swap
 · unfold R; rw [(u _ hx).zero hv ((p S hS).order hp |>.smooth) y ⟨0,hn⟩ hu, norm_zero]; exact sum_nonneg fun _ _=> hM _ _
 apply (show _≤ w S from (entry_bound y).trans ((p S hS).norm_le _ hp)).trans; apply le_trans ?_ (single_le_sum (fun x (_:x∈(univ:Finset (Site r)))=> hM S x) (mem_univ o)); unfold M; rw [if_pos hx]; apply (le_mul_of_one_le_right (ht _) (he o _ (hk _ hS) hu)).trans; exact le_of_eq (by ring)
abbrev frameT (G:Ratio (CSide m B) (CSide X B))(p:0<e)(F:Forest T.ratio)(Z: Snap F):↥(Broc.Rent0 G e):= Pec.pear G p (hats F Z)
variable {i:Set (Snap F)}
structure Fleck (G:Ratio (CSide m B) (CSide X B))(p:0<e)(F:Forest T.ratio)(s A:ℝ)(n:ℕ):Prop where
 onP(y:Snap F)(h:‖y‖<s): hats F y∈ Broc.Rent0 G e
 mark: (Jet.LineE n G A e).test (Snap F) (ball 0 s) (frameT G p F)
lemma rootC(b:0<e)(hn:1 ≤ n)(L:Side):∃ K r:ℝ,1 ≤ K∧0<r∧∀ {m M B:Side}{T:Roam m M B}(F:Forest T.ratio)(G:Ratio (CSide m B) (CSide M B)), G.count=L→∀ a:ℝ, K≤a → Fleck G b F r a n:=by
 obtain ⟨C,h,H⟩:=gleanA n; obtain ⟨v,hv,p,P⟩:= windA L b hn h; refine ⟨C,v,h,hv,fun {m M B T} F G he a g=>?_⟩
 have hV(y)(hy:‖y‖<v):= P G F he (fun x hx=>H F x (hx.trans p)) y hy; have hz(y)(hy:y∈ball 0 v): (frameT G b F y).val=hats F y:= congrArg Subtype.val (Pec.pear_even G b (show _∈ Broc.Rent0 G e from hV y (mem_ball_zero_iff.mp hy)))
 refine ⟨hV,?_⟩; intro z ht; let f:=hV z (mem_ball_zero_iff.mp ht); obtain ⟨hp,hl⟩:= H F z ((mem_ball_zero_iff.mp ht).le.trans p); constructor
 · intro i; apply ((hp i).mono g).germ; filter_upwards [isOpen_ball.mem_nhds ht] with y hy; change _=fund ((frameT G b F y).val.1 i); rw [hz _ hy]; rfl
 intro i; apply ((hl i).mono g).germ; filter_upwards [isOpen_ball.mem_nhds ht] with y hy; change _=fund ((frameT G b F y).val.2 i); rw [hz _ hy]; rfl
lemma sleeve(p:0<e){s v f d:ℝ}(h:T.ratio=ratio G)(t:Fleck G p F s v k)(N:Seal (Site (More (CSide X B)))→ ℝ)(H: Seal (Site (More (CSide X B)))→ Broc.Rent0 G e → ℂ)(ht:∀ i, Jet.Flash (Broc.dressL G e) (Jet.LineE k G v e) k i (H i) (N i))(j:ℕ) (X:Finset (Seal (Site (More (CSide X B)))))(hX:∀ i∈X,j ≤ i.card)(hk:2 ≤k)(hv:0<s)(hg:∀ i,hitE f N i≤d)(hd:0<f):
 Funds (fun x=>∑ i∈X,H i (frameT G p F x)) (d*(Real.exp (-(f/2)*j)*Real.exp ((f/2)*T.ratio.count.val))*countCost (f/2)):=by
 let P:= frameT G p F; let f'(i):= H i ∘ P; let Z:=ball (0:Snap F) s
 have hl S: Jet.Allows k (f' S) 0 (N S):=(ht S).plot (Snap F) Z isOpen_ball _ t.mark 0 (mem_ball_self hv)
 have hz(i)(l:N i ≠0): i.Nonempty∧∀ x∈i,Requests Z (f' i) (clothH T F) x (i.card+T.ratio.count.val):=by
    have he := (ht i).travel l; have hu:i.Nonempty:=by cases he<;> simp
    exact ⟨hu, fun x v=> Pec.readsV F G h p Z (fun x hx=> t.onP _ (mem_ball_zero_iff.mp hx)) i x v he (ht i).toPeak⟩
 have hh(a)(he:a≤k)(hp:0<a)(w):=geist (L':=X) (n:=a) (ball_mem_nhds (0:Snap F) hv) (fun i _=>hl i) (fun i _ hi=>hz i hi) hd hg he hp w (fun i=>(ht i).pos) _ hX
 exact ⟨(Jet.allows_sum (s:=X) (f:=f') (fun i _=>hl i)).smooth.of_le (by exact_mod_cast hk),fun i=>hh _ (by omega) (by decide) i,fun i=>hh _ (by omega) (by decide) i⟩
end YM.CF.Cour
