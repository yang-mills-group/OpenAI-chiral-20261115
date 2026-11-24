import YM.CF.BPress.Wealth.Split
import YM.Push.ABSOLUTE_SUMS.Array
/-!
Accounting primitives over gauge sites. B-eq wn of VolumeB-gauge; exact supports in true pull. Aggregate over paths for real outputs preserving gauge invariance. Separately pay all long pair costs with same lumping. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}{s:Side}{I : Type*} [Countable I]
open Push.Local
open RG
abbrev Rooms (s : Side) := Grid.field 4 s

structure GEM (S : Support s)(f:Config G s→ℝ)(k:ℝ) : Prop where
 zero : 0≤k
 price (x:Config G s) : |f x|≤ k
 meas : Measurable f
 loc : LocalOn S f
 inv : GaugeInvariant f
namespace GEM
variable {f g : Config G s→ℝ} {S P: Support s} {k t : ℝ}
theorem vac (S : Support s) : GEM (G:=G) S 0 0 := ⟨by norm_num,by simp,measurable_const,fun _ _ _=>rfl,fun _ _=>rfl⟩
#check vac
theorem plus (h:GEM S f k)(p:GEM S g t): GEM S (fun i=> f i+g i) (k+t):= ⟨add_nonneg h.zero p.zero,fun x=>(abs_add_le ..).trans (add_le_add (h.price x) (p.price x)),h.meas.add p.meas,fun _ _ e=> congrArg₂ (·+·) (h.loc _ _ e) (p.loc _ _ e),fun g i=>congrArg₂ (·+·) (h.inv g i) (p.inv g i)⟩
#print plus
theorem scale (a:ℝ)(h:GEM S f k): GEM S (fun i=> a*f i) (|a| *k) := ⟨mul_nonneg (abs_nonneg _) h.zero,fun x=>abs_mul a _|>.le.trans (mul_le_mul_of_nonneg_left (h.price _) (abs_nonneg _)),measurable_const.mul h.meas,fun _ _ e=>congrArg _ (h.loc _ _ e), fun g i=>congrArg _ (h.inv g i)⟩
theorem ship (σ:Signed)(h:GEM S f k): GEM (photo σ S) (fun i=> f (pull σ 0 i)) k:= ⟨h.zero,fun i=>h.price _,h.meas.comp (continuous_pull ..).measurable,fun _ _ t=> h.loc _ _ (agrees_pull _ _ t), invariant_pull h.inv σ 0⟩
theorem env (h:GEM S f k): Envelope f:= ⟨h.meas,k,h.price⟩
end GEM
structure Thinner (f: Support s → Config G s→ ℝ)(K:Support s →ℝ) (a C:ℝ) : Prop where
 zero(P): ¬ Grove (Rooms s) P→ K P=0
 unit(P): GEM P (f P) (K P)
 cash : Ledger.Cash id K a C
namespace Thinner
variable {f g : Support s → Config G s→ℝ} {K L: Support s→ℝ} {a C D:ℝ}
theorem vac (a:ℝ): Thinner (G:=G) (s:=s) 0 0 a 0:= by refine ⟨fun p _=>rfl,fun p=>GEM.vac p, fun _=> le_rfl,fun p=>?_⟩; change SumBudget (fun i:Support s=> if p∈id i then Real.exp (a*(id i).card)*0 else 0) 0; simp only [Ledger.score,Pi.zero_apply,mul_zero,ite_self]; exact budget_finite (fun _=>le_rfl) (by simp)
theorem plus (p: Thinner f K a C)(t: Thinner g L a D) : Thinner (fun P i=> f P i+g P i) (fun P=>K P+L P) a (C+D):=⟨fun i h=>by rw [p.zero i h,t.zero i h,zero_add],fun i=> (p.unit i).plus (t.unit i),p.cash.plus t.cash⟩
theorem scale (c:ℝ)(p:Thinner f K a C): Thinner (fun P i=> c*f P i) (fun P=>|c| * K P) a (|c| *C):= ⟨fun i h=>by rw [p.zero i h,mul_zero],fun i=>(p.unit i).scale c, p.cash.scale |c| (abs_nonneg _)⟩ -- tune order
theorem low (p:Thinner f K a C){b:ℝ}(v:b ≤ a)(t:C ≤ D) : Thinner f K b D:= ⟨p.zero,p.unit,(p.cash.chill v).weaken t⟩
theorem inactive (p:Thinner f K a C) (P:Support s)(t:¬ Grove (Rooms s) P)(U) : f P U=0:=abs_nonpos_iff.mp ((p.unit P).price U|>.trans_eq (p.zero P t))
#check Thinner.plus
theorem sumThin {ι:Type*}(t:Finset ι) {f:ι→Support s→Config G s→ℝ}{K:ι→Support s→ℝ}{C:ι→ℝ}(p:∀ i,Thinner (f i) (K i) a (C i)): Thinner (fun P i=>∑ j∈t,f j P i) (fun P=>∑ j∈t,K j P) a (∑ j∈t,C j) := by
 induction t using Finset.induction_on with|empty=> simp_rw [sum_empty]; exact vac _ | insert i t ht ih=> simp_rw [sum_insert ht]; exact (p i).plus ih
end Thinner

def crop (r:I→ Support s) (f : I→Config G s→ℝ) (t: Support s)(x:Config G s):= Ledger.lump r (fun i=> f i x) t
theorem crop_bound {a C:ℝ} {r:I→ Support s}{f : I→Config G s→ℝ}{K:I→ℝ} (t:∀ i, GEM (r i) (f i) (K i)) (v:∀ i,Grove (Rooms s) (r i))(p:Cash r K a C)(h:0≤a):
    Summable K ∧ (∀ U, Summable fun i=> f i U) ∧ (∀ U, ∑ P,crop r f P U=∑' i,f i U) ∧ Thinner (crop r f) (Ledger.lump r K) a C:= by
 have hv: Summable K := (p.total h (fun i g=> False.elim ((Finset.nonempty_iff_ne_empty.mp (Grid.inhabited_grove (v i))) g))).2.1; have hm(U): Summable fun i=> f i U:= Summable.of_norm_bounded hv (fun i=> (t i).price _); have c:=p.lump r K hv
 refine ⟨hv,hm,fun U=> lump_sum r _ (hm U), ⟨ fun i p=> ?_, fun i=> ⟨ c.pos _, fun U=> lump_bound r K (fun i=> f i U) hv (fun j=> (t j).price _) i,?_, ?_, fun g U=> ?_ ⟩, c⟩⟩
 · unfold Ledger.lump; simp_rw [show ∀ j,i≠ r j from fun j z=> p (z ▸ v j)]; simp
 · unfold crop Ledger.lump; apply Measurable.tsum; intro j; split; exact (t j).meas; exact measurable_const
 · intro U V h; apply tsum_congr; intro j; split; next p=> exact (t j).loc _ _ (p ▸ h)
   rfl
 apply tsum_congr; intro j; split; exact (t j).inv _ _; rfl

-- geometric estimate for copies over every center.
def Wt (σ : ℝ)(M:ℕ):= (((2*M+3:ℕ):ℝ))^4 * ( (σ/2)⁻¹^4* (Nat.factorial 4:ℝ) * Real.exp (σ/2)) * Real.exp 1
theorem expense (σ:ℝ) (p:0<σ)(M l:ℕ) : ((↑(2*(M+l)+1)):ℝ)^4 * Real.exp (1+(σ/2)*(l:ℝ)) ≤ Wt σ M * Real.exp (σ*l):=by
 let a:= σ/2; have hv:0<a:= half_pos p; have he: Real.exp (σ*l) = Real.exp (a*l)*Real.exp (a*l):= by rw [←Real.exp_add,← add_mul,show a+a=σ by unfold a; ring]
 rw [he]; change _ * Real.exp (1 + a*l) ≤ _; rw [Real.exp_add]; push_cast; apply le_trans (b:= (((2*M+3:ℕ):ℝ)*(1+l:ℝ))^4 * (Real.exp 1*Real.exp (a*l))) -- tune refine
 swap; · rw [mul_pow]; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_cost hv (Nat.cast_nonneg l) 4) (by positivity)) (by positivity)) (Eq.le ?_); unfold Wt a; ring
 gcongr; push_cast; nlinarith

theorem current_bound (q : Site s ≃ Site s) (M : ℕ)(l : I→ℕ)(r : Site s × I→Support s)
    (v:∀ i, r i ⊆ halo (M+l i.2) {q i.1}) {b:I→ℝ}(h:∀ i,0≤b i){σ a C:ℝ}(t:0<σ)(d:∀ i, a*(r i).card ≤ 1+σ/2*l i.2)(p : SumBudget (fun i=> b i * Real.exp (σ*l i)) C):
    Cash r (fun i => b i.2) a (Wt σ M*C) := by
 constructor; exact fun i=> h _; intro x; have ht:0≤ Wt σ M:= by unfold Wt; positivity
 refine budget_fiberwise Prod.snd (fun i=>(by unfold score; split; exact mul_nonneg (Real.exp_pos _).le (h _); rfl)) ?_ (budget_scale ht p)
 intro k u e; let s':= u.filter (fun i=>x∈ r i); let g : Finset (Site s):= halo (M+l k) {x}; have hx(i)(p:i∈ s') : i.2=k ∧ x ∈ r i ∧ q i.1∈g:=by
    obtain ⟨z,h⟩:=mem_filter.mp p; obtain ⟨j,t,a⟩:=halo_spec.mp (v i h); specialize e i z; rw [mem_singleton.mp t,e] at a; exact ⟨e,h, halo_spec.mpr ⟨x,mem_singleton_self x,(separation_comm ..).le.trans a⟩⟩
 have hl:s'.card ≤ (2*(M+l k)+1)^4:= le_trans (card_le_card_of_injOn (fun i=>q i.1) (fun i p=>(hx i p).2.2) (fun i p j t h=> Prod.ext (q.injective h) ((hx i p).1.trans (hx j t).1.symm))) (halo_size ..)
 let H := Real.exp (1+(σ/2)*l k); unfold score; simp_rw [← sum_filter]; apply le_trans (sum_le_sum (g:=fun _=> H*b k) (fun i v=> ?_)); swap; · have he := d i; obtain ⟨f,y⟩:= hx _ v; rw [f] at he ⊢; exact mul_le_mul_of_nonneg_right (Real.exp_monotone he) (h k) -- tune apply order
 rw [sum_const, nsmul_eq_mul]; refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hl) (mul_nonneg (Real.exp_pos _).le (h _))) ?_; rw [Nat.cast_pow, ←mul_assoc]; exact le_trans (mul_le_mul_of_nonneg_right (expense σ t M (l k)) (h _)) (Eq.le (by ring))
end YM.CF.BPress.Wealth
