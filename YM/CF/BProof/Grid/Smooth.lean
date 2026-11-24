import YM.CF.BProof.Grid.Range

/-! End of transport estimate of lem:B-frames. R = b*2^k, b fixed. Support cardinal cost
is in k instead of logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid.Blend
open Function Lattice MeasureTheory SU Filter
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
local notation "ℬ" => SU.group
local notation "P" => (spinFiber.pay 3)

variable (ε C u : ℝ)(b : Side)(pC:0<C)(pε:0<ε)(hu : Ticket P C ε b.val u)
variable {c f s : Side}

def Step (ε C : ℝ): Prop := ∀ {c s:Side}(g:Ratio c s)(U:Wire ℬ 3 s)(Q:Floor E 3 c){m a : ℝ},
    4≤c.val→g.count.val=2→0≤m→0≤a→ Wire.Flat ℬ U Set.univ m → SeatBound ℬ Q (Wire.long ℬ U g) a → m+a≤ ε → SeatBound ℬ (blend ℬ g U Q) U (a/2+C*(m+a^2))

variable (Z:Step ε C)(hp: spinFiber.cap b (u/(b.val:ℝ)^2))
variable (g : Ratio c f) (r : Ratio f s)(hc:4≤ c.val)
local notation "Lk" => (10+3*b.val)
local notation "Q" => quota (10+3*b.val)
def Aspect (u : ℝ) (g : Ratio c s) (U : Wire ℬ 3 s) := Wire.Flat ℬ U Set.univ (u / (g.count.val:ℝ)^2)

-- keep n.k choice and total height assertion
include pC hu hp hc Z
private lemma process (k:ℕ)(ht:g.count.val=b.val*2^k):
    ∃ F: Ψ c s→ Floor E 3 f, Measurable F ∧
      Shelter r g F ((k+1)*(1+Q)) ((2* Lk+1)*(nest g r).count.val) (Q*(2*(nest g r).count.val-r.count.val)) ∧
      ∀ V : Ψ c s, (∀ x, F V (grow g x)=V.2 x) ∧
        (Aspect u (nest g r) V.1 → SeatBound ℬ (F V) (Wire.long ℬ V.1 r) (speed P b.val k)):=by
 -- go_est needs flat for pinned? pinned currently inside go_est requires valid. separate.
 have hs {c s:Side}(g:Ratio c s):0<(g.count.val:ℝ):= Nat.cast_pos.mpr g.count.property
 have hw {i j t:Side}(g:Ratio i j)(r:Ratio j t)(U: Wire ℬ 3 t)(h:Aspect u (nest g r) U) : Wire.Flat ℬ (Wire.long ℬ U r) Set.univ (u/(g.count.val:ℝ)^2):= by
    unfold Aspect at h; have he:= Wire.coarse_flat ℬ U r _ h; rw [show (nest g r).count.val=g.count.val*r.count.val from rfl,Nat.cast_mul,show (r.count.val:ℝ)^2* _=u/(g.count.val:ℝ)^2 from ?_] at he; exact he
    have hv:= hs r; have hh:=hs g; field_simp; -- tune
 have hl (r : Ratio f s) : Measurable (fun U : Wire ℬ 3 s=> Wire.long ℬ U r):= Contin r -- tune
 have hb0:0<(b.val:ℝ):=hu.pre; have ht':0<u:=hu.mass
 induction k generalizing f with
 | zero=>
   rw [pow_zero,mul_one] at ht
   let F(U:Ψ c s):= Grid.go g U.2 (Wire.long ℬ U.1 r)
   obtain hg:= premise r g (10+3*b.val) hc (by omega)
   refine ⟨F,(Grid.go_m g).comp (f:=fun x:Ψ c s=>(x.2, Wire.long ℬ x.1 r)) (Measurable.prodMk measurable_snd ((hl r).comp measurable_fst)),⟨fun S v w=>?_⟩,fun V=> ⟨?_,?_⟩⟩
   · obtain ⟨T,v,o,x,y,z⟩:=hg.reach S v w; refine ⟨T,v,o,x.trans (collar_le (fun _ h=>h) ?_), y.trans ?_, z⟩; -- tune
     have he:r.count.val ≤ (nest g r).count.val:= Nat.le_mul_of_pos_left _ g.count.property; exact Nat.mul_le_mul_left _ he
     rw [Nat.zero_add,one_mul]; gcongr; have he:r.count.val ≤ (nest g r).count.val:= Nat.le_mul_of_pos_left _ g.count.property; omega
   · exact fun x=> go_pin g _ _ hc x -- missing
   intro v; have hp' : spinFiber.cap g.count (u/(g.count.val:ℝ)^2):=by unfold Fiber.cap; rw [ht]; exact hp
   have hz:= (Grid.go_est g V.2 _ hc hp' (hw g r V.1 v)).1; rw [ht] at hz -- beware rewrites inside F
   unfold speed; ring_nf; exact hz -- tune
 | succ k ih=>
   let s':Side := c*(b*2^k); let g':Ratio c s':=⟨b*2^k,rfl⟩
   let r':Ratio s' f:=⟨2,by rw [g.exact_size,ht]; push_cast; unfold s'; push_cast; rw [pow_succ]; ring⟩ -- tune
   have hs':4≤s'.val:= hc.trans (Nat.le_mul_of_pos_right c.val (b*2^k:Side).property)
   let T:= nest r' r; have Hℓ(R : Ratio s' s) : Measurable (fun U: Wire ℬ 3 s=> Wire.long ℬ U R):=Contin R
   obtain ⟨F,hF,V,H⟩:= ih g' T (by simp [g']) Hℓ -- tune
   let A (U : Ψ c s):=blend ℬ r' (Wire.long ℬ U.1 r) (F U)
   have ht':= hu.mass; have hr:r'.count.val=2:=rfl
   refine ⟨A,(birth_m ℬ r').comp (f:=fun U: Ψ c s=> (Wire.long ℬ U.1 r,F U)) (Measurable.prodMk ((hl r).comp measurable_fst) hF),⟨fun S v w=>?_⟩,fun W=> ⟨fun x=>?_, fun p=>?_⟩⟩
   · have he := purchase r r' g' F hr hs' V Lk (by omega)
     obtain ⟨D,a,i,u,d,y⟩:=he.reach S v w; rw [nest_eq (nest g' T) (nest g r)] at *; rw [nest_eq (nest g' r') g] at y
     refine ⟨D,a,i,u.trans (collar_le (fun _ h=>h) (max_le le_rfl (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ g.count.property)))),d.trans ?_,y⟩
     have hr₀:r.count.val≤ (nest g r).count.val:= Nat.le_mul_of_pos_left _ g.count.property; have hR: (nest r' r).count.val ≤ (nest g r).count.val := by rw [← nest_eq (nest g' T) (nest g r)]; exact Nat.le_mul_of_pos_left _ g'.count.property
     have h' : (nest r' r).count.val=2*r.count.val:=rfl
     rw [show (k+1)*(1+Q)+1+Q=(k+1+1)*(1+Q) from by ring]
     -- simplify N
     rw [←mul_add]; gcongr; have Hx : T.count.val=2*r.count.val:=h'; omega
   · unfold A; rw [← nest_eq (nest g' r') g,grow_nest,pinned]; exact (H W).1 x
   have hb : 0≤speed P b.val k:= (speed_le (spinFiber.pay_p _) hu.pre k).1.le
   let K:=u/(g.count.val:ℝ)^2; have hh:0≤K:=by unfold K; positivity
   have he : K=u/(b.val* (2:ℝ)^(k+1))^2:= by unfold K; rw [ht]; push_cast; rfl
   have hz:= Z r' (Wire.long ℬ W.1 r) (F W) hs' hr hh hb (hw _ _ W.1 p)
   have hF : Aspect u (nest g' T) W.1 :=by rw [nest_eq (nest g' T) (nest g r)]; exact p
   intro x i; apply le_trans (hz (by rw [Wire.long_nest]; exact (H W).2 hF) (he ▸ hu.small k) x i); rw [he]; exact hu.bill k
where Contin {f s:Side} (r:Ratio f s) : Measurable (fun U:Wire ℬ 3 s=>Wire.long ℬ U r):= measurable_pi_lambda _ fun i=> (Wire.continuous_line ..).measurable
omit pC hu hp hc Z
open Finset
/-- lemma B-frames expressed with the log in the integer exponent. All support estimates
carry both endpoints of read links. -/
theorem frames : ∃ k₀ C' : ℕ, ∃ d K : ℝ,0<d ∧ 0<K ∧ ∀ {c f:Side}(g : Ratio c f),
   4≤ c.val → ∀ k : ℕ,g.count.val=2^k→ k₀ ≤ k → ∃ F : Ψ c f → Floor E 3 f, Measurable F ∧
    (∀ V : Ψ c f,(∀ x,F V (grow g x)=V.2 x)∧(Aspect d g V.1→ SeatBound ℬ (F V) V.1 (K/g.count.val)))∧
    ∀ S:Finset (Cubic 3 f), S.Nonempty → Conn S 1 → ∃ T : Finset (Cubic 3 f), S⊆T∧ Conn T 1∧ T⊆collar S (C'*g.count.val)∧ T.card≤ C'*(g.count.val+(1+k)*S.card)∧
        ∀ V W:Ψ c f, Wire.Agrees ℬ (T:Set _) V.1 W.1 → Set.EqOn V.2 W.2 ((grow g) ⁻¹' T) → Set.EqOn (F V) (F W) S:= by
 obtain ⟨C,ε,hc,he,H⟩:=stepper ℬ 3
 let s : ℝ:= 1/100
 obtain ⟨k₀,T₀⟩:= ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually (buys _ _ _ (spinFiber.pay_p 3) hc he)).exists
 let b:Side:=2^k₀; have hb:b.val=2^k₀:=by simp [b]
 have hu : Ticket P C ε b.val s:=by rw [hb]; push_cast; exact T₀ s (by norm_num [s]) (by norm_num [s])
 let V':ℕ:=10+3*b.val; let q:= quota V'; let C':=max (2*V'+1) (2*q+1); have hp: spinFiber.cap b (s/(b.val:ℝ)^2):=by
    have hp:= hu.pre; unfold Fiber.cap s; rw [show spinFiber.C=2 from rfl]; constructor; positivity; field_simp; norm_num
 refine ⟨k₀,C',s,2*P,hu.mass,mul_pos (by norm_num) (spinFiber.pay_p 3),fun g hg k hk v=>?_⟩
 let n:=k-k₀; have hp' : g.count.val=b.val*2^n:=by rw [hb,← pow_add]; exact hk.trans (by rw [Nat.add_sub_of_le v])
 obtain ⟨F,hF,L,T⟩:= process ε C s b hc hu H hp g (digit _) hg n hp'; refine ⟨F,hF,fun U=>⟨(T U).1, fun h a i=>?_⟩, fun S t u=>?_⟩
 · have he:= (T U).2 (by rw [nest_eq (nest g (digit _)) g]; exact h) a i; apply le_trans (b:=speed P b.val n); simpa only [Wire.long,digit_grow,digit_count, Wire.line_one] using he; rw [hp']; push_cast; exact (speed_le (spinFiber.pay_p _) hu.pre n).2
 obtain ⟨A,hA,d,J,w,K⟩:= L.reach S t u
 refine ⟨A,hA,d,J.trans (collar_le (fun _ h=>h) (by rw [nest_eq (nest ..) g]; exact Nat.mul_le_mul_right _ (le_max_left ..))),w.trans ?_, fun V W h e x hx=> K V W h (fun x u=> e (by rwa [digit_grow] at u)) _ (show scoutR _ S x 6 from ?_)⟩
 · rw [nest_eq (nest ..) g]; let M:=g.count.val
   have hQ : q*2≤ C':=le_trans (by omega : q*2≤ 2*q+1) (le_max_right ..); have hh : 1+q ≤ C':=le_trans (by omega : 1+q ≤ 2*q+1) (le_max_right ..)
   rw [mul_add C',add_comm (C'*_)]; apply Nat.add_le_add
   · rw [mul_comm (n+1),←mul_assoc]; apply Nat.mul_le_mul_right; exact Nat.mul_le_mul hh (by unfold n; omega)
   exact le_trans (Nat.mul_le_mul_left q (show 2*M-_≤2*M from Nat.sub_le ..)) (by rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hQ)
 unfold scoutR; rw [digit_grow]; exact to_collar _ _ hx
end YM.CF.BProof.Grid.Blend
