import YM.SU5.Relativistic.Succot
/-! # pay at oscillator. let lambda* charge budget ~$e$, chooses z. buys estimates from `tide` on birth mask, even after all earlier. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted Pea Omelet
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
def tickTea (A:Bite→Ket I)(w:LinksC) (L:List Wine):= (L.map fun x=>x.fees w • rollC (fun i=>creed i.hand (A i)) x.song).sum
variable (A X:Bite→Ket I){S:Finset Cover}{b:Bool}
abbrev billP(V:List Wine): List Bite:= V.flatMap Wine.song
lemma bill_ (L:List Wine)(x:Wine):billP (x::L)=x.song++billP L:= List.flatMap_cons
lemma tipPower (C:ℝ) (L:List Wine) (p:0<C)(h:AreaW b S L) : ∃ R:ℝ,0 < R ∧∀ {I:Type*}[LinearOrder I][Fintype I][Nonempty I] (U:LinksC) (X:Bite→Ket I), (∀ i∈ billP L, ‖X i‖≤C) → ‖tickTea X U L‖ ≤ R:=by
 induction L with| nil=> refine ⟨1,zero_lt_one,fun _ x h=>?_⟩; simp [tickTea]| cons i L ih=>
    obtain ⟨R,hR,f⟩:=ih (fun i t=>h i (List.mem_cons_of_mem _ t)); obtain ⟨K,p0,Kp⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty ((h i List.mem_cons_self).price.norm.continuousOn); let Q:= ‖i.fees K‖
    refine ⟨Q*C^i.song.length+R,add_pos_of_nonneg_of_pos (by unfold Q; positivity) hR,?_⟩; intro J _ _ _ y X t
    unfold tickTea; rw [List.map_cons,List.sum_cons]; apply (norm_add_le ..).trans; rw [norm_smul]; rw [bill_] at t; exact add_le_add (mul_le_mul (Kp (Set.mem_univ _)) (normC _ _ p _ (fun j q=> (cost_pe ..).trans (t j (List.mem_append.mpr (Or.inl q))))) (norm_nonneg _) (norm_nonneg _)) (f _ _ (fun i p=> t i (List.mem_append.mpr (Or.inr p))))
lemma tipSlope (C:ℝ)(L:List Wine)(p:1≤C)(h:AreaW b S L) (ε:ℝ)(e:0<ε):∃ δ> (0:ℝ),∀ {I:Type*}[LinearOrder I][Fintype I][Nonempty I] (U:LinksC) (X Y:Bite→Ket I), (∀ i∈ billP L, ‖X i‖≤C ∧ ‖Y i‖≤C∧ ‖X i-Y i‖≤δ) → ‖tickTea X U L -tickTea Y U L‖ ≤ ε:=by
 have g:=zero_lt_one.trans_le p; induction L generalizing ε with| nil=> refine ⟨_,e,fun _ _ _ _=>?_⟩; simpa [tickTea] using e.le| cons i L ih=>
    obtain ⟨R,hR,f⟩:=ih (fun i t=>h i (List.mem_cons_of_mem _ t)) (ε/2) (half_pos e); obtain ⟨K,p0,Kp⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty ((h i List.mem_cons_self).price.norm.continuousOn); let A:= ‖i.fees K‖+1; let n:=i.song.length; have hA:0<A:=by unfold A; positivity
    let δ:=(ε/2)/(A*((n:ℝ)+1)*C^n); have hf:A*((n:ℝ)+1)*C^n>0:=by positivity
    have ht:0<δ:=div_pos (by positivity) hf
    refine ⟨_,lt_min ht hR,?_⟩; intro I _ _ _ U X Y t; rw [bill_] at t; unfold tickTea; rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,add_sub_add_comm,←smul_sub]
    have he:=f U X Y (fun i p=> by obtain ⟨a,b,c⟩:= t i (List.mem_append.mpr (Or.inr p)); exact ⟨a,b,c.trans (min_le_right ..)⟩); apply (norm_add_le ..).trans; refine (add_le_add (b:=ε/2) ?_ he).trans_eq (add_halves _)
    have hj(j)(u:j∈i.song): ‖creed j.hand (X j)‖ ≤ C ∧ ‖creed j.hand (Y j)‖ ≤ C∧ ‖creed j.hand (X j)-creed j.hand (Y j)‖ ≤ δ:=by obtain ⟨a,b,c⟩:=t _ (List.mem_append.mpr (Or.inl u)); exact ⟨(cost_pe ..).trans a,(cost_pe ..).trans b,(scone ..).trans (c.trans (min_le_left ..))⟩
    rw [norm_smul]; apply (mul_le_mul ( (Kp (Set.mem_univ U)).trans (le_add_of_nonneg_right zero_le_one)) (normsDiff _ _ _ p δ ht.le i.song (fun i v=> (hj i v).1) (fun i v=>(hj i v).2.1) (fun i v=>(hj i v).2.2)) (norm_nonneg _) hA.le).trans
    have hx:ε/2=δ*(A*((n:ℝ)+1)*C^n):=(div_mul_cancel₀ _ hf.ne').symm
    rw [hx]; nlinarith only [mul_nonneg (mul_nonneg ht.le (pow_nonneg g.le n)) hA.le] -- n vs i...
lemma shiftTea (T:Shaft I) (U:LinksC) (L:List Wine): T.glow (tickTea A U L)= tickTea (fun i=>acts (if i.hand then star T.buy else T.sell) (A i)) U L:=by
 let B(i:Bite) := acts (if i.hand then star T.buy else T.sell) (A i)
 let X(i:Bite):=creed i.hand (A i); let Y(i:Bite):= creed i.hand (B i)
 have he(L:List Bite): T.glow (rollC X L) = rollC Y L:=by
    induction L with| nil=> simp [rollC,Shaft.glow_nil]| cons i L ih=>
      change T.glow (X i*rollC X L)=Y i*rollC Y L; rw [Shaft.glow_mult,ih]; congr 1; unfold X Y B; cases i.hand; exact Shaft.glow_up ..; exact T.glow_down _
 induction L with| nil=>simp [tickTea, T.glow_zero]| cons i L ih=> simp only [tickTea,List.map_cons,List.sum_cons] at *; rw [T.glow_sum,ih,T.glow_free]; congr 2; exact he _
variable {N:Side}{P:Op (Single N)}(p:IsStarProjection P)
local notation "𝔯" k => Saber (B:=tickA N) p k
def Straw (P:Op (Single N))(k:ℕ) (i:Bite):= (stilt k P i).2
lemma skyT (U:Pane N)(X:Fields N)(h:X.1=U) (L:List Wine)(k:ℕ) : (Saber (B:=tickA N) p k).glow (motet N L X)= tickTea (Straw P k) (onC N U) L:=by
 induction L with| nil=>simp [motet,tickTea,Shaft.glow_zero]|cons i L ih=> unfold motet tickTea at *; rw [List.map_cons,List.sum_cons,List.map_cons,List.sum_cons,Shaft.glow_sum,pulseX,Shaft.glow_free,stamps,ih]; rw [h]; rfl
-- when trans α.H hosting
lemma juice {Q A:Pea I}(h:Q.Zones A)(v:Ket I)(p:acts A.robe v=v) (T Qx:ℝ) : acts (Q.Φ T Qx) v=v:=by
 have hv:acts Q.robe v=0:=by nth_rw 1 [←p]; rw [←act_mul,h.fares,act_zero]; -- tune
 have ht:acts Q.fill v=0:=by nth_rw 1 [← Q.flsp]; rw [act_mul,hv,map_zero]
 have hh:acts Q.pour v=0:=by nth_rw 1 [←Q.posp]; rw [act_mul,hv,map_zero]
 unfold Pea.Φ; rw [act_add,act_add,act_one,show T • Q.fill=(T:ℂ) • Q.fill from (Complex.coe_smul ..).symm,show Qx • Q.pour=(Qx:ℂ) • Q.pour from (Complex.coe_smul ..).symm,act_smul,act_smul,hh,ht]; simp
lemma juice_arm(T Q:Pea I)(h:T.Zones Q)(A: Bite→Ket I)(b:Bite) : let X:=acts Q.robe (A b); acts (if b.hand then star T.mint.buy else T.mint.sell) X=X:=by
 intro X; have he:acts Q.robe X=X:=by unfold X; rw [←act_mul,Q.robe_p.isIdempotentElem]
 split
 next _=> rw [show star T.mint.buy=T.mint.buy from T.tale _ _]; exact juice h _ he 1 (- (1/2:ℝ))
 next _=> exact juice h _ he (- (1/2:ℝ)) 1
lemma mntSize (T:Pea I)(x:Bool): ‖if x then star T.mint.buy else T.mint.sell‖≤2:=by split; exact (norm_star _).trans_le (T.signed.2); exact T.signed.1
-- local cylinders
lemma scopeTea (p:Pea I)(U:UNI I)(s t:Finset I)(x:p.fill=twist U (cutM s))(y:p.pour=twist U (cutM t))(L:List Wine)(h:AreaW b S L)(Y:LinksC) (Ψ:Bite→Ket I)(ht:∀ i∈ billP L, acts p.robe (Ψ i)=Ψ i) (u:Disjoint s t): Sector (s∪t) b (twist (star (quantU U)) (tickTea Ψ Y L)):=by
 let K:=twist (star (quantU U)); have he(i)(a:i∈billP L): Sector (s∪t) true (K (creed i.hand (Ψ i))):=by
    have hv:acts (cutM (s∪t)) (acts (star U.val) (Ψ i))=acts (star U.val) (Ψ i):=by
       have hw:p.robe= twist U (cutM (s∪t)):=by unfold Pea.robe; rw [x,y,←map_add]; apply congrArg; ext i j; by_cases p:i=j; subst j; by_cases h:i∈s; have hp:i∉t:=Finset.disjoint_left.mp u h; simp [cutM,h,hp]; by_cases z:i∈t <;> simp [cutM,h,z]; simp [cutM,p]
       have hz:= ht i a; rw [hw,twist_formula,act_mul,act_mul] at hz; -- apply star
       exact ((act_unit U _).symm.trans (congrArg (acts (star U.val)) hz))
    change Sector _ true (twist _ _); have hg: star (quantU U)=quantU (star U):=Subtype.ext (quant_star _).symm
    rw [hg]; cases q:i.hand with
    | false=> rw [show creed false _=create (Ψ i) from rfl,twist_create]; exact Sector.makeP _ hv -- locations support
    | true=> rw [show creed true _=remove (Ψ i) from rfl,twist_remove]; exact (Sector.makeP _ hv).contr
 induction L with| nil=> simp only [tickTea,List.map_nil,List.sum_nil,map_zero]; apply Sector.zero
                 | cons i L ih=>
   rw [bill_] at he
   unfold tickTea; rw [List.map_cons,List.sum_cons,map_add,twist_scalar]
   have hv(x:List Bite)(g:∀ i∈x,Sector (s∪t) true (K (creed i.hand (Ψ i)))): Sector (s∪t) (label x) (K (rollC (fun i=>creed i.hand (Ψ i)) x)):=by
    induction x with|nil=> rw [rollC,List.map_nil,List.prod_nil,label,map_one]; exact Sector.one|cons i y ih=> rw [rollC,List.map_cons,List.prod_cons,map_mul,label]; rw [show (!(label y))=true.xor (label y) from (by cases label y <;> rfl)]; exact Sector.mul (g _ List.mem_cons_self) (ih (fun i p=>g _ (List.mem_cons_of_mem _ p))) -- tune!
   refine (Sector.scale (?_: Sector _ b _) _).add (ih (fun i p=>h _ (List.mem_cons_of_mem _ p)) (fun i p=> ht _ (List.mem_append.mpr (Or.inr p))) (fun i p=>he _ (List.mem_append.mpr (Or.inr p))))
   rw [← (h i List.mem_cons_self).ethic]; exact hv _ fun i p=>he _ (List.mem_append.mpr (Or.inl p))
end YM.CF.Papyrus.Franc.Loaves
