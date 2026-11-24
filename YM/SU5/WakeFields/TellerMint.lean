import YM.SU5.WakeFields.LatchCorp

/-! # Actually collecting the layout loans with old Keys
 (the arrangement wire, including color on true flag).
 -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson RG Scroll Fock Cadre Stax Mew Roots
open Push.AbsoluteSums Trees Ione MeasureTheory Finset
open Cube Lat Tulip Skye Scree Hake Jet Sault Vow Vow.TreasuryFog Rive Larch
open scoped Topology ContDiff BigOperators Classical YM.CF.Mew Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Palot Leaf Rill
variable {n:Side} {P:BudgetPoint} {a b h:ℝ} {q : ℕ} {I : Type} [LinearOrder I] [Fintype I]

-- keep pigmentation in retail goods markup (inherited Force)
theorem settlement {K : ForceBudget n}(p : SanB K (giftK P a) P h (fun _=>b)) (u : 0 ≤ h) (w : FlagWidth P K (cipherK q)) (c:ℝ) :
    ∃ G:blazeK n, (∀ X:Aura n,∀ D⊆X.val, Fray P h (cipherK q) X D (settleK K X D) (G X D)) ∧
        ∀ i:Seat n,Cadre.nook (roofL G 1* Cadre.loom_v a c (widthK n P.B) 0) i ≤ chi_f P.order*b := by
 obtain ⟨g,t,v⟩:=p.bit
 let f(i:Force n):= chi_f P.order*g i
 let G(X:Aura n)(D):= ∑ i∈motV X D,f i
 have ht(X:Aura n) : G X ∅=0:=by
    apply sum_eq_zero; intro i w; have hh: extraD i=∅:= (mem_filter.mp w).2.2; exact False.elim (i.property.1.ne_empty hh)
 have hu(X:Aura n)(D:Support (More n)):Fray P h (cipherK q) X D (settleK K X D) (G X D):=by
    apply Fray.sumP; intro i v; obtain ⟨p,t'⟩:=(mem_filter.mp v).2; change Fray P h (cipherK q) X D (K i) (f i); rw [← p,←t']; exact ⟨(rimP (t i) u).2,w i⟩
 refine ⟨G,fun X D _=>hu X D,fun i=>?_⟩
 rw [←parse,mul_zero,sub_zero, age_t,show urnL G=0 from funext ht, tallB, Finset.sum_eq_zero (fun j _=>zero_mul _), zero_add,one_mul]; apply le_trans _ (mul_le_mul_of_nonneg_left (v i) (Vow.spicy_f _)); unfold tallB; simp_rw [giftK,ite_mul,zero_mul]
 rw [←sum_filter, ←sum_fiberwise_of_maps_to (t:=univ.filter fun x:Aura n=>i∈x.val) (g:=lordD) (fun j p=>mem_filter.mpr ⟨mem_univ _,(mem_filter.mp p).2⟩),mul_sum]; apply sum_le_sum; intro X uX; apply le_of_eq
 let F(i:Force n):= chi_f P.order * (Trees.currency P.B a X.val*g i)
 let Y:=univ.filter fun j:Force n=> lordD j=X
 have he: (univ.filter (fun j:Force n=> i∈j.val.1.val.2)).filter (fun j=>lordD j=X) = Y:= by ext j; simp only [Y, mem_filter,mem_univ,true_and, and_iff_right_iff_imp]; intro g; change i∈ (lordD j).val; rw [g]; exact (mem_filter.mp uX).2
 have hh: chi_f P.order* (∑ i∈ Y,Trees.currency P.B a i.val.1.val.2*g i)= ∑ i∈Y,F i:=by
    rw [Finset.mul_sum]; exact sum_congr rfl (fun i v => by rw [show i.val.1.val.2=X.val from congrArg Subtype.val (mem_filter.mp v).2]) -- tune
 rw [he,hh]; rw [← Finset.sum_fiberwise_of_maps_to (s:=Y) (t:= Vow.fullD X) (g:= extraD) (fun j h=>?_)] -- goals?
 · unfold Vow.hymn; rw [sum_mul]; apply sum_congr rfl; intro j u; unfold G; unfold Y; rw [sum_mul,filter_filter]; exact sum_congr rfl (fun j _=> (by unfold f F; ring))
 rw [←(mem_filter.mp h).2]; exact mem_filter.mpr ⟨mem_univ _,j.property⟩

-- per-x rack handles
structure Mentor (C:Occlus P) (n:ℕ) (a b k:ℝ) : Prop where
    one : C.κ=1
    shelf : C.γ*Sour.spanV P.B≤C.η
    stiff : Sour.spanV P.B*C.η⁻¹*C.c ≤ C.d
    hard : Sour.spanV P.B*C.c ≤ C.w
    barrier : C.e+C.d*C.γ-(C.w-Sour.spanV P.B*C.c)*C.γ<0
    aff : 0≤a
    birth : 0≤b
    funds : coastU P.B n * a ≤ C.c
    hazard : coastU P.B n * b ≤ C.e
    force : chi_f P.order*k < C.γ
    deg : 3≤P.B
abbrev careRate (C:Occlus P) : ℝ:= C.uΓ+C.η+C.η + discount P.B

-- diagonal syntax, not an auxiliary family with derivative match a.e.! Useful as well
-- for recharging only Sublist with disjoint supports in sector. The program `V` can
-- remember base Reg or an equivalent `E0` representative. The crossing has to buy it on
-- the previous Force and parent pages with exactly these new Key slots.
variable {o:I→Seat n} {s:ℕ} {C:Occlus P} {k:ℝ}
variable (T: Mentor C s a b k) (V : I→Key I→ Bag n) (p : ∀ i z,z∈hill I→ Barrage P q ({o i}:Support (More n)) h (V i z) (careRate C) a b)
    (v : 1 ≤ h)(Z : ∀ i (X:Aura n), Hush o X.val (fun z=> V i z X) ∧ ∀ U:Orbit n,River (fun z=> V i z X U))
    (F : Key I→ ForceBudget n) (e : ∀ z∈hill I, SanB (F z) (giftK P C.uΓ) P h (fun _=>k) ∧ FlagWidth P (F z) (cipherK q))
    (f : ∀ i: Force n,Hush o i.val.1.val.2 (fun z=> F z i) ∧ ∀ U:Orbit n,River (fun z=> F z i U))
    (x : Force_M P.B o s)
abbrev lug (V : I→ Key I→ Bag n)(z:Key I) : Bag n:= agenda (fun i=> V i z) z

include Z
lemma evolve (i : Aura n)(u : Orbit n) : Flood 1 (fun z=>lug V z i u) := by
 unfold lug agenda; simp_rw [Finset.sum_apply, Pi.smul_apply]
 refine (Flood.oneStep _).mpr ⟨(tip_bank univ (fun j z=> z j • V j z i u) (fun j _=> κscale (Flood.coord j|>.riv) ((Z j i).2 u))).1,?_⟩ -- tune FF
 change ∑ j:I, (0:ℂ) • _=_; simp only [zero_smul,Finset.sum_const_zero]

include p
lemma invested (i : Aura n) : Hush o i.val (fun z=> lug V z i) := by
 have hv(j)(t:o j ∉ i.val)(z:Key I)(u:z∈hill I):V j z i=0:=by
    obtain ⟨_,_,_,w,_⟩:=(p j z u).price; exact (w i (by simpa using t)).1
 intro z vz w vw u; change lug _ _ _=lug _ _ _; unfold lug agenda; simp_rw [Finset.sum_apply, Pi.smul_apply]; refine sum_congr rfl (fun j _=>?_) -- Pi.smul Apply may not progress? tune
 by_cases g:o j∈i.val
 · exact congrArg₂ (fun (c:ℂ) (V:Firing n)=>c • V) (u j g) ((Z j i).1 _ vz _ vw u)
 rw [hv j g z vz,hv j g w vw, smul_zero,smul_zero]

include T v e f x
lemma fundingMint : ∃ (K : Key I→ Rinse (Seat n) (Copy n)) (Y W : Key I → Aura n→ℝ)(J:Key I → blazeK n), Furrow o C q F h K Y W J (lug V) := by
 let u:= zero_le_one.trans v
 choose! Y W B Q using fun (z : Key I)(hz:z∈hill I)=> tapeBuy x _ (C.uΓ+C.η+C.η) (fun i=> p i z hz) T.aff T.birth z hz -- tune
 let A(z)(w:z∈hill I):= bannerOil (Y z) (W z) (lug V z) (B z w)
 let K(z:Key I): Rinse (Seat n) (Copy n):= if w:z∈hill I then (A z w).payX else 0
 have ht(z:Key I)(v:z∈hill I): K z=(A z v).payX:= dif_pos v
 choose! J s' p' using fun (z : Key I)(w:z∈hill I)=> settlement (e z w).1 u (e z w).2 C.w
 refine ⟨K,Y,W,J,s',?_,?_,?_,f,fun i=>⟨invested V p Z i,evolve _ Z i⟩,?_,?_⟩
 · intro z w; rw [ht z w]; exact (A z w).buys T.deg u
 · intro z w; rw [ht z w]; exact bias_pic P _ _ (A z w) -- check order
 · intro z w X; rw [ht z w]; exact birthIncome _ _ _ (B z w) (A z w) X u T.deg
 · intro z v i; rw [ht z v]; exact programTurf _ _ _ (B z v) _ _ i
 intro z hz; have hv:0 ≤ W z:=fun X=> by obtain ⟨k,h,-⟩:=(B z hz X).forms; exact h.price
 apply Ledger.fromDelay C _ (A z hz).weight hv (fun X D p=> (s' z hz X D p).merit.wage u) T.shelf (fun i=>⟨((Q z hz i).1.trans T.funds),((Q z hz i).2.trans T.hazard)⟩) T.stiff T.one T.hard ((mul_nonneg (coastSafe P.B s) T.aff).trans T.funds) T.barrier
 rw [T.one]; exact fun i=> (p' z hz i).trans_lt T.force
end YM.CF.Sour
#print axioms YM.CF.Sour.fundingMint
