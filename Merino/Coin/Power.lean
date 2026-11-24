import YM.SU5.Exchange.Seed.Pension

set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Coin
open Function Finset Lattice Cube RG Scree Skye Fock
open scoped Topology Matrix MatrixOrder Classical Matrix.Norms.L2Operator
open Py Roots QuadClock Oise Mew Neon Waxy
open Vow TreasuryFog Dial Paige Vault
open scoped YM.CF.Mew
variable {N B:Side}
variable {I:Type}[Fintype I][LinearOrder I]
local notation "X"=>mid N B

variable {h w:ℝ}{o:I→Site (mid N B)}
 {D:Key I→RegBudget (mid N B)}{K:Key I→ForceBudget (mid N B)}
local notation "σ"=> node∘o

def cream (p:BudgetPoint):BudgetPoint:={p with supportExponent:=1/2,exponent_pos:=by norm_num}


open Rive

section
variable {p:BudgetPoint}{n:Side}
private lemma sugared {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U]{x:Seat n}{F:tangD n→U}{c:ℝ}:
 Signs p x F c ↔ Signs (cream p) x F c:=
   ⟨fun ⟨a,b,c⟩=>⟨a,b,c⟩,fun ⟨a,b,c⟩=>⟨a,b,c⟩⟩
lemma lessE {x:Scree.Hub n}{F:InkD n}{z:ℝ}:PressB p x F h z ↔ PressB (cream p) x F h z:=
 ⟨fun ⟨a,b,c,d,e,g,u,v⟩=> ⟨a,b,c,d,e,g,fun i t x=> sugared.mp (u i t x),v⟩,fun ⟨a,b,c,d,e,g,u,v⟩=> ⟨a,b,c,d,e,g,fun i t x=> sugared.mpr (u i t x),v⟩⟩
lemma lessF {x:Force n}{F:Copy n}{z:ℝ}:ForceB p x F h z ↔ ForceB (cream p) x F h z:=by
 constructor <;> rintro ⟨a,b,c,d,e,g,w,j,u,v⟩
 · exact ⟨a,b,c,d,e,g,w,j,fun i t x=> sugared.mp (u i t x),v⟩
 exact ⟨a,b,c,d,e,g,w,j,fun i t x=> sugared.mpr (u i t x),v⟩
end

abbrev film(p:BudgetPoint){n:Side}: Scree.Hub n→Seat n→ℝ:=filmK (cream p) ((cream p).supportExponent+1/2)
abbrev sale(p:BudgetPoint){n:Side}: Force n→Seat n→ℝ:=giftK (cream p) ((cream p).supportExponent+1/2)
abbrev reduce (o:I→Site (mid N B))(D:Key I→RegBudget (mid N B)) :=awake (node∘o) D (νTip D)
abbrev reduceK(o:I→Site (mid N B))(K:Key I→ForceBudget (mid N B)):=bustle (node∘o) K

variable (t:Notice o D K)
include t
lemma displayE (x:Scree.Hub X): Hush (σ) x.val.2 (fun z=> D z x) ∧ ∀ i,River (fun z=> D z x i):=
 ⟨quiet_hush (t.col _),fun y=>river_all _ (t.varE x y)⟩
lemma displayK (x:Force X): Hush (σ) x.val.1.val.2 (fun z=> K z x) ∧ ∀ i,River (fun z=>K z x i):=
 ⟨quiet_hush (t.joinF _),fun y=>river_all _ (t.varF x y)⟩

lemma point_b (i:Finset I):
 (∀ x:Force X,νΦK K i x≠0→ poke_F (node∘o) x.val.1.val.2 i)∧
 ∀ x:Scree.Hub X,νΦX D i x ≠ 0 → poke_F (node∘o) x.val.2 i:=by
 constructor

 · intro x p j v; by_contra hi; apply p; funext y
   have h:=displayK t x
   exact husht_B _ _ _ (show Hush (σ) x.val.1.val.2 (fun z=>K z x y) from fun u v w f g=> congrFun (h.1 u v w f g) y)
     (h.2 y) (Mew.Cue I i) j hi (by simpa [Mew.Cue] using v)
 intro x p j v; by_contra hi; apply p; funext y
 have h:=displayE t x
 exact husht_B _ _ _ (show Hush (σ) x.val.2 (fun z=>D z x y) from fun u v w f g=> congrFun (h.1 u v w f g) y)
    (h.2 y) (Mew.Cue I i) j hi (by simpa [Mew.Cue] using v)

lemma news :Notice o (reduce o D) (reduceK o K):=by
 have e(i:I):νTip (reduce o D) i=νTip D i:=value_E (node∘o) (νTip D) D i
 have f(i:I):emberTip (reduceK o K) i=νΦK K {i}:= value_F (node∘o) K i
 have a(j:I)(x:Scree.Hub X)(v: νTip D j x≠0): node (o j)∈ x.val.2:=
    (point_b t {j}).2 _ (fun h=> v ((funext fun y=>cue_1 _ j) |>.symm |>.trans h)) j (mem_singleton_self j)
 exact ⟨cash0 (node∘o) (νTip D) D K, quietE _ (νTip D) D (displayE t) a,eReady (node∘o) (νTip D) D, quietF _ K (displayK t),fReady (node∘o) K, fun i w=> by rw [e,f];exact ⟨crest_E ..,crest_K ..⟩⟩



variable {P:BudgetPoint}{q:ℝ}
variable (h0:0<h)(hx:P.supportExponent=1)
variable (v:∀ z∈hill I,IncX primeU (D z) P h q ∧ Dark primeU (K z) P h w)
include v hx h0

lemma normE(i:Finset I): ForgeB (νΦX D i) (film P) (cream P) h (fun _=>q):=by
 refine onset_t D h0 _ (fun i j=>by unfold film filmK; split; exact (Real.exp_pos _).le;exact le_rfl) (fun i=> ⟨i.val.1,by unfold film filmK;rw [if_pos rfl];exact Real.exp_pos _⟩)
   _ ?_ (fun i=>(displayE t i).2) (Mew.Cue I i)
 intro z p
 obtain ⟨a,f,g⟩:=(v z p).1.weight
 refine ⟨a,fun i=>lessE.mp (f i),fun i=>le_trans (sum_le_sum (fun j _=>?_)) (g i)⟩
 change film P j i * a j ≤ _
 unfold film
 rw [show (cream P).supportExponent+(1:ℝ)/2=P.supportExponent from by unfold cream;rw [hx];norm_num] -- may need unfold film
 unfold filmK; split; exact le_rfl; rw [zero_mul]


lemma normF(i:Finset I): SanB (νΦK K i) (sale P) (cream P) h (fun _=>w):=by
 refine insight_t K h0 _ (fun i j=>by unfold sale giftK; split; exact (Real.exp_pos _).le;exact le_rfl) (fun i=> ⟨i.val.1.val.1,by unfold sale giftK;rw [if_pos i.val.1.property];exact Real.exp_pos _⟩)
   _ ?_ (fun i=>(displayK t i).2) (Mew.Cue I i)
 intro z p
 obtain ⟨a,f,g⟩:=(v z p).2.weight
 refine ⟨a,fun i=>lessF.mp (f i),fun i=>le_trans (sum_le_sum (fun j _=>?_)) (g i)⟩
 change sale P j i * a j ≤ _
 unfold sale
 rw [show (cream P).supportExponent+(1:ℝ)/2=P.supportExponent from by unfold cream;rw [hx];norm_num]
 unfold giftK; split; exact le_rfl; rw [zero_mul]

lemma tender (i:I) : FixedF (cream P) h w (νΦK K {i}):=by
 obtain ⟨k,z,r⟩:= (normF t h0 hx v {i}).bit
 let a(y:Force X):= if (σ) i∈ y.val.1.val.2 then k y else 0
 refine ⟨a,fun x=>?_,le_trans ?_ (r ((σ) i))⟩
 · unfold a; split; exact z _; next g=>
       have hz: νΦK K {i} x = 0:=by contrapose! g;exact (point_b t {i}).1 x g i (mem_singleton_self _)
       rw [hz]; exact Vale.rinsed ..
 refine sum_le_sum fun x _=>?_; unfold a sale giftK; split
 next e =>
   refine le_mul_of_one_le_left (gradeQ _ _ (z x) h0.le) (Real.one_le_exp ?_);have := (cream P).exponent_pos;positivity
 next e=>rw [zero_mul]

variable {L V:ℝ}{m f:ℕ}{Y:I→Neon.ArcΦ}
variable
  (b:Force_M P.B (node∘o) m)
  (d:∀i, Axon f (o i) P (νTip D i) h w (Y i))

include b d


lemma feasting {W:ℝ}(p:1≤L)(n:Nice_B P.B m L (1/8))(r:8≤P.B)(s:0≤q)(g:0≤w)
  (u:wish_E P.B q≤V)(z:wish_E P.B w≤V)
  (c:L*w≤W):PanoramaBill (cream P) h L V W (reduce o D) (reduceK o K):=by
 intro y j
 let F:=manySet (node∘o)
 have ha(i)(hi:i∈F):= (mem_filter.mp hi).2
 have hb(i:Finset I): ‖pine i y‖ ≤ L^i.card:=by
     unfold Mew.pine
     rw [norm_prod];exact (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=> j i)).trans_eq (prod_const ..)
 change Pavilion (cream P) h V _ (_ + ∑i∈ F, _) (bustle (node∘o) K y)
 unfold bustle; rw [sumOpen]
 have hi(i:I):pine {i} y = y i:= by rw [pine,prod_singleton]
 simp_rw [hi]
 refine ⟨_,_,_,_,rfl,rfl,?_,?_,?_,?_⟩
 · obtain ⟨G,k,e⟩:=(sum_FixedE (νTip D) (fun _=>w) y (fun i=> Axon_fixedE (d i) h0.le)).pay
   refine ⟨G,fun i=>lessE.mp (k i),e.trans ?_⟩
   refine le_trans (sum_le_sum (g:=fun _=>W)
        (fun i _=> (mul_le_mul_of_nonneg_right (j i) g).trans c)) (by rw [sum_const,nsmul_eq_mul,card_univ,mul_comm])


 · refine (sum_FixedF (fun i=>νΦK K {i}) (fun _=>w) y (tender t h0 hx v)).more ?_
   refine le_trans (sum_le_sum (g:=fun _=>W)
        (fun i _=> (mul_le_mul_of_nonneg_right (j i) g).trans c)) (by rw [sum_const,nsmul_eq_mul,card_univ,mul_comm])
 · obtain ⟨⟨A,B',C⟩,g'⟩:=streak_E F (νΦX D) (node∘o) h0 L q (fun i _=> (point_b t i).2) (fun i _=>normE t h0 hx v i)
          (fun i=>pine i y) (fun i _=>hb i) p r s b.1 b.2 n (fun i w=> (ha i w).2) (fun i w=> (ha i w).1)
   exact ⟨⟨A,B',fun i=>(C i).trans u⟩,g'⟩
 obtain ⟨⟨M,H,T⟩,Z⟩:=sprint_K F (νΦK K) (node∘o) h0 L w (fun i _=> (point_b t i).1) (fun i _=>normF t h0 hx v i)
          (fun i=>pine i y) (fun i _=>hb i) p r g b.1 b.2 n (fun i w=> (ha i w).2) (fun i w=> (ha i w).1)
 exact ⟨⟨M,H,fun i=>(T i).trans z⟩,Z⟩
end YM.CF.Merino.Coin
