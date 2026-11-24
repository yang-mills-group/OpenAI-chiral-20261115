import YM.CF.DPress.FD.Geo.Gist
import YM.CF.DPress.FD.Tile.Arch
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Finset Cash Bifold Deck Hue Ramp
open scoped Topology BigOperators ENNReal NNReal Classical
variable {n:Side} {q l m F:ℕ} {i j x y:Site n}
namespace Geo
variable (D W:Support n)(c e:ColorT q n)(u v:NormW n)
local notation "L"=> Site n
abbrev leafL(n:Side)(m:ℕ):= Ramp (Site n) m
-- raw boxes; max contest.
def tom(D:Support n)(u:NormW n)(m:ℕ)(x i:L):= if i∈ D then min m (u i-separation i x) else 0
def kid(D:Support n)(c:ColorT q n)(u:NormW n)(m:ℕ)(x i:L):= univ.sup fun j:L=> if c i<c j then tom D u m x j else 0
def hits(D:Support n)(c:ColorT q n)(u:NormW n)(m:ℕ)(x:L) : leafL n m:=fun i=> ⟨min m (min (2*tom D u m x i) (2*(m-kid D c u m x i))), Nat.lt_succ_of_le (min_le_left ..)⟩
local notation "C"=> hits D c u m
local notation "X"=> tom D u m
local notation "Y"=> kid D c u m
lemma kids(t:c i<c j): X x j≤Y x i:= by unfold kid; exact (show (if c i<c j then X x j else 0)=_ from (if_pos t)).symm.trans_le (le_sup (f:=fun j=> if c i<c j then X x j else 0) (mem_univ j)) -- syntax mem_univ
lemma cape {w:ℕ}: Y x i≤w ↔∀ j:L,c i<c j→X x j≤w:=by
 refine ⟨fun p j t=>(kids D c u t).trans p,fun p=>?_⟩; unfold kid; refine Finset.sup_le ?_; intro j _; split; exact p _ (by assumption); exact Nat.zero_le _
lemma tom_size : X x i ≤ m:= by unfold tom; split; exact min_le_left ..; omega
lemma tom_v : 0<X x i↔i∈ D∧0<m∧ separation i x < u i:= by unfold tom; split <;> rename_i h <;> simp [h]
lemma C_pos : 0< (C x i).val↔ 0<m∧0<X x i∧Y x i<m:=by unfold hits; dsimp only; omega
lemma C_si {r:ℕ}: r≤ (C x i).val ↔ r ≤ m ∧ r ≤ 2*X x i ∧ r ≤ 2*(m-Y x i):=by unfold hits; dsimp only; omega
lemma cap (t:∀ j∈ D,Score l (u j))(p:0<X x i):separation i x<4*l:=by obtain ⟨x,v,q⟩:= (tom_v D u).1 p; exact q.trans_le (t i x).2
lemma gem (h:i∈supportT (C x)): 0< X x i:= by have he:x=x:=rfl; have hp: (C x i).val ≠ 0 :=(by intro t; exact ((mem_h ..).1 h) (Fin.ext t)); exact ((C_pos D c u).1 (Nat.pos_of_ne_zero hp)).2.1
lemma glowD (x:L): supportT (C x)⊆D:= fun _ h=> ((tom_v D u).1 (gem D c u h)).1
lemma born (p:0<m)(hl:m≤ l)(h:∀ i∈ D,Score l (u i))(t:∃ j∈ D, separation x j ≤ l) : Live (C x):=by
 let A:=univ.filter fun i:L=> m≤2*X x i
 obtain ⟨j,b,k⟩:=t; have hv: u j≥2*l:= (h j b).1; have hx:separation j x ≤ l:= (separation_comm ..).trans_le k; have he:(X x j)=m:=by unfold tom; rw [if_pos b]; omega
 have hw:j∈A:= mem_filter.mpr ⟨mem_univ _,(show m≤ 2*X x j from by rw [he]; omega)⟩
 obtain ⟨i,x',hi⟩:= Finset.exists_max_image A c ⟨j,hw⟩; refine ⟨i,Fin.ext (show _ = m from (le_antisymm (Nat.le_of_lt_succ (C x i).isLt) ?_))⟩ -- tune
 apply (C_si D c u).2; refine ⟨le_rfl,(mem_filter.mp x').2,?_⟩; have hp:Y x i ≤ m/2:=by
    apply (cape D c u).2; intro j t; by_contra! f; exact t.not_ge (hi j (mem_filter.mpr ⟨mem_univ _,show m ≤ 2*X x j from (by omega)⟩))
 omega
lemma diff_x:Y x i ≤ Y y i+separation x y:=by
 apply (cape D c u).2; intro j v; apply le_trans _ (Nat.add_le_add_right (kids D c u v) _); unfold tom; split; · have hz:= separation_triangle j x y; omega
 omega
lemma cost_m : Ramp.d (C x) (C y) ≤ 2*separation x y:=by
 have h(x y:L)(i:L):(C x i).val ≤ (C y i).val +2*separation x y:=by
    have ht:X x i≤X y i+separation x y:=by unfold tom; split; · have hz:= separation_triangle i x y; omega
                                           omega
    have hu:Y y i≤Y x i+separation x y:= by rw [separation_comm]; exact diff_x D c u; -- tune
    unfold hits; dsimp only; omega
 refine (Ramp.dusk ..).2 fun j=>?_ ; have hz:= h x y j; have ht:=h y x j; rw [separation_comm y x] at ht; unfold DistU; omega
-- visibility local (including reassigned data, orientations later)
variable {V U: NormW n}
abbrev UBook(l:ℕ)(D:Support n)(u:NormW n):=∀ i∈ D, Score l (u i)
lemma cutT (p: UBook l D u)(t:i∉cell n x (5*l)): tom D u m x i=0:=by
 by_contra h; have he:= cap D u p (Nat.pos_of_ne_zero h); apply t; rw [cellP,separation_comm]; omega
lemma tom_j (t:UBook l D u)(h:UBook l W v)(g:sees D W (cell n x (5*l)))(p:Set.EqOn u v (cell n x (5*l))):X x i=tom W v m x i:=by
 by_cases hp:i∈cell n x (5*l); unfold tom; simp_rw [p hp,g i hp];
 rw [cutT D u t hp,cutT W v h hp]
lemma kid_j (p:c i=e i)(t:UBook l D u)(h:UBook l W v)(g:sees D W (cell n x (5*l)))(k:Set.EqOn u v (cell n x (5*l)))(V:Set.EqOn c e (cell n x (5*l))) : Y x i=kid W e v m x i:=by
 unfold kid; refine Finset.sup_congr rfl fun j _=> ?_; rw [p]; by_cases w:j∈cell n x (5*l); rw [V w,tom_j D W u v t h g k]
 rw [cutT D u t w,cutT W v h w,ite_self,ite_self]
lemma hits_j (t:UBook l D u)(h:UBook l W v)(g:sees D W (cell n x (5*l)))(k:Set.EqOn u v (cell n x (5*l)))(V:Set.EqOn c e (cell n x (5*l))) : C x=hits W e v m x:=by
 funext i; apply Fin.ext; unfold hits; dsimp only; by_cases p:i∈cell n x (5*l); rw [kid_j D W c e u v (V p) t h g k V,tom_j D W u v t h g k]
 rw [cutT D u t p,cutT W v h p]; omega
lemma hits_r(s:Signed)(x i j:Site n)(p:c=e ∘ aura s x)(t:∀ i,i∈ D ↔ aura s x i∈W)(h:u=v ∘ aura s x):C j i=hits W e v m (aura s x j) (aura s x i):=by
 let S:= aura s x; let X':=tom W v m; have he(i):u i=v (S i):= congrFun h i; have hv(i):c i=e (S i):= congrFun p i; have hx(i):X j i=X' (S j) (S i):=by unfold tom X'; simp only [he,S]; simp only [tom,around,t] -- loops?
 have hw:Y j i=kid W e v m (S j) (S i):=by
    let g(y:L):= if e (S i)<e y then X' (S j) y else 0; let f(y:L):=if c i<c y then X j y else 0; have hh(y:L) :g (S y)=f y:=by simp only [f,g,hv,hx];
    change univ.sup f=univ.sup g; rw [show f=g ∘ S from funext (fun i=>(hh i).symm), ← sup_image]; simp
 apply Fin.ext; unfold hits; dsimp only; rw [hw,hx]; -- exact rfl
end Geo
end YM.CF.DPress.FD
